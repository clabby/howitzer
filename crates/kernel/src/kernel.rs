//! This module contains the [Kernel] struct and its associated methods.

use crate::{gz::compress_bytes, types::Proof};
use anyhow::{anyhow, Result};
use howitzer_fpvm::{state::state_hash, InstrumentedState};
use kona_preimage::{HintRouter, PreimageFetcher};
use std::{
    fs::File,
    io::{BufWriter, Write},
    process::Child,
    time::Instant,
};
use tokio::{runtime::Runtime, task::JoinHandle};

/// The [Kernel] struct contains the configuration for a Howitzer kernel as well as
/// the [PreimageOracle] and [InstrumentedState] instances that form it.
#[allow(dead_code)]
pub struct Kernel<O, E, P>
where
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    /// The instrumented state that the kernel will run.
    ins_state: InstrumentedState<O, E, P>,
    /// The server's process coupled with the preimage server's IO. We hold on to these so that
    /// they are not dropped until the kernel is dropped, preventing a broken pipe before the
    /// kernel is dropped. The other side of the bidirectional channel is owned by the
    /// [InstrumentedState], which is also dropped when the kernel is dropped.
    server_proc: Option<Child>,
    /// The path to the input JSON state.
    input: String,
    /// The path to the output JSON state.
    output: Option<String>,
    /// The step to generate an output proof at.
    proof_at: Option<String>,
    /// Format for proof data output file names. Proof data is written to stdout
    /// if this is not specified.
    proof_format: Option<String>,
    /// The step pattern to generate state snapshots at.
    snapshot_at: Option<String>,
    /// Format for snapshot data output file names.
    snapshot_format: Option<String>,
    /// The instruction step to stop running at.
    stop_at: Option<String>,
    /// The pattern to print information at.
    info_at: Option<String>,
}

impl<O, E, P> Kernel<O, E, P>
where
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        ins_state: InstrumentedState<O, E, P>,
        server_proc: Option<Child>,
        input: String,
        output: Option<String>,
        proof_at: Option<String>,
        proof_format: Option<String>,
        snapshot_at: Option<String>,
        snapshot_format: Option<String>,
        stop_at: Option<String>,
        info_at: Option<String>,
    ) -> Self {
        Self {
            ins_state,
            server_proc,
            input,
            output,
            proof_at,
            proof_format,
            snapshot_at,
            snapshot_format,
            stop_at,
            info_at,
        }
    }

    pub fn run(mut self) -> Result<()> {
        let rt = Runtime::new().unwrap();

        rt.block_on(async move {
            let stop_at = create_matcher(self.stop_at.as_ref())?;
            let proof_at = create_matcher(self.proof_at.as_ref())?;
            let snapshot_at = create_matcher(self.snapshot_at.as_ref())?;

            let proof_fmt = self.proof_format.unwrap_or("%d.json.gz".to_string());
            let snapshot_fmt = self.snapshot_format.unwrap_or("%d.json.gz".to_string());

            let (info_at, start_step, start) = (
                create_matcher(self.info_at.as_ref())?,
                self.ins_state.state.step,
                Instant::now(),
            );

            let mut io_tasks: Vec<JoinHandle<Result<()>>> = Vec::default();

            while !self.ins_state.state.exited {
                let step = self.ins_state.state.step;

                if info_at.matches(step) {
                    let delta = start.elapsed();
                    tracing::info!(
                        target: "howitzer::kernel",
                        "[ELAPSED: {}.{:03}s] step: {}, pc: {}, instruction: {:08x}, ips: {}, pages: {}, mem: {}",
                        delta.as_secs(),
                        delta.subsec_millis(),
                        step,
                        self.ins_state.state.pc,
                        self.ins_state.state.memory.get_memory_word(self.ins_state.state.pc)?,
                        (step - start_step) as f64 / delta.as_secs_f64(),
                        self.ins_state.state.memory.page_count(),
                        self.ins_state.state.memory.usage(),
                    );
                }

                if stop_at.matches(step) {
                    tracing::info!(target: "howitzer::kernel", "Stopping at step {}", step);
                    break;
                }

                if snapshot_at.matches(step) {
                    tracing::info!(target: "howitzer::kernel", "Writing snapshot at step {}", step);
                    let ser_state = serde_json::to_vec(&self.ins_state.state).unwrap();
                    let snap_path = snapshot_fmt.replace("%d", &format!("{}", step));
                    io_tasks.push(tokio::task::spawn(async move {
                        let gz_state = compress_bytes(&ser_state)?;
                        let mut writer = BufWriter::new(File::create(snap_path)?);
                        writer.write_all(&gz_state)?;
                        tracing::info!(target: "howitzer::kernel", "Wrote snapshot at step {} successfully.", step);

                        Ok(())
                    }));
                }

                if proof_at.matches(step) {
                    tracing::info!(target: "howitzer::kernel", "Writing proof at step {}", step);

                    let prestate_hash = state_hash(self.ins_state.state.encode_witness()?);
                    let step_witness = self
                        .ins_state
                        .step(true).await?
                        .ok_or(anyhow!("No step witness"))?;
                    let poststate_hash = state_hash(self.ins_state.state.encode_witness()?);

                    let proof_path = proof_fmt.replace("%d", &format!("{}", step));
                    io_tasks.push(tokio::task::spawn(async move {
                        let proof = {
                            let preimage_input = step_witness.encode_preimage_oracle_input();
                            Proof {
                                step,
                                pre: prestate_hash,
                                post: poststate_hash,
                                state_data: step_witness.state,
                                step_input: step_witness.encode_step_input().to_vec(),
                                proof_data: step_witness.mem_proof,
                                oracle_input: preimage_input.map(|k| k.to_vec()),
                                oracle_key: step_witness.preimage_key.map(|k| k.to_vec()),
                                oracle_value: step_witness.preimage_value,
                                oracle_offset: step_witness.preimage_offset,
                            }
                        };

                        let ser_proof = &serde_json::to_string(&proof)?;
                        let mut writer = BufWriter::new(File::create(proof_path)?);
                        writer.write_all(ser_proof.as_bytes())?;

                        tracing::info!(target: "howitzer::kernel", "Wrote proof at step {} successfully.", step);

                        Ok(())
                    }));
                } else {
                    self.ins_state.step(false).await?;
                }

                // Periodically check if the preimage server process has exited. If it has, then
                // we should exit as well with a failure.
                // TODO: This may be problematic.
                if step % 10_000_000 == 0 {
                    if let Some(ref mut proc) = self.server_proc {
                        match proc.try_wait() {
                            Ok(Some(status)) => {
                                anyhow::bail!("Preimage server exited with status: {}", status);
                            }
                            Ok(None) => { /* noop - keep it rollin', preimage server is still listening */
                            }
                            Err(e) => {
                                anyhow::bail!("Failed to wait for preimage server: {}", e)
                            }
                        }
                    }
                }
            }

            // Output the final state
            if let Some(output) = &self.output {
                if !output.is_empty() {
                    tracing::info!(target: "howitzer::kernel", "Writing final state to {}", output);
                    let mut writer = BufWriter::new(File::create(output)?);

                    let ser_state = &serde_json::to_vec(&self.ins_state.state)?;
                    let gz_state = compress_bytes(ser_state)?;

                    writer.write_all(&gz_state)?;
                }
            } else {
                println!("{:?}", &self.ins_state.state);
            }

            tracing::info!(target: "howitzer::kernel", "Kernel exiting...");

            // Wait for all of the i/o tasks to finish.
            for task in io_tasks {
                task.await??;
            }

            // File descriptors are closed when the kernel struct is dropped, since it owns all open IO.
            Ok(())
        })
    }
}

enum Matcher {
    Never,
    Always,
    Equal(u64),
    MultipleOf(u64),
}

impl Matcher {
    #[inline(always)]
    fn matches(&self, value: u64) -> bool {
        match self {
            Matcher::Never => false,
            Matcher::Always => true,
            Matcher::Equal(step) => value == *step,
            Matcher::MultipleOf(steps) => value % steps == 0,
        }
    }
}

fn create_matcher(pattern: Option<&String>) -> Result<Matcher> {
    match pattern {
        None => Ok(Matcher::Never),
        Some(pattern) => match pattern.as_str() {
            "never" => Ok(Matcher::Never),
            "always" => Ok(Matcher::Always),
            _ if pattern.starts_with('=') => {
                // Extract the number from the pattern
                if let Ok(step) = pattern[1..].parse::<u64>() {
                    Ok(Matcher::Equal(step))
                } else {
                    anyhow::bail!("Invalid pattern: {}", pattern)
                }
            }
            _ if pattern.starts_with('%') => {
                // Extract the number from the pattern
                if let Ok(steps) = pattern[1..].parse::<u64>() {
                    Ok(Matcher::MultipleOf(steps))
                } else {
                    anyhow::bail!("Invalid pattern: {}", pattern)
                }
            }
            _ => {
                anyhow::bail!("Invalid pattern: {}", pattern)
            }
        },
    }
}

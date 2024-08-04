//! This module contains the [Kernel] struct and its associated methods.

use crate::{gz::compress_bytes, types::Proof};
use anyhow::Result;
use howitzer_fpvm::{
    memory::{Address, Memory},
    mips::HowitzerVM,
    state::{state_hash, StepWitness},
};
use kona_preimage::{HintRouter, PreimageFetcher};
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{BufWriter, Write},
    process::Child,
    time::Instant,
};

/// The [Kernel] struct contains the configuration for a Howitzer kernel as well as
/// the [HintRouter] + [PreimageFetcher] and [HowitzerVM] instances that form it.
pub struct Kernel<M, P>
where
    M: Memory,
    P: HintRouter + PreimageFetcher,
{
    /// The VM that the kernel will run.
    pub(crate) vm: HowitzerVM<M, P>,
    /// The server's process coupled with the preimage server's IO. We hold on to these so that
    /// they are not dropped until the kernel is dropped, preventing a broken pipe before the
    /// kernel is dropped. The other side of the bidirectional channel is owned by the
    /// [HowitzerVM], which is also dropped when the kernel is dropped.
    pub(crate) server_proc: Option<Child>,
    /// The path to the output JSON state.
    pub(crate) output: Option<String>,
    /// The step to generate an output proof at.
    pub(crate) proof_at: Option<String>,
    /// Format for proof data output file names. Proof data is written to stdout
    /// if this is not specified.
    pub(crate) proof_format: Option<String>,
    /// The step pattern to generate state snapshots at.
    pub(crate) snapshot_at: Option<String>,
    /// Format for snapshot data output file names.
    pub(crate) snapshot_format: Option<String>,
    /// The instruction step to stop running at.
    pub(crate) stop_at: Option<String>,
    /// The pattern to print information at.
    pub(crate) info_at: Option<String>,
}

impl<M, P> Kernel<M, P>
where
    M: Memory + Serialize + 'static,
    <M as Memory>::Proof: Serialize,
    for<'de> M: Deserialize<'de>,
    for<'de> <M as Memory>::Proof: Deserialize<'de>,
    P: HintRouter + PreimageFetcher,
{
    pub async fn run(mut self) -> Result<()> {
        let stop_at = create_matcher(self.stop_at.as_ref())?;
        let proof_at = create_matcher(self.proof_at.as_ref())?;
        let snapshot_at = create_matcher(self.snapshot_at.as_ref())?;

        let proof_fmt = self.proof_format.unwrap_or("proof-%d.json.gz".to_string());
        let snapshot_fmt = self.snapshot_format.unwrap_or("snapshot-%d.json.gz".to_string());

        let (info_at, start_step, start) =
            (create_matcher(self.info_at.as_ref())?, self.vm.state.step, Instant::now());

        while !self.vm.state.exited {
            let step = self.vm.state.step;

            if info_at.matches(step) {
                let delta = start.elapsed();
                tracing::info!(
                    target: "howitzer::kernel",
                    "[ELAPSED: {}.{:03}s] step: {}, pc: {}, instruction: {:08x}, ips: {}, pages: {}, mem: {}",
                    delta.as_secs(),
                    delta.subsec_millis(),
                    step,
                    self.vm.state.pc,
                    self.vm.state.memory.get_word(self.vm.state.pc)?,
                    (step - start_step) as f64 / delta.as_secs_f64(),
                    self.vm.state.memory.page_count(),
                    self.vm.state.memory.usage(),
                );
            }

            if stop_at.matches(step) {
                tracing::info!(target: "howitzer::kernel", "Stopping at step {}", step);
                break;
            }

            if snapshot_at.matches(step) {
                tracing::info!(target: "howitzer::kernel", "Writing snapshot at step {}", step);
                let ser_state = serde_json::to_vec(&self.vm.state).unwrap();
                let snap_path = snapshot_fmt.replace("%d", &format!("{}", step));
                let gz_state = compress_bytes(&ser_state)?;
                let mut writer = BufWriter::new(File::create(snap_path)?);
                writer.write_all(&gz_state)?;
                tracing::info!(target: "howitzer::kernel", "Wrote snapshot at step {} successfully.", step);
            }

            if proof_at.matches(step) {
                tracing::info!(target: "howitzer::kernel", "Writing proof at step {}", step);

                // Formulate the state witness as well as the instruction proof prior to performing
                // the state transition.
                let prestate_witness = self.vm.state.encode_witness()?;
                let mut step_witness: StepWitness<M> = {
                    // Generate a merkle proof for the page containing the current instruction.
                    let instruction_proof =
                        self.vm.state.memory.proof(self.vm.state.pc as Address)?;

                    // Allocate the proof vector and push the instruction proof.
                    let mut proof = Vec::with_capacity(2);
                    proof.push(instruction_proof);

                    StepWitness { state: prestate_witness, proof, ..Default::default() }
                };

                let prestate_hash = state_hash(prestate_witness);
                self.vm.step(true).await?;
                let poststate_hash = state_hash(self.vm.state.encode_witness()?);

                // Update the step_witness with the memory access proof and preimage data, if there
                // was a preimage read within the state transition.
                if let Some(mem_proof) = self.vm.proof_meta.mem_proof.take() {
                    step_witness.proof.push(mem_proof);
                }

                if self.vm.proof_meta.last_preimage_offset.is_some() {
                    step_witness.preimage_key = Some(self.vm.proof_meta.last_preimage_key);
                    step_witness.preimage_value = Some(self.vm.proof_meta.last_preimage.clone());
                    step_witness.preimage_offset = self.vm.proof_meta.last_preimage_offset;
                }

                let proof_path = proof_fmt.replace("%d", &format!("{}", step));
                let proof = {
                    let preimage_input = step_witness.encode_preimage_oracle_input();
                    Proof::<M> {
                        step,
                        pre: prestate_hash,
                        post: poststate_hash,
                        state_data: step_witness.state,
                        step_input: step_witness.encode_step_input().to_vec(),
                        proof_data: step_witness.proof,
                        oracle_input: preimage_input.map(|k| k.to_vec()),
                        oracle_key: step_witness.preimage_key.map(Into::into),
                        oracle_value: step_witness.preimage_value,
                        oracle_offset: step_witness.preimage_offset,
                    }
                };

                let ser_proof = &serde_json::to_string(&proof)?;
                let mut writer = BufWriter::new(File::create(proof_path)?);
                writer.write_all(ser_proof.as_bytes())?;

                tracing::info!(target: "howitzer::kernel", "Wrote proof at step {} successfully.", step);
            } else {
                self.vm.step(false).await?;
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

                let ser_state = &serde_json::to_vec(&self.vm.state)?;
                let gz_state = compress_bytes(ser_state)?;

                writer.write_all(&gz_state)?;
            }
        } else {
            println!("{:?}", &self.vm.state);
        }

        tracing::info!(target: "howitzer::kernel", "Kernel exiting...");

        // File descriptors are closed when the kernel struct is dropped, since it owns all open IO.
        Ok(())
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

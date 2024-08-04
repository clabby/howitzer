//! The [KernelBuilder] struct is a helper for building a [Kernel] struct.

use crate::{gz, utils::bidirectional_pipe, Kernel, ProcessPreimageOracle};
use anyhow::{anyhow, Result};
use howitzer_fpvm::{memory::Memory, mips::HowitzerVM, state::State};
use serde::{Deserialize, Serialize};
use std::{
    fs::{self, File},
    io::{BufReader, Read},
    path::PathBuf,
};

/// The [KernelBuilder] struct is a helper for building a [Kernel] struct.
#[derive(Default, Debug)]
pub struct KernelBuilder {
    /// The full command to run the preimage server
    preimage_server: String,
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

impl KernelBuilder {
    /// Builds the [Kernel] struct from the information contained within the [KernelBuilder].
    pub fn build<M>(self) -> Result<Kernel<M, ProcessPreimageOracle>>
    where
        M: Memory + Serialize + Send + 'static,
        <M as Memory>::Proof: Serialize + Send + 'static,
        for<'de> M: Deserialize<'de>,
        for<'de> <M as Memory>::Proof: Deserialize<'de>,
    {
        // Read the compressed state dump from the input file, decompress it, and deserialize it.
        let f = File::open(&self.input)?;
        let f_sz = f.metadata()?.len();
        let mut reader = BufReader::new(f);
        let mut raw_state = Vec::with_capacity(f_sz as usize);
        reader.read_to_end(&mut raw_state)?;
        let raw_state = fs::read(&self.input)?;
        let state: State<M> = serde_json::from_slice(&gz::decompress_bytes(&raw_state)?)?;

        let hint_channel = bidirectional_pipe()?;
        let preimage_channel = bidirectional_pipe()?;

        let cmd = self.preimage_server.split(' ').map(String::from).collect::<Vec<_>>();
        let (oracle, server_proc) = ProcessPreimageOracle::start(
            PathBuf::from(cmd.first().ok_or(anyhow!("Missing preimage server binary path"))?),
            &cmd[1..],
            hint_channel,
            preimage_channel,
        )?;

        let vm = HowitzerVM::new(state, oracle);

        Ok(Kernel {
            vm,
            server_proc,
            output: self.output,
            proof_at: self.proof_at,
            proof_format: self.proof_format,
            snapshot_at: self.snapshot_at,
            snapshot_format: self.snapshot_format,
            stop_at: self.stop_at,
            info_at: self.info_at,
        })
    }

    pub fn with_preimage_server(mut self, preimage_server: String) -> Self {
        self.preimage_server = preimage_server;
        self
    }

    pub fn with_input(mut self, input: String) -> Self {
        self.input = input;
        self
    }

    pub fn with_output(mut self, output: Option<String>) -> Self {
        self.output = output;
        self
    }

    pub fn with_proof_at(mut self, proof_at: Option<String>) -> Self {
        self.proof_at = proof_at;
        self
    }

    pub fn with_proof_format(mut self, proof_format: Option<String>) -> Self {
        self.proof_format = proof_format;
        self
    }

    pub fn with_snapshot_at(mut self, snapshot_at: Option<String>) -> Self {
        self.snapshot_at = snapshot_at;
        self
    }

    pub fn with_snapshot_format(mut self, snapshot_format: Option<String>) -> Self {
        self.snapshot_format = snapshot_format;
        self
    }

    pub fn with_stop_at(mut self, stop_at: Option<String>) -> Self {
        self.stop_at = stop_at;
        self
    }

    pub fn with_info_at(mut self, info_at: Option<String>) -> Self {
        self.info_at = info_at;
        self
    }
}

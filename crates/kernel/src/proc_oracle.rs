//! This module contains the [ProcessPreimageOracle] struct and its associated methods.

use anyhow::Result;
use async_trait::async_trait;
use command_fds::{CommandFdExt, FdMapping};
use kona_common::FileDescriptor;
use kona_preimage::{
    HintRouter, HintWriter, HintWriterClient, OracleReader, PipeHandle, PreimageFetcher,
    PreimageKey, PreimageOracleClient,
};
use std::{
    io,
    os::fd::{AsFd, AsRawFd},
    path::PathBuf,
    process::{Child, Command},
};

use crate::utils::BidirectionalPipe;

/// The [ProcessPreimageOracle] struct represents a preimage oracle process that communicates with
/// the fault proof VM via a few special file descriptors. This process is responsible for preparing
/// and sending the results of preimage requests to the FPVM process.
pub struct ProcessPreimageOracle {
    /// The preimage oracle client
    pub preimage_client: OracleReader,
    /// The hint writer client
    pub hint_writer_client: HintWriter,
}

impl ProcessPreimageOracle {
    /// Creates a new [ProcessPreimageOracle] from the given [OracleReader] and [HintWriter] and
    /// starts the server process.
    pub fn start(
        cmd: PathBuf,
        args: &[String],
        hint_channel: BidirectionalPipe,
        preimage_channel: BidirectionalPipe,
    ) -> Result<(Self, Option<Child>)> {
        let cmd_str = cmd.display().to_string();
        let child = (!cmd_str.is_empty()).then(|| {
            let mut command = Command::new(cmd);
            let command = {
                tracing::info!(target: "howitzer::preimage::server", "Starting preimage server process: {:?}", args);

                command
                    .args(args)
                    .fd_mappings(vec![
                        FdMapping { parent_fd: io::stdin().as_fd().try_clone_to_owned().unwrap(), child_fd: 0 },
                        FdMapping { parent_fd: io::stdout().as_fd().try_clone_to_owned().unwrap(), child_fd: 1 },
                        FdMapping { parent_fd: io::stderr().as_fd().try_clone_to_owned().unwrap(), child_fd: 2 },
                        FdMapping { parent_fd: hint_channel.host.reader.into(), child_fd: 3 },
                        FdMapping { parent_fd: hint_channel.host.writer.into(), child_fd: 4 },
                        FdMapping { parent_fd: preimage_channel.host.reader.into(), child_fd: 5 },
                        FdMapping { parent_fd: preimage_channel.host.writer.into(), child_fd: 6 },
                    ])?
            };

            command.spawn().map_err(|e| anyhow::anyhow!("Failed to start preimage server process: {}", e))
        });

        let oracle = Self {
            hint_writer_client: HintWriter::new(PipeHandle::new(
                FileDescriptor::Wildcard(hint_channel.client.reader.as_raw_fd() as usize),
                FileDescriptor::Wildcard(hint_channel.client.writer.as_raw_fd() as usize),
            )),
            preimage_client: OracleReader::new(PipeHandle::new(
                FileDescriptor::Wildcard(preimage_channel.client.reader.as_raw_fd() as usize),
                FileDescriptor::Wildcard(preimage_channel.client.writer.as_raw_fd() as usize),
            )),
        };

        // Ensure client IO lives for the lifetime of the process
        std::mem::forget(hint_channel.client);
        std::mem::forget(preimage_channel.client);

        Ok((oracle, child.transpose()?))
    }
}

#[async_trait]
impl HintRouter for ProcessPreimageOracle {
    async fn route_hint(&self, hint: String) -> Result<()> {
        self.hint_writer_client.write(&hint).await
    }
}

#[async_trait]
impl PreimageFetcher for ProcessPreimageOracle {
    async fn get_preimage(&self, key: PreimageKey) -> Result<Vec<u8>> {
        self.preimage_client.get(key).await
    }
}

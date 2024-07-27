//! This module contains the [PreimageServer] struct and its associated methods.

use crate::utils::NativePipeFiles;
use anyhow::Result;
use async_trait::async_trait;
use command_fds::{CommandFdExt, FdMapping};
use kona_preimage::{
    HintRouter, HintWriter, HintWriterClient, OracleReader, PipeHandle, PreimageFetcher,
    PreimageKey, PreimageOracleClient,
};
use std::{
    io,
    os::fd::AsRawFd,
    path::PathBuf,
    process::{Child, Command},
};

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
    /// Creates a new [PreimageServer] from the given [OracleClient] and [HintWriter] and starts
    /// the server process.
    pub fn start(
        cmd: PathBuf,
        args: &[String],
        preimage_pipe: PipeHandle,
        hint_pipe: PipeHandle,
        pipe_files: NativePipeFiles,
    ) -> Result<(Self, Option<Child>)> {
        let cmd_str = cmd.display().to_string();
        let child = (!cmd_str.is_empty()).then(|| {
            tracing::info!(
                "Starting preimage server process: {} {:?}",
                cmd.display(),
                args
            );

            let mut command = Command::new(cmd);
            let command = {
                // Grab the file descriptors for the hint and preimage channels
                // that the server will use to communicate with the FPVM
                let fds = [
                    pipe_files.preimage_read.as_raw_fd(),
                    pipe_files.preimage_write.as_raw_fd(),
                    pipe_files.hint_read.as_raw_fd(),
                    pipe_files.hint_write.as_raw_fd()
                ];

                tracing::info!(target: "howitzer::preimage::server", "Starting preimage server process: {:?} with fds {:?}", args, fds);

                command
                    .args(args)
                    .stdout(io::stdout())
                    .stderr(io::stderr())
                    .fd_mappings(
                        fds.iter().enumerate()
                            .map(|(i, fd)| FdMapping {
                                parent_fd: *fd,
                                child_fd: 3 + i as i32,
                            })
                            .collect(),
                    )?
            };

            command.spawn().map_err(|e| anyhow::anyhow!("Failed to start preimage server process: {}", e))
        });

        Ok((
            Self {
                hint_writer_client: HintWriter::new(hint_pipe),
                preimage_client: OracleReader::new(preimage_pipe),
            },
            child.transpose()?,
        ))
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

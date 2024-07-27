//! Utilities for the `howitzer` crate.

use anyhow::{anyhow, Result};
use kona_common::FileDescriptor;
use kona_preimage::PipeHandle;
use std::{fs::File, os::fd::AsRawFd};

/// Represents the files that are used to communicate with the native client.
pub struct NativePipeFiles {
    /// The file that the preimage oracle reads from.
    pub preimage_read: File,
    /// The file that the preimage oracle writes to.
    pub preimage_write: File,
    /// The file that the hint reader reads from.
    pub hint_read: File,
    /// The file that the hint reader writes to.
    pub hint_write: File,
}

/// Creates two temporary files that are connected by a pipe.
pub(crate) fn create_temp_files() -> Result<(File, File)> {
    let (read, write) = (
        tempfile::tempfile().map_err(|e| anyhow!(e))?,
        tempfile::tempfile().map_err(|e| anyhow!(e))?,
    );
    Ok((read, write))
}

/// Create a pair of pipes for the preimage oracle and hint reader. Also returns the files that are
/// used to create the pipes, which must be kept alive until the pipes are closed.
pub(crate) fn create_native_pipes() -> Result<(PipeHandle, PipeHandle, NativePipeFiles)> {
    let (po_reader, po_writer) = create_temp_files()?;
    let (hint_reader, hint_writer) = create_temp_files()?;
    let preimage_pipe = PipeHandle::new(
        FileDescriptor::Wildcard(
            po_reader.as_raw_fd().try_into().map_err(|e| anyhow!("Failed to get raw FD: {e}"))?,
        ),
        FileDescriptor::Wildcard(
            po_writer.as_raw_fd().try_into().map_err(|e| anyhow!("Failed to get raw FD: {e}"))?,
        ),
    );
    let hint_pipe = PipeHandle::new(
        FileDescriptor::Wildcard(
            hint_reader.as_raw_fd().try_into().map_err(|e| anyhow!("Failed to get raw FD: {e}"))?,
        ),
        FileDescriptor::Wildcard(
            hint_writer.as_raw_fd().try_into().map_err(|e| anyhow!("Failed to get raw FD: {e}"))?,
        ),
    );

    let files = NativePipeFiles {
        preimage_read: po_reader,
        preimage_write: po_writer,
        hint_read: hint_reader,
        hint_write: hint_writer,
    };

    Ok((preimage_pipe, hint_pipe, files))
}

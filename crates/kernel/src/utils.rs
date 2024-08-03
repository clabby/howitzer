//! Utilities for the `howitzer` crate.

use anyhow::Result;
use os_pipe::{PipeReader, PipeWriter};
use std::fs::File;

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

/// Creates a set of bidirectional pipes.
pub(crate) fn bidirectional_pipe() -> Result<((PipeReader, PipeWriter), (PipeReader, PipeWriter))> {
    let (ar, bw) = os_pipe::pipe()?;
    let (br, aw) = os_pipe::pipe()?;
    Ok(((ar, aw), (br, bw)))
}

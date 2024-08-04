//! Utilities for the `howitzer` crate.

use anyhow::Result;
use os_pipe::{PipeReader, PipeWriter};

/// Creates a set of bidirectional pipes.
pub(crate) fn bidirectional_pipe() -> Result<((PipeReader, PipeWriter), (PipeReader, PipeWriter))> {
    let (ar, bw) = os_pipe::pipe()?;
    let (br, aw) = os_pipe::pipe()?;
    Ok(((ar, aw), (br, bw)))
}

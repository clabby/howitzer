//! Utilities for the `howitzer` crate.

use anyhow::Result;
use os_pipe::{PipeReader, PipeWriter};

/// A bidirectional pipe.
pub struct BidirectionalPipe {
    /// The client handle
    pub client: Pipe,
    /// The host handle
    pub host: Pipe,
}

/// A single pipe.
pub struct Pipe {
    /// The reader
    pub reader: PipeReader,
    /// The writer
    pub writer: PipeWriter,
}

/// Creates a set of bidirectional pipes.
pub(crate) fn bidirectional_pipe() -> Result<BidirectionalPipe> {
    let (ar, bw) = os_pipe::pipe()?;
    let (br, aw) = os_pipe::pipe()?;
    Ok(BidirectionalPipe {
        client: Pipe { reader: ar, writer: aw },
        host: Pipe { reader: br, writer: bw },
    })
}

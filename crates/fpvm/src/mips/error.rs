//! Error types for the MIPS virtual machine.

/// A [Result] type over a generic value with [VMError].
pub type VMResult<T> = Result<T, VMError>;

/// An error within the MIPS virtual machine
pub enum VMError {
    Fatal
}

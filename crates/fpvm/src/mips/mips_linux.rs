//! Linux-specific MIPS64 constructs.

/// A [Syscall] is a system call that can be made to the kernel from userspace within the emulator.
///
/// Syscalls in this list are specific to the MIPS64 architecture.
pub enum Syscall {
    Mmap = 5009,
    Brk = 5012,
    Clone = 5055,
    ExitGroup = 5205,
    Read = 5000,
    Write = 5001,
    Fcntl = 5070,
}

impl TryFrom<u64> for Syscall {
    type Error = anyhow::Error;

    fn try_from(n: u64) -> Result<Self, Self::Error> {
        match n {
            5009 => Ok(Syscall::Mmap),
            5012 => Ok(Syscall::Brk),
            5055 => Ok(Syscall::Clone),
            5205 => Ok(Syscall::ExitGroup),
            5000 => Ok(Syscall::Read),
            5001 => Ok(Syscall::Write),
            5070 => Ok(Syscall::Fcntl),
            _ => anyhow::bail!("Failed to convert {} to Syscall", n),
        }
    }
}

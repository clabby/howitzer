# `howitzer-fpvm`

The `howitzer-fpvm` crate contains the low-level MIPS64 emulator, with minimal Linux system call support. It is
implemented following the [MIPS64r2][mips64] specification and [Linux][linux] system manual.

## Features

- `tracing`: Enables tracing within the VM. This is useful for debugging, but does not need to be enabled in production
  environments for performance reasons, unless a store of logs is required.
- `simd-keccak`: Exclusive to ARMv8-A processors. Uses the [`keccak256-aarch64-simd`](https://github.com/clabby/keccak256-aarch64/tree/master) crate
  for performance-critical `keccak256` hashing, which provides a very significant speedup to merkleization. **Warning**:
  This crate is _highly_ experimental, and it is not suggested that this feature is enabled in production, unless you
  understand the risks associated with enabling it.

[mips64]: https://scc.ustc.edu.cn/zlsc/lxwycj/200910/W020100308600769158777.pdf
[linux]: https://www.man7.org/linux/man-pages/man1/man.1.html

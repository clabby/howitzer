<h1 align="center">
<img src="./assets/banner.png" alt="Howitzer" width="100%" align="center">
</h1>

<h4 align="center">
    An evolution of the OP Stack's <a href="https://github.com/ethereum-optimism/optimism/tree/develop/cannon">Cannon</a> FPVM, written in pure Rust.
</h4>

<p align="center">
  <a href="https://github.com/clabby/howitzer-rs/actions/workflows/ci.yaml">
    <img src="https://github.com/clabby/howitzer-rs/actions/workflows/ci.yaml/badge.svg?label=ci" alt="Ci">
  </a>
  <img src="https://img.shields.io/badge/License-MIT-green.svg?label=license" alt="License">
  <a href="https://github.com/ethereum-optimism/monorepo"><img src="https://img.shields.io/badge/OP%20Stack-monorepo-red" alt="OP Stack"></a>
</p>

<p align="center">
  <a href="#whats-a-howitzer">What's a Howitzer?</a> •
  <a href="#overview">Overview</a> •
  <a href="#docker">Docker</a> •
  <a href="#contributing">Contributing</a> •
  <a href="#documentation">Documentation</a> •
  <a href="#credits">Credits</a>
</p>

## What's a Howitzer?

Howitzer is a MIPS64 emulator designed to simulate deterministic execution within a single MIPS thread context both
natively and on the EVM. Its primary objective is to execute [Fault Proof Programs][fpp-specs] such as [`kona`][kona]
or [`op-program`][op-program] for the sake of the [OP Stack][monorepo]'s interactive dispute protocol.

_TL;DR:_

- It's Rust code
- ...that was [originally Go code][cannon]
- ...that runs an EVM
- ...emulating a MIPS64 machine
- ...that was originally a MIPS32 machine
- ...running compiled [Rust][kona] or [Go][op-program] code
- ...that runs an EVM

## Overview

- [`howitzer`](./bin) - The binary for executing MIPS64 programs natively on top of Howitzer with a detached preimage server.
- [`howitzer-kernel`](./crates/kernel) - High-level library for running the Howitzer FPVM with a detached preimage server.
- [`howitzer-fpvm`](./crates/fpvm) - Contains the native implementation of the MIPS thread context emulator.
- [`howitzer-contracts`](./contracts) - Contains the EVM implementation of the MIPS thread context emulator.

## Docker

The docker image for `howitzer` is located in the [docker](./docker) directory, and can be built using the
script provided.

## Contributing

To get started, a few dependencies are required:

- [Rust toolchain][rustup]
  - Recommended: [`cargo-nextest`][nextest]
- [Just][just]
- [Go toolchain][golang]
- [binutils][binutils]

### Testing

```sh
just test
```

### Linting and Formatting

```sh
just lint
```

### Running Benchmarks

```sh
just bench
```

## Documentation

Rustdocs are available by running `cargo doc --open` after cloning the repo.

### Specification

The specification for both Cannon and the preimage oracle can be found in the [Optimism monorepo][monorepo].

- [Cannon specification][cannon-specs]
- [Preimage oracle specification][fpp-specs]

## Credits

This repository is heavily inspired by the original [Cannon][cannon] VM, built by [George Hotz][geohot] and members of the
[OP Labs][op-labs] team. The original implementation is written in Go, and can be found [in the Optimism monorepo][cannon]. All
credits for the original idea and reference implementation of this concept go to these folks.

[geohot]: https://github.com/geohot
[op-labs]: https://oplabs.co
[monorepo]: https://github.com/ethereum-optimism/optimism
[cannon]: https://github.com/ethereum-optimism/optimism/tree/develop/cannon
[kona]: https://github.com/ethereum-optimism/kona
[op-program]: https://github.com/ethereum-optimism/optimism/tree/develop/op-program
[op-challenger]: https://github.com/ethereum-optimism/optimism/tree/develop/op-challenger
[fpp-specs]: https://specs.optimism.io/fault-proof/index.html
[cannon-specs]: https://github.com/ethereum-optimism/optimism/blob/develop/specs/cannon-fault-proof-vm.md
[rustup]: https://rustup.rs/
[golang]: https://go.dev/doc/install
[binutils]: https://www.gnu.org/software/binutils/
[nextest]: https://nexte.st/
[just]: https://github.com/casey/just

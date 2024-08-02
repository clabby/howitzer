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
  <a href="#credits">Credits</a> •
  <a href="#benchmarks">Benchmarks</a> •
  <a href="#contributing">Contributing</a> •
  <a href="#documentation">Documentation</a> •
  <a href="#docker">Docker</a>
</p>

## What's a Howitzer?

Howitzer is an emulator designed to simulate a single MIPS thread context on the EVM. Its primary use is to execute the [`op-program`][op-program]
(also known as the fault-proof program) for the [OP Stack][monorepo]'s interactive dispute protocol. The `op-program` consists
of a stripped down version of `op-geth`'s state transition code in addition to the derivation pipeline, and produces deterministic results.
Subsequently, it is compiled to MIPS to be ran on top of Howitzer on-chain to prove fault in claims about the state of L2 on L1. Howitzer also has a
native implementation of the MIPS thread context that mirrors the on-chain version, which enables the [op-challenger][op-challenger] to generate
state commitments for an `op-program` execution trace and participate in dispute games.

_TL;DR:_

- It's Rust code
- ...that was [originally Go code][cannon]
- ...that runs an EVM
- ...emulating a MIPS64 machine
- ...that was originally a MIPS32 machine
- ...running [compiled Go code][op-program]
- ...that runs an EVM

## Overview

- [`howitzer-fpvm`](./crates/fpvm) - Contains the native implementation of the MIPS thread context emulator.
- [`howitzer-contracts`](https://github.com/ethereum-optimism/optimism/tree/develop/packages/contracts-bedrock/src/cannon) - [*in OP monorepo*] Contains the Solidity implementation of the MIPS thread context and the Preimage Oracle. (TODO: Will be replaced with Howitzer contracts, as the VM architectures will differ.)

## Credits

This repository is heavily inspired by the original [Cannon][cannon], built by [George Hotz][geohot] and members of the [OP Labs][op-labs] team. The original implementation is written in Go, and can be found [in the Optimism monorepo][cannon]. All
credits for the original idea and reference implementation of this concept go to these folks.

## Benchmarks

### `howitzer-fpvm` benchmarks

_TODO_

## Contributing

To get started, a few dependencies are required:

- [Rust toolchain][rustup]
  - Recommended: [`cargo-nextest`][nextest]
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

## Docker

The docker image for `howitzer` is located in the [docker](./docker) directory, and can be built using the
script provided.

[geohot]: https://github.com/geohot
[op-labs]: https://oplabs.co
[monorepo]: https://github.com/ethereum-optimism/optimism
[cannon]: https://github.com/ethereum-optimism/optimism/tree/develop/cannon
[op-program]: https://github.com/ethereum-optimism/optimism/tree/develop/op-program
[op-challenger]: https://github.com/ethereum-optimism/optimism/tree/develop/op-challenger
[rustup]: https://rustup.rs/
[golang]: https://go.dev/doc/install
[binutils]: https://www.gnu.org/software/binutils/
[nextest]: https://nexte.st/
[fpp-specs]: https://github.com/ethereum-optimism/optimism/blob/develop/specs/fault-proof.md
[cannon-specs]: https://github.com/ethereum-optimism/optimism/blob/develop/specs/cannon-fault-proof-vm.md

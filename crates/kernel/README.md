# `howitzer-kernel`

The `howitzer-kernel` crate provides a high-level interface to run the howitzer FPVM, which consists of the [MIPS32 emulator][fpvm]
as well as the [preimage oracle server][preimage-oracle].

The interaction between these two processes is fully synchronous. While the emulator is running, the preimage oracle
server is blocked on waiting for hints and preimage requests from the emulator. During the time that the preimage oracle server
is working, the emulator is blocked on waiting for the preimage oracle server to respond.

```text
┌──────┐   ┌───────────────┐
│ fpvm │   │preimage-server│
└───┬──┘   └───────┬───────┘
    │              │
    │     Hint     │
    │─────────────>│
    │              │
    │   Ack hint   │
    │<─────────────│
    │              │
    │ Get Preimage │
    │─────────────>│
    │              │
    │ Ret preimage │
    │<─────────────│
┌───┴──┐   ┌───────┴───────┐
│ fpvm │   │preimage-server│
└──────┘   └───────────────┘
```

[fpvm]: ../fpvm
[preimage-oracle]: https://github.com/ethereum-optimism/kona

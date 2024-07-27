//! The MIPS module contains the implementation of the [InstrumentedState] and the MIPS emulator.

mod instrumented;
pub use instrumented::InstrumentedState;

mod mips_vm;

//! Subcommands for the `howitzer` binary

use anyhow::Result;
use async_trait::async_trait;
use clap::Subcommand;

mod load_elf;
mod run;
mod witness;

#[async_trait]
pub(crate) trait HowitzerSubcommandDispatcher {
    /// Dispatches the subcommand
    async fn dispatch(self) -> Result<()>;
}

/// The subcommands for the `howitzer` binary
#[derive(Subcommand, Debug)]
pub(crate) enum HowitzerSubcommand {
    /// Run a program on Howitzer with a detached preimage oracle server
    Run(run::RunArgs),
    /// Convert a state snapshot to a state witness
    Witness(witness::WitnessArgs),
    /// Load an ELF file into a Howitzer state snapshot
    LoadElf(load_elf::LoadElfArgs),
}

#[async_trait]
impl HowitzerSubcommandDispatcher for HowitzerSubcommand {
    async fn dispatch(self) -> Result<()> {
        match self {
            HowitzerSubcommand::Run(args) => args.dispatch().await,
            HowitzerSubcommand::Witness(args) => args.dispatch().await,
            HowitzerSubcommand::LoadElf(args) => args.dispatch().await,
        }
    }
}

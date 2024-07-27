//! Subcommands for the `howitzer` binary

use anyhow::Result;
use clap::Subcommand;

mod load_elf;
mod run;
mod witness;

pub(crate) trait HowitzerSubcommandDispatcher {
    /// Dispatches the subcommand
    fn dispatch(self) -> Result<()>;
}

/// The subcommands for the `howitzer` binary
#[derive(Subcommand, Debug)]
pub(crate) enum HowitzerSubcommand {
    Run(run::RunArgs),
    Witness(witness::WitnessArgs),
    LoadElf(load_elf::LoadElfArgs),
}

impl HowitzerSubcommandDispatcher for HowitzerSubcommand {
    fn dispatch(self) -> Result<()> {
        match self {
            HowitzerSubcommand::Run(args) => args.dispatch(),
            HowitzerSubcommand::Witness(args) => args.dispatch(),
            HowitzerSubcommand::LoadElf(args) => args.dispatch(),
        }
    }
}

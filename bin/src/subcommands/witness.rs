//! The `witness` subcommand for the howitzer binary

use super::HowitzerSubcommandDispatcher;
use alloy_primitives::B256;
use anyhow::Result;
use howitzer_kernel::gz::decompress_bytes;
use howitzer_fpvm::types::{state_hash, State};
use clap::Args;
use std::{fs, path::PathBuf};

/// Command line arguments for `howitzer witness`
#[derive(Args, Debug)]
#[command(author, version, about)]
pub(crate) struct WitnessArgs {
    /// The path to the input JSON state.
    #[arg(long)]
    input: PathBuf,

    /// The path to the output JSON state.
    #[arg(long)]
    output: Option<PathBuf>,
}

impl HowitzerSubcommandDispatcher for WitnessArgs {
    fn dispatch(self) -> Result<()> {
        tracing::info!(target: "howitzer-cli::witness", "Loading state JSON dump from {}", self.input.display());

        let state_raw = fs::read(&self.input)?;
        let mut state: State = serde_json::from_slice(&decompress_bytes(&state_raw)?)?;

        tracing::info!(target: "howitzer-cli::witness", "Loaded state JSON dump and deserialized the State");

        let witness = state.encode_witness()?;
        let witness_hash = state_hash(witness);

        tracing::info!(target: "howitzer-cli::witness", "Encoded witness and computed witness hash: {}", B256::from(witness_hash));

        match self.output {
            Some(ref output_path) => fs::write(output_path, witness).map_err(|_| {
                anyhow::anyhow!("Failed to write witness to {}", output_path.display())
            }),
            None => {
                println!("{}", B256::from(witness_hash));
                Ok(())
            }
        }?;

        tracing::info!(target: "howitzer-cli::witness", "Wrote witness to {}", self.output.as_ref().map_or("stdout".to_string(), |p| p.display().to_string()));
        Ok(())
    }
}

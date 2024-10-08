use crate::subcommands::HowitzerSubcommandDispatcher;
use anyhow::{anyhow, Result};
use clap::{ArgAction, ColorChoice, Parser};
use tracing::Level;

mod subcommands;

/// Comand line arguments for `howitzer` binary
#[derive(Parser, Debug)]
#[command(author, version, about, color = ColorChoice::Always)]
struct Args {
    /// Verbosity level (0-4)
    #[arg(long, short, action = ArgAction::Count, default_value = "2")]
    v: u8,

    /// The subcommand to run
    #[command(subcommand)]
    subcommand: subcommands::HowitzerSubcommand,
}

#[tokio::main]
async fn main() -> Result<()> {
    // Parse the command arguments
    let Args { v, subcommand } = Args::parse();

    // Initialize the tracing subscriber
    init_tracing_subscriber(v)?;

    tracing::debug!(target: "howitzer-cli", "Dispatching subcommand");
    subcommand.dispatch().await?;

    Ok(())
}

/// Initializes the tracing subscriber
///
/// # Arguments
/// * `verbosity_level` - The verbosity level (0-4)
///
/// # Returns
/// * `Result<()>` - Ok if successful, Err otherwise.
fn init_tracing_subscriber(verbosity_level: u8) -> Result<()> {
    let subscriber = tracing_subscriber::fmt()
        .with_max_level(match verbosity_level {
            0 => Level::ERROR,
            1 => Level::WARN,
            2 => Level::INFO,
            3 => Level::DEBUG,
            _ => Level::TRACE,
        })
        .finish();
    tracing::subscriber::set_global_default(subscriber).map_err(|e| anyhow!(e))
}

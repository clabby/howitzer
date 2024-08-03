//! The `load-elf` subcommand for the howitzer binary

use super::HowitzerSubcommandDispatcher;
use alloy_primitives::B256;
use anyhow::Result;
use clap::Args;
use howitzer_fpvm::{
    state::state_hash,
    utils::patch::{load_elf, patch_go, patch_stack},
};
use howitzer_kernel::gz::compress_bytes;
use std::{
    fmt::Display,
    fs::File,
    io::{BufReader, BufWriter, Read, Write},
    path::PathBuf,
    str::FromStr,
};

/// Command line arguments for `howitzer load-elf`
#[derive(Args, Debug)]
#[command(author, version, about)]
pub(crate) struct LoadElfArgs {
    /// The path to the input 32-bit big-endian MIPS ELF file.
    #[arg(long, short)]
    input: PathBuf,

    /// The type of patch to perform on the ELF file.
    #[arg(long, short, default_values = ["go", "stack"])]
    patch_kind: Vec<PatchKind>,

    /// The output path to write the JSON state to. State will be dumped to stdout if set to `-`.
    /// Not written if not provided.
    #[arg(long, short)]
    output: Option<String>,
}

#[derive(Clone, Debug)]
enum PatchKind {
    Go,
    Stack,
}

impl FromStr for PatchKind {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "go" => Ok(PatchKind::Go),
            "stack" => Ok(PatchKind::Stack),
            _ => Err(anyhow::anyhow!("Invalid patch kind: {}", s)),
        }
    }
}

impl Display for PatchKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PatchKind::Go => write!(f, "Go"),
            PatchKind::Stack => write!(f, "Stack"),
        }
    }
}

impl HowitzerSubcommandDispatcher for LoadElfArgs {
    fn dispatch(self) -> Result<()> {
        tracing::info!(target: "howitzer-cli::load-elf", "Loading ELF file @ {}", self.input.display());
        let file = File::open(&self.input)?;
        let file_sz = file.metadata()?.len();
        let mut reader = BufReader::new(file);
        let mut elf_raw = Vec::with_capacity(file_sz as usize);
        reader.read_to_end(&mut elf_raw)?;
        let mut state = load_elf(&elf_raw)?;
        tracing::info!(target: "howitzer-cli::load-elf", "Loaded ELF file and constructed the State");

        for p in self.patch_kind {
            tracing::info!(target: "howitzer-cli::load-elf", "Patching the ELF file with patch type = {p}...");
            match p {
                PatchKind::Go => patch_go(&elf_raw, &mut state),
                PatchKind::Stack => patch_stack(&mut state),
            }?;
        }

        state.memory.flush_page_cache();

        if let Some(ref path_str) = self.output {
            if path_str == "-" {
                println!("{}", serde_json::to_string(&state)?);
            } else {
                let mut writer = BufWriter::new(File::create(path_str)?);
                let ser_state = serde_json::to_vec(&state)?;
                let gz_state = compress_bytes(&ser_state)?;
                writer.write_all(&gz_state)?;
            }
        }

        tracing::info!(target: "howitzer-cli::load-elf", "Patched the ELF file and dumped the State successfully. state hash: {} mem size: {} pages: {}", B256::from(state_hash(state.encode_witness()?)), state.memory.usage(), state.memory.page_count());

        Ok(())
    }
}

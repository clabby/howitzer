//! This module contains the [HowitzerVM] definition.

use super::proof::ProofMeta;
use crate::{memory::Memory, state::State};
use kona_preimage::{HintRouter, PreimageFetcher};
use std::io::{self, BufWriter, Stderr, Stdout};

/// The [HowitzerVM] is a wrapper around [State] that contains cached machine state,
/// the input and output buffers, and an implementation of the MIPS VM.
///
/// To perform an instruction step on the MIPS emulator, use the [HowitzerVM::step] method.
#[derive(Debug)]
pub struct HowitzerVM<M, P>
where
    M: Memory,
    P: HintRouter + PreimageFetcher,
{
    /// The inner [State] of the MIPS thread context.
    pub state: State<M>,
    /// The proof metadata
    pub proof_meta: ProofMeta<M>,
    /// The MIPS thread context's stdout buffer.
    pub(crate) std_out: BufWriter<Stdout>,
    /// The MIPS thread context's stderr buffer.
    pub(crate) std_err: BufWriter<Stderr>,
    /// The [HintRouter] + [PreimageFetcher] used to fetch preimages.
    pub(crate) preimage_oracle: P,
}

impl<M, P> HowitzerVM<M, P>
where
    M: Memory,
    P: HintRouter + PreimageFetcher,
{
    /// Create a new [HowitzerVM].
    pub fn new(state: State<M>, oracle: P) -> Self {
        Self {
            state,
            proof_meta: Default::default(),
            std_out: BufWriter::new(io::stdout()),
            std_err: BufWriter::new(io::stderr()),
            preimage_oracle: oracle,
        }
    }

    /// Returns a reference the stdout buffer.
    pub fn std_out(&self) -> &[u8] {
        self.std_out.buffer()
    }

    /// Returns a reference the stderr buffer.
    pub fn std_err(&self) -> &[u8] {
        self.std_err.buffer()
    }
}

#[cfg(test)]
mod test {
    use crate::{
        memory::{Address, Memory, TrieMemory},
        mips::HowitzerVM,
        state::State,
        test_utils::{ClaimTestOracle, StaticOracle, BASE_ADDR_END, END_ADDR},
        utils::{
            meta::Meta,
            patch::{load_elf, patch_go, patch_stack},
        },
    };
    use elf::{endian::AnyEndian, ElfBytes};
    use std::{fs, io::BufReader};

    #[tokio::test]
    async fn open_mips_tests() {
        let tests_path =
            std::env::current_dir().unwrap().join("open_mips_tests").join("test").join("bin");
        let test_files = fs::read_dir(tests_path).unwrap().flatten();

        for f in test_files.into_iter() {
            let file_name = String::from(f.file_name().to_str().unwrap());

            // Short circuit early for `exit_group.bin`
            let exit_group = file_name == "exit_group.bin";

            let program_mem = fs::read(f.path()).unwrap();

            let memory = TrieMemory::default();
            let mut state = State { pc: 0, next_pc: 4, memory, ..Default::default() };
            state.memory.set_memory_range(0, BufReader::new(program_mem.as_slice())).unwrap();

            // Set the return address ($ra) to jump into when the test completes.
            state.registers[31] = END_ADDR;

            let mut ins = HowitzerVM::new(state, StaticOracle::new(b"hello world".to_vec()));

            for _ in 0..1000 {
                if ins.state.pc == END_ADDR {
                    break;
                }
                if exit_group && ins.state.exited {
                    break;
                }
                ins.step(false).await.unwrap();
            }

            if exit_group {
                assert_ne!(END_ADDR, ins.state.pc, "must not reach end");
                assert!(ins.state.exited, "must exit");
                assert_eq!(1, ins.state.exit_code, "must exit with 1");
            } else {
                assert_eq!(END_ADDR, ins.state.pc, "must reach end");
                let mut state = ins.state.memory;
                let (done, result) = (
                    state.get_word((BASE_ADDR_END + 4) as Address).unwrap(),
                    state.get_word((BASE_ADDR_END + 8) as Address).unwrap(),
                );
                assert_eq!(done, 1, "must set done to 1 {:?}", f.file_name());
                assert_eq!(result, 1, "must have success result {:?}", f.file_name());
                println!("Test passed: {:?}", f.file_name());
            }
        }
    }

    #[tokio::test]
    async fn test_hello() {
        let elf_bytes = include_bytes!("../../../../example/bin/hello.elf");
        let mut state = load_elf::<TrieMemory>(elf_bytes).unwrap();
        patch_go(elf_bytes, &mut state).unwrap();
        patch_stack(&mut state).unwrap();

        let metadata =
            Meta::from_elf(ElfBytes::<AnyEndian>::minimal_parse(elf_bytes).unwrap()).unwrap();
        let mut ins = HowitzerVM::new(state, StaticOracle::new(b"hello world".to_vec()));

        let mut last_symbol = None;
        for _ in 0..400_000 {
            let symbol = metadata.lookup(ins.state.pc);
            if last_symbol.unwrap_or_default() != symbol {
                println!("pc: 0x{:x} symbol name: {}", ins.state.pc, symbol);
            }
            last_symbol = Some(symbol);

            if ins.state.exited {
                break;
            }
            ins.step(false).await.unwrap();
        }

        assert!(ins.state.exited, "must exit");
        assert_eq!(ins.state.exit_code, 0, "must exit with 0");

        assert_eq!(String::from_utf8(ins.std_out.buffer().to_vec()).unwrap(), "hello world!\n");
        assert_eq!(String::from_utf8(ins.std_err.buffer().to_vec()).unwrap(), "");
    }

    #[tokio::test]
    async fn test_claim() {
        let elf_bytes = include_bytes!("../../../../example/bin/claim.elf");
        let mut state = load_elf::<TrieMemory>(elf_bytes).unwrap();
        patch_go(elf_bytes, &mut state).unwrap();
        patch_stack(&mut state).unwrap();

        let metadata =
            Meta::from_elf(ElfBytes::<AnyEndian>::minimal_parse(elf_bytes).unwrap()).unwrap();
        let mut ins = HowitzerVM::new(state, ClaimTestOracle::default());

        let mut last_symbol = None;
        for _ in 0..5_000_000 {
            let symbol = metadata.lookup(ins.state.pc);
            if last_symbol.unwrap_or_default() != symbol {
                println!("pc: 0x{:x} symbol name: {}", ins.state.pc, symbol);
            }
            last_symbol = Some(symbol);

            if ins.state.exited {
                break;
            }
            ins.step(false).await.unwrap();
        }

        assert!(ins.state.exited, "must exit");
        assert_eq!(ins.state.exit_code, 0, "must exit with 0");

        assert_eq!(
            String::from_utf8(ins.std_out.buffer().to_vec()).unwrap(),
            format!(
                "computing {} * {} + {}\nclaim {} is good!\n",
                ClaimTestOracle::S,
                ClaimTestOracle::A,
                ClaimTestOracle::B,
                ClaimTestOracle::S * ClaimTestOracle::A + ClaimTestOracle::B
            )
        );
        assert_eq!(String::from_utf8(ins.std_err.buffer().to_vec()).unwrap(), "started!");
    }
}

//! This module contains the [InstrumentedState] definition.

use super::isa::DoubleWord;
use crate::{
    memory::{Address, Memory},
    state::{State, StepWitness},
};
use anyhow::Result;
use kona_preimage::{HintRouter, PreimageFetcher};
use std::io::{BufWriter, Write};

/// The [InstrumentedState] is a wrapper around [State] that contains cached machine state,
/// the input and output buffers, and an implementation of the MIPS VM.
///
/// To perform an instruction step on the MIPS emulator, use the [InstrumentedState::step] method.
#[derive(Debug)]
pub struct InstrumentedState<M, O, E, P>
where
    M: Memory,
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    /// The inner [State] of the MIPS thread context.
    pub state: State<M>,
    /// The MIPS thread context's stdout buffer.
    pub(crate) std_out: BufWriter<O>,
    /// The MIPS thread context's stderr buffer.
    pub(crate) std_err: BufWriter<E>,

    /// Whether or not the memory proof generation is enabled.
    pub(crate) mem_proof_enabled: bool,
    /// The last address we accessed in memory.
    pub(crate) last_mem_access: Option<Address>,
    /// The memory proof, if it is enabled.
    pub(crate) mem_proof: Option<M::Proof>,

    /// The [HintRouter] + [PreimageFetcher] used to fetch preimages.
    pub(crate) preimage_oracle: P,
    /// Cached pre-image data, including 8 byte length prefix
    pub(crate) last_preimage: Vec<u8>,
    /// Key for the above preimage
    pub(crate) last_preimage_key: [u8; 32],
    /// The offset we last read from, or max u64 if nothing is read at
    /// the current step.
    pub(crate) last_preimage_offset: Option<DoubleWord>,
}

impl<M, O, E, P> InstrumentedState<M, O, E, P>
where
    M: Memory,
    O: Write,
    E: Write,
    P: HintRouter + PreimageFetcher,
{
    /// Create a new [InstrumentedState].
    pub fn new(state: State<M>, oracle: P, std_out: O, std_err: E) -> Self {
        Self {
            state,
            std_out: BufWriter::new(std_out),
            std_err: BufWriter::new(std_err),
            last_mem_access: None,
            mem_proof_enabled: false,
            mem_proof: Default::default(),
            preimage_oracle: oracle,
            last_preimage: Vec::default(),
            last_preimage_key: [0u8; 32],
            last_preimage_offset: None,
        }
    }

    /// Step the MIPS emulator forward one instruction.
    ///
    /// ### Returns
    /// - Ok(Some(witness)): The [StepWitness] for the current
    /// - Err(_): An error occurred while processing the instruction step in the MIPS emulator.
    pub async fn step(&mut self, proof: bool) -> Result<Option<StepWitness<M>>> {
        self.mem_proof_enabled = proof;
        self.last_mem_access = None;
        self.last_preimage_offset = None;

        // Reset witness generation parameters
        if !proof {
            self.inner_step().await?;
            Ok(None)
        } else {
            // Formulate the state witness as well as the instruction proof prior to performing the
            // state transition.
            let mut witness = {
                // Generate a merkle proof for the page containing the current instruction.
                let instruction_proof = self.state.memory.proof(self.state.pc as Address)?;

                // Allocate the proof vector and push the instruction proof.
                let mut proof = Vec::with_capacity(2);
                proof.push(instruction_proof);

                StepWitness { state: self.state.encode_witness()?, proof, ..Default::default() }
            };

            // Perform the state transition.
            self.inner_step().await?;

            // Update the witness with the memory access proof and preimage data, if there was a
            // preimage read within the state transition.
            if let Some(mem_proof) = self.mem_proof.take() {
                witness.proof.push(mem_proof);
            }

            if self.last_preimage_offset.is_some() {
                witness.preimage_key = Some(self.last_preimage_key);
                witness.preimage_value = Some(self.last_preimage.clone());
                witness.preimage_offset = self.last_preimage_offset;
            }

            Ok(Some(witness))
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
        mips::InstrumentedState,
        state::State,
        test_utils::{ClaimTestOracle, StaticOracle, BASE_ADDR_END, END_ADDR},
        utils::{
            meta::Meta,
            patch::{load_elf, patch_go, patch_stack},
        },
    };
    use elf::{endian::AnyEndian, ElfBytes};
    use std::{
        fs,
        io::{self, BufReader, BufWriter},
    };

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

            let mut ins = InstrumentedState::new(
                state,
                StaticOracle::new(b"hello world".to_vec()),
                io::stdout(),
                io::stderr(),
            );

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

        let out = BufWriter::new(Vec::default());
        let err = BufWriter::new(Vec::default());
        let mut ins =
            InstrumentedState::new(state, StaticOracle::new(b"hello world".to_vec()), out, err);

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

        let out = BufWriter::new(Vec::default());
        let err = BufWriter::new(Vec::default());
        let mut ins = InstrumentedState::new(state, ClaimTestOracle::default(), out, err);

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

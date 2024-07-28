//! This module contains a wrapper around a [revm] inspector with an in-memory backend
//! that has the MIPS & PreimageOracle smart contracts deployed at deterministic addresses.

// use crate::types::{state_hash, StateWitness, StepWitness};
// use anyhow::Result;
// use revm::{
//     db::{CacheDB, EmptyDB},
//     primitives::{
//         hex, AccountInfo, Address, Bytecode, Bytes, Output, ResultAndState, TransactTo, TxEnv,
//         B256, U256,
//     },
//     Database, Evm, EvmBuilder,
// };
//
// /// The address of the deployed MIPS VM on the in-memory EVM.
// pub const MIPS_ADDR: [u8; 20] = hex!("000000000000000000000000000000000000C0DE");
// /// The address of the deployed PreimageOracle on the in-memory EVM.
// pub const PREIMAGE_ORACLE_ADDR: [u8; 20] = hex!("00000000000000000000000000000000424f4f4b");
//
// /// The creation EVM bytecode of the MIPS contract. Does not include constructor arguments.
// pub const MIPS_CREATION_CODE: &str = include_str!("../../bindings/mips_creation.bin");
// /// The deployed EVM bytecode of the PreimageOracle contract.
// pub const PREIMAGE_ORACLE_DEPLOYED_CODE: &str =
//     include_str!("../../bindings/preimage_creation.bin");
//
// /// A wrapper around a [revm] interpreter with an in-memory backend that has the MIPS &
// /// PreimageOracle smart contracts deployed at deterministic addresses. This is used for
// /// differential testing the implementation of the MIPS VM in this crate against the smart contract
// /// implementations.
// pub struct MipsEVM<'a, DB: Database> {
//     pub inner: Evm<'a, (), DB>,
// }
//
// impl<'a> Default for MipsEVM<'a, CacheDB<EmptyDB>> {
//     fn default() -> Self {
//         Self::new()
//     }
// }
//
// impl<'a> MipsEVM<'a, CacheDB<EmptyDB>> {
//     /// Creates a new MIPS EVM with an in-memory backend.
//     pub fn new() -> Self {
//         let evm = EvmBuilder::default().with_db(CacheDB::default()).build();
//         Self { inner: evm }
//     }
//
//     /// Initializes the EVM with the MIPS contracts deployed.
//     ///
//     /// ### Returns
//     /// - A [Result] indicating whether the initialization was successful.
//     pub fn try_init(&mut self) -> Result<()> {
//         let db = self.inner.db_mut();
//
//         // Fund the zero address.
//         db.insert_account_info(
//             Address::ZERO,
//             AccountInfo {
//                 balance: U256::from(u128::MAX),
//                 nonce: 0,
//                 code_hash: B256::ZERO,
//                 code: None,
//             },
//         );
//
//         // Deploy the PreimageOracle contract.
//         let preimage_creation_heap = hex::decode(PREIMAGE_ORACLE_DEPLOYED_CODE)?
//             .into_iter()
//             .chain([0u8; 64])
//             .collect::<Vec<_>>();
//         self.fill_tx_env(TransactTo::Create, preimage_creation_heap.into());
//         if let Ok(ResultAndState {
//             result:
//                 revm::primitives::ExecutionResult::Success {
//                     reason: _,
//                     gas_used: _,
//                     gas_refunded: _,
//                     logs: _,
//                     output: Output::Create(code, _),
//                 },
//             state: _,
//         }) = self.inner.transact()
//         {
//             self.deploy_contract(Address::from_slice(PREIMAGE_ORACLE_ADDR.as_slice()), code)?;
//         } else {
//             anyhow::bail!("Failed to deploy PreimageOracle contract");
//         };
//
//         // Deploy the MIPS contract prior to deploying it manually. This contract has an immutable
//         // variable, so we let the creation code fill this in for us, and then deploy it to the
//         // test address.
//         let encoded_preimage_addr =
//             Address::from_slice(PREIMAGE_ORACLE_ADDR.as_slice()).into_word();
//         let mips_creation_heap = hex::decode(MIPS_CREATION_CODE)?
//             .into_iter()
//             .chain(encoded_preimage_addr)
//             .collect::<Vec<_>>();
//         self.fill_tx_env(TransactTo::Create, mips_creation_heap.into());
//         if let Ok(ResultAndState {
//             result:
//                 revm::primitives::ExecutionResult::Success {
//                     reason: _,
//                     gas_used: _,
//                     gas_refunded: _,
//                     logs: _,
//                     output: Output::Create(code, _),
//                 },
//             state: _,
//         }) = self.inner.transact()
//         {
//             // Deploy the MIPS contract manually.
//             self.deploy_contract(Address::from_slice(MIPS_ADDR.as_slice()), code)
//         } else {
//             anyhow::bail!("Failed to deploy MIPS contract");
//         }
//     }
//
//     /// Perform a single instruction step on the MIPS smart contract from the VM state encoded
//     /// in the [StepWitness] passed.
//     ///
//     /// ### Takes
//     /// - `witness`: The [StepWitness] containing the VM state to step.
//     ///
//     /// ### Returns
//     /// - A [Result] containing the post-state hash of the MIPS VM or an error returned during
//     ///   execution.
//     pub fn step(&mut self, witness: StepWitness) -> Result<StateWitness> {
//         if witness.has_preimage() {
//             tracing::debug!(
//                 target: "mipsevm::evm",
//                 "Reading preimage key {:x} at offset {:?}",
//                 B256::from(witness.preimage_key.ok_or(anyhow::anyhow!("Missing preimage key"))?),
//                 witness.preimage_offset
//             );
//
//             let preimage_oracle_input = witness
//                 .encode_preimage_oracle_input()
//                 .ok_or(anyhow::anyhow!("Failed to ABI encode preimage oracle input."))?;
//             self.fill_tx_env(TransactTo::Call(PREIMAGE_ORACLE_ADDR.into()), preimage_oracle_input);
//             self.inner.transact_commit().map_err(|_| {
//                 anyhow::anyhow!("Failed to commit preimage to PreimageOracle contract")
//             })?;
//         }
//
//         tracing::debug!(target: "mipsevm::evm", "Performing EVM step");
//
//         let step_input = witness.encode_step_input();
//         self.fill_tx_env(TransactTo::Call(MIPS_ADDR.into()), step_input);
//         if let Ok(ResultAndState {
//             result:
//                 revm::primitives::ExecutionResult::Success {
//                     reason: _,
//                     gas_used: _,
//                     gas_refunded: _,
//                     logs,
//                     output: Output::Call(output),
//                 },
//             state: _,
//         }) = self.inner.transact()
//         {
//             let output = B256::from_slice(&output);
//
//             tracing::debug!(target: "mipsevm::evm", "EVM step successful with resulting post-state hash: {:x}", output);
//
//             if logs.len() != 1 {
//                 anyhow::bail!("Expected 1 log, got {}", logs.len());
//             }
//
//             let post_state: StateWitness = logs[0].data.data.to_vec().as_slice().try_into()?;
//
//             if state_hash(post_state).as_slice() != output.as_slice() {
//                 anyhow::bail!(
//                     "Post-state hash does not match state hash in log: {:x} != {:x}",
//                     output,
//                     B256::from(state_hash(post_state))
//                 );
//             }
//
//             Ok(post_state)
//         } else {
//             anyhow::bail!("Failed to step MIPS contract");
//         }
//     }
//
//     /// Deploys a contract with the given code at the given address.
//     ///
//     /// ### Takes
//     /// - `db`: The database backend of the MIPS EVM.
//     /// - `addr`: The address to deploy the contract to.
//     /// - `code`: The code of the contract to deploy.
//     pub(crate) fn deploy_contract(&mut self, addr: Address, code: Bytes) -> Result<()> {
//         let mut acc_info = AccountInfo {
//             balance: U256::ZERO,
//             nonce: 0,
//             code_hash: B256::ZERO,
//             code: Some(Bytecode::new_raw(code)),
//         };
//         let db = self.inner.db_mut();
//         db.insert_contract(&mut acc_info);
//         db.insert_account_info(addr, acc_info);
//         Ok(())
//     }
//
//     /// Fills the transaction environment with the given data.
//     ///
//     /// ### Takes
//     /// - `transact_to`: The transaction type.
//     /// - `data`: The calldata for the transaction.
//     /// - `to`: The address of the contract to call.
//     pub(crate) fn fill_tx_env(&mut self, transact_to: TransactTo, data: Bytes) {
//         let tx_env = self.inner.tx_mut();
//         *tx_env = TxEnv {
//             caller: Address::ZERO,
//             gas_limit: u64::MAX,
//             gas_price: U256::ZERO,
//             gas_priority_fee: None,
//             transact_to,
//             value: U256::ZERO,
//             data,
//             chain_id: None,
//             nonce: None,
//             access_list: Vec::default(),
//             blob_hashes: Vec::default(),
//             max_fee_per_blob_gas: None,
//             authorization_list: None,
//         };
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use super::*;
//     use crate::{
//         test_utils::{ClaimTestOracle, StaticOracle, BASE_ADDR_END, END_ADDR},
//         types::{Address, State},
//         utils::patch::{load_elf, patch_go, patch_stack},
//         InstrumentedState,
//     };
//     use std::{
//         fs,
//         io::{self, BufReader, BufWriter},
//     };
//
//     #[tokio::test]
//     async fn evm() {
//         let mut mips_evm = MipsEVM::new();
//         mips_evm.try_init().unwrap();
//
//         let tests_path =
//             std::env::current_dir().unwrap().join("open_mips_tests").join("test").join("bin");
//         let test_files = fs::read_dir(tests_path).unwrap().flatten();
//
//         for f in test_files.into_iter() {
//             let file_name = String::from(f.file_name().to_str().unwrap());
//             println!(" -> Running test: {file_name}");
//
//             // Short circuit early for `exit_group.bin`
//             let exit_group = file_name == "exit_group.bin";
//
//             let program_mem = fs::read(f.path()).unwrap();
//
//             let mut state = State { pc: 0, next_pc: 4, ..Default::default() };
//             state.memory.set_memory_range(0, BufReader::new(program_mem.as_slice())).unwrap();
//
//             // Set the return address ($ra) to jump into when the test completes.
//             state.registers[31] = END_ADDR;
//
//             let mut instrumented = InstrumentedState::new(
//                 state,
//                 StaticOracle::new(b"hello world".to_vec()),
//                 io::stdout(),
//                 io::stderr(),
//             );
//
//             for _ in 0..1000 {
//                 if instrumented.state.pc == END_ADDR {
//                     break;
//                 }
//                 if exit_group && instrumented.state.exited {
//                     break;
//                 }
//
//                 let instruction =
//                     instrumented.state.memory.get_memory(instrumented.state.pc as Address).unwrap();
//                 println!(
//                     "step: {} pc: 0x{:08x} insn: 0x{:08x}",
//                     instrumented.state.step, instrumented.state.pc, instruction
//                 );
//
//                 let step_witness = instrumented.step(true).await.unwrap().unwrap();
//
//                 // Verify that the post state matches
//                 let evm_post = mips_evm.step(step_witness).unwrap();
//                 let rust_post = instrumented.state.encode_witness().unwrap();
//
//                 assert_eq!(evm_post, rust_post);
//             }
//
//             if exit_group {
//                 assert_ne!(END_ADDR, instrumented.state.pc, "must not reach end");
//                 assert!(instrumented.state.exited, "must exit");
//                 assert_eq!(1, instrumented.state.exit_code, "must exit with 1");
//             } else {
//                 assert_eq!(END_ADDR, instrumented.state.pc, "must reach end");
//                 let mut state = instrumented.state.memory;
//                 let (done, result) = (
//                     state.get_memory((BASE_ADDR_END + 4) as Address).unwrap(),
//                     state.get_memory((BASE_ADDR_END + 8) as Address).unwrap(),
//                 );
//                 assert_eq!(done, 1, "must set done to 1");
//                 assert_eq!(result, 1, "must have success result {:?}", f.file_name());
//             }
//         }
//     }
//
//     #[tokio::test]
//     async fn evm_single_step() {
//         let mut mips_evm = MipsEVM::new();
//         mips_evm.try_init().unwrap();
//
//         let cases = [
//             ("j MSB set target", 0, 4, 0x0A_00_00_02),
//             ("j non-zero PC region", 0x10_00_00_00, 0x10_00_00_04, 0x08_00_00_02),
//             ("jal MSB set target", 0, 4, 0x0E_00_00_02),
//             ("jal non-zero PC region", 0x10_00_00_00, 0x10_00_00_04, 0x0C_00_00_02),
//         ];
//
//         for (name, pc, next_pc, instruction) in cases {
//             println!(" -> Running test: {name}");
//
//             let mut state = State { pc, next_pc, ..Default::default() };
//             state.memory.set_memory(pc, instruction).unwrap();
//
//             let mut instrumented = InstrumentedState::new(
//                 state,
//                 StaticOracle::new(b"hello world".to_vec()),
//                 io::stdout(),
//                 io::stderr(),
//             );
//             let step_witness = instrumented.step(true).await.unwrap().unwrap();
//
//             let evm_post = mips_evm.step(step_witness).unwrap();
//             let rust_post = instrumented.state.encode_witness().unwrap();
//
//             assert_eq!(evm_post, rust_post);
//         }
//     }
//
//     #[tokio::test]
//     async fn evm_fault() {
//         let mut mips_evm = MipsEVM::new();
//         mips_evm.try_init().unwrap();
//
//         let cases = [
//             ("illegal instruction", 0, 0xFF_FF_FF_FFu32),
//             ("branch in delay slot", 8, 0x11_02_00_03),
//             ("jump in delay slot", 8, 0x0c_00_00_0c),
//         ];
//
//         for (name, next_pc, instruction) in cases {
//             println!(" -> Running test: {name}");
//
//             let mut state = State { next_pc: next_pc as Address, ..Default::default() };
//             state.memory.set_memory(0, instruction).unwrap();
//
//             // Set the return address ($ra) to jump to when the test completes.
//             state.registers[31] = END_ADDR;
//
//             let mut instrumented = InstrumentedState::new(
//                 state,
//                 StaticOracle::new(b"hello world".to_vec()),
//                 io::stdout(),
//                 io::stderr(),
//             );
//             assert!(instrumented.step(true).await.is_err());
//
//             let mut initial_state = State {
//                 next_pc: next_pc as Address,
//                 memory: instrumented.state.memory.clone(),
//                 ..Default::default()
//             };
//             let instruction_proof = initial_state.memory.merkle_proof(0).unwrap();
//             let step_witness = StepWitness {
//                 state: initial_state.encode_witness().unwrap(),
//                 mem_proof: instruction_proof.to_vec(),
//                 preimage_key: None,
//                 preimage_value: None,
//                 preimage_offset: None,
//             };
//             assert!(mips_evm.step(step_witness).is_err());
//         }
//     }
//
//     #[tokio::test]
//     async fn test_hello_evm() {
//         let mut mips_evm = MipsEVM::new();
//         mips_evm.try_init().unwrap();
//
//         let elf_bytes = include_bytes!("../../../../example/bin/hello.elf");
//         let mut state = load_elf(elf_bytes).unwrap();
//         patch_go(elf_bytes, &mut state).unwrap();
//         patch_stack(&mut state).unwrap();
//
//         let mut instrumented =
//             InstrumentedState::new(state, StaticOracle::default(), io::stdout(), io::stderr());
//
//         for i in 0..400_000 {
//             if instrumented.state.exited {
//                 break;
//             }
//
//             if i % 1000 == 0 {
//                 let instruction =
//                     instrumented.state.memory.get_memory(instrumented.state.pc as Address).unwrap();
//                 println!(
//                     "step: {} pc: 0x{:08x} instruction: {:08x}",
//                     instrumented.state.step, instrumented.state.pc, instruction
//                 );
//             }
//
//             let step_witness = instrumented.step(true).await.unwrap().unwrap();
//
//             let evm_post = mips_evm.step(step_witness).unwrap();
//             let rust_post = instrumented.state.encode_witness().unwrap();
//             assert_eq!(evm_post, rust_post);
//         }
//
//         assert!(instrumented.state.exited, "Must complete program");
//         assert_eq!(instrumented.state.exit_code, 0, "Must exit with 0");
//     }
//
//     #[tokio::test]
//     async fn test_claim_evm() {
//         let mut mips_evm = MipsEVM::new();
//         mips_evm.try_init().unwrap();
//
//         let elf_bytes = include_bytes!("../../../../example/bin/claim.elf");
//         let mut state = load_elf(elf_bytes).unwrap();
//         patch_go(elf_bytes, &mut state).unwrap();
//         patch_stack(&mut state).unwrap();
//
//         let out_buf = BufWriter::new(Vec::default());
//         let err_buf = BufWriter::new(Vec::default());
//
//         let mut instrumented =
//             InstrumentedState::new(state, ClaimTestOracle::default(), out_buf, err_buf);
//
//         for i in 0..2_000_000 {
//             if instrumented.state.exited {
//                 break;
//             }
//
//             if i % 1000 == 0 {
//                 let instruction =
//                     instrumented.state.memory.get_memory(instrumented.state.pc as Address).unwrap();
//                 println!(
//                     "step: {} pc: 0x{:08x} instruction: {:08x}",
//                     instrumented.state.step, instrumented.state.pc, instruction
//                 );
//             }
//
//             let step_witness = instrumented.step(true).await.unwrap().unwrap();
//
//             let evm_post = mips_evm.step(step_witness).unwrap();
//             let rust_post = instrumented.state.encode_witness().unwrap();
//             assert_eq!(evm_post, rust_post);
//         }
//
//         assert!(instrumented.state.exited, "Must complete program");
//         assert_eq!(instrumented.state.exit_code, 0, "Must exit with 0");
//
//         assert_eq!(
//             String::from_utf8(instrumented.std_out.buffer().to_vec()).unwrap(),
//             format!(
//                 "computing {} * {} + {}\nclaim {} is good!\n",
//                 ClaimTestOracle::S,
//                 ClaimTestOracle::A,
//                 ClaimTestOracle::B,
//                 ClaimTestOracle::S * ClaimTestOracle::A + ClaimTestOracle::B
//             )
//         );
//         assert_eq!(String::from_utf8(instrumented.std_err.buffer().to_vec()).unwrap(), "started!");
//     }
// }

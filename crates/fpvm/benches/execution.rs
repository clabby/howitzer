use criterion::{criterion_group, criterion_main, Bencher, Criterion};
use howitzer_fpvm::{
    memory::TrieMemory,
    mips::HowitzerVM,
    test_utils::{ClaimTestOracle, StaticOracle},
    utils::patch::{load_elf, patch_go, patch_stack},
};
use kona_preimage::{HintRouter, PreimageFetcher};
use pprof::criterion::{Output, PProfProfiler};
use std::sync::Arc;
use tokio::sync::Mutex;

#[inline(always)]
fn bench_exec(
    elf_bytes: &[u8],
    oracle: impl HintRouter + PreimageFetcher,
    compute_witness: bool,
    b: &mut Bencher,
) {
    let mut state = load_elf::<TrieMemory>(elf_bytes).unwrap();
    patch_go(elf_bytes, &mut state).unwrap();
    patch_stack(&mut state).unwrap();

    let ins = Arc::new(Mutex::new(HowitzerVM::new(state, oracle)));

    let rt = tokio::runtime::Runtime::new().unwrap();
    b.to_async(rt).iter(|| async {
        let mut ins = ins.lock().await;
        loop {
            if ins.state.exited {
                break;
            }
            ins.step(compute_witness).await.unwrap();
        }
    })
}

fn execution(c: &mut Criterion) {
    let mut g = c.benchmark_group("execution");
    g.sample_size(10);

    g.bench_function("[No Witness] Execution (hello.elf)", |b| {
        let elf_bytes = include_bytes!("../../../example/bin/hello.elf");
        bench_exec(elf_bytes, StaticOracle::default(), false, b);
    });

    g.bench_function("[Witness] Execution (hello.elf)", |b| {
        let elf_bytes = include_bytes!("../../../example/bin/hello.elf");
        bench_exec(elf_bytes, StaticOracle::default(), true, b);
    });

    g.bench_function("[No Witness] Execution (claim.elf)", |b| {
        let elf_bytes = include_bytes!("../../../example/bin/claim.elf");
        bench_exec(elf_bytes, ClaimTestOracle::default(), false, b);
    });

    g.bench_function("[Witness] Execution (claim.elf)", |b| {
        let elf_bytes = include_bytes!("../../../example/bin/claim.elf");
        bench_exec(elf_bytes, ClaimTestOracle::default(), true, b);
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = execution
}
criterion_main!(benches);

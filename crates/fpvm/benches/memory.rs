use criterion::{criterion_group, criterion_main, Criterion};
use howitzer_fpvm::memory::{Memory, TrieMemory};
use pprof::criterion::{Output, PProfProfiler};
use rand::RngCore;

fn merkle_root(c: &mut Criterion) {
    let mut g = c.benchmark_group("memory");
    g.sample_size(10);

    g.bench_function("Merkle Root (memory size = 25 MB)", |b| {
        let mut memory = TrieMemory::default();
        let mut data = vec![0u8; 25_000_000];
        rand::thread_rng().fill_bytes(&mut data[..]);
        memory.set_memory_range(0, &data[..]).expect("Should not error");
        b.iter(|| {
            memory.merkleize().unwrap();
        });
    });

    g.bench_function("Merkle Root (memory size = 50 MB)", |b| {
        let mut memory = TrieMemory::default();
        let mut data = vec![0u8; 50_000_000];
        rand::thread_rng().fill_bytes(&mut data[..]);
        memory.set_memory_range(0, &data[..]).expect("Should not error");
        b.iter(|| {
            memory.merkleize().unwrap();
        });
    });

    g.bench_function("Merkle Root (memory size = 100 MB)", |b| {
        let mut memory = TrieMemory::default();
        let mut data = vec![0u8; 100_000_000];
        rand::thread_rng().fill_bytes(&mut data[..]);
        memory.set_memory_range(0, &data[..]).expect("Should not error");
        b.iter(|| {
            memory.merkleize().unwrap();
        });
    });

    g.bench_function("Merkle Root (memory size = 200 MB)", |b| {
        let mut memory = TrieMemory::default();
        let mut data = vec![0u8; 200_000_000];
        rand::thread_rng().fill_bytes(&mut data[..]);
        memory.set_memory_range(0, &data[..]).expect("Should not error");
        b.iter(|| {
            memory.merkleize().unwrap();
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(100, Output::Flamegraph(None)));
    targets = merkle_root
}
criterion_main!(benches);

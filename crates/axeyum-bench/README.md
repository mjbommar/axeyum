# axeyum-bench

Corpus and diagnostic harness for Axeyum. The main binary records backend
selection, limits, PAR-2 scoring, expected-status comparison, model replay, and
versioned JSON artifacts. The `examples/` directory contains targeted research
probes; those probes are not all stable user interfaces.

Run the committed micro corpus through the default pure-Rust BV backend:

```sh
cargo run -p axeyum-bench -- corpus/micro --backend sat-bv \
  --timeout-ms 1000 --out /tmp/axeyum-micro.json
```

See [Benchmarks](../../docs/user-guide/benchmarks.md) for result interpretation
and [Benchmark artifacts](../../docs/contributor-guide/benchmark-artifacts.md)
for reproducibility requirements.

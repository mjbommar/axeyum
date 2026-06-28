# SMT Fragment Atlas

The SMT Fragment Atlas is the planned machine-readable map of what Axeyum can
parse, solve, replay, prove, and measure.

It should become the shared source for capability documentation, benchmark
coverage, proof-route coverage, and planning status. The first version is a
small curated artifact, not a full replacement for SMT-LIB metadata or the
existing Axeyum capability matrix.

## Audience

- Solver contributors deciding which fragment to improve next.
- Proof contributors checking which certificate route applies to a fragment.
- Users deciding whether Axeyum can handle their problem shape.
- Benchmark maintainers reconciling scoreboards, dominance audits, and support
  matrices.

## Planned Artifacts

```text
docs/atlas/
  README.md
  ROADMAP.md
artifacts/ontology/
  smt-fragments.json        # planned first machine-readable atlas
  smt-fragments.schema.json # planned validation schema
```

## Roadmap

The detailed implementation plan lives in [ROADMAP.md](ROADMAP.md).

## First Useful Slice

The MVP should cover only the strongest or most strategically important rows:

- `QF_BV`
- `QF_ABV`
- `QF_UF`
- `QF_UFBV`
- `QF_LRA`
- `QF_LIA`
- `QF_DT`
- `QF_FP`
- `QF_NRA` and `QF_NIA` as honest partial/frontier rows

Each row should link to:

- [capability matrix](../research/08-planning/capability-matrix.md);
- [support matrix](../research/08-planning/support-matrix.md);
- [trust ledger](../research/08-planning/trust-ledger.md);
- [dominance scoreboard](../../bench-results/DOMINANCE.md);
- [parity path](../PARITY-STATUS-AND-PATH.md).

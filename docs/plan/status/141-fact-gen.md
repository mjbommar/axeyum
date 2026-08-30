# Lane: fact-gen — making mechanical fact registration mechanical

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, fact-gen, 2026-08-27).** Built
`scripts/gen-kernel-facts.py`: ledger-schema facts emitted for already-proved
`kernel-lean` theorems, deriving every formulaic field from
`kernel_declaration_projection`'s unfiltered eight-field emit and **refusing**
the rest. The join ("which theorem is this fact about") is imported from
`gen-ledger-coverage.py`, which imports `theorem_of` from
`check-fact-depends-derived.py` — three consumers, one definition, no fourth
copy to diverge. Registered `--audit` in `scripts/check.sh` and `justfile`
beside the existing `gen-ledger-coverage --check` step.

**Headline: the string prelude, 0/64 → 64/64, and overall coverage
474/1,397 (34%) → 538/1,397 (38.5%).** 64 planned, **0 declined**;
`validate-facts.py` green at 882 facts / 0 errors. `string` was
[297](../../autogenesis/297-ledger-coverage-gate.md)'s only genuine zero and
is now the only prelude at full coverage.

**Every emitted checker was executed, not assumed: 128 commands, 0 failed** —
all 64 facts × 2 evidence rows, not a sample. And shown able to FAIL, which is
the part that matters for a bulk generator. In an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout), renaming
`append_assoc`'s interned name and rebuilding gave `count=0 exit=1` for its
generated checker, `count=1 exit=0` for `append_nil` in the **same run against
the same binary**, and `count=1 exit=0` for `append_assoc_MUTANT` — so the
failure is the *name*, not a broken build or a lost proof. Footprint side:
`--require-axiom-free string` exits 0, `axreal` (30 axioms) exits 1, a prelude
the run never built exits 1.

Detail moved to [`../notes/141-fact-gen.md`](../notes/141-fact-gen.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | fact-gen | `scripts/gen-kernel-facts.py` + 32-test suite + `mutation_controls.py kernel-facts` (13 guards); 64 generated `string` facts (0/64 → 64/64); ledger coverage 34% → 38.5%; ADR-0607; one `KERNEL_THEOREM_RE` alternative in `validate-facts.py` |

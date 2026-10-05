## Status

Axeyum is a working research-grade reasoning stack: a pure-Rust default path,
replay-checked SAT models, several independently checked UNSAT evidence routes,
broad but uneven theory support, an independent Lean-core checker and importer,
a kernel-checked fact library, a CAS, and three external consumers. It is not
yet a drop-in Z3 replacement or a replacement for Lean.

Every number below names its source. "(not re-run)" means it was copied from
the cited file on 2026-10-05, not re-measured.

### Solver — the parity ledger

Latest entry per division by **solver commit** in
[`bench-results/PARITY.md`](bench-results/PARITY.md): all sixteen were taken on
2026-09-11, fifteen at `c1d6db6fe` against cvc5 1.3.4 (Bitwuzla 0.9.1 for QF_ABV, QF_BV and QF_FP), QF_UFLRA at
`14712b1f4` against z3 4.13.3. **0 disagreements in every division.** Axeyum /
reference on identical 200-file lists, 24 s:

| ≥ 95 % | 85–95 % | < 85 % |
|---|---|---|
| QF_UF 200/200 · QF_FP 199/200 · QF_SLIA 193/194 · QF_RDL 152/154 · UF 90/93 · QF_BV 186/194 | QF_ABV 186/197 · QF_S 186/197 · QF_IDL 113/123 · QF_UFLIA 161/180 · QF_LIA 119/139 | QF_LRA 107/145 · QF_UFLRA 142/198 · QF_NRA 117/186 · QF_DT 114/192 · QF_NIA 41/87 |

The ledger frame is old: `c1d6db6fe` is 976 commits behind `a38d5f5da`. Gains
measured after it are **not ledger entries** and are listed separately:

- **2026-09-17 board A/B** ([README](bench-results/board-ab-20260917-adr2142/README.md)):
  Axeyum alone, 16 × 200 files, `60e23fa39` decides **2,432 of 3,200** (+8 over
  its parent, 0 losses, 0 of 4,380 `:status` disagreements). Where that board
  differs most from the ledger: QF_NIA **87** (ledger 41), QF_DT **171** (114),
  QF_NRA 124 (117), QF_UFLIA 167 (161), QF_UFLRA 149 (142). No reference ran.
- **Shipped after that board** (ADR A/Bs, pinned lists;
  [coordinator record](docs/plan/archive/lanes/coordinator-three-repos-2026-09-16.md)):
  QF_LRA 107 → 113 ([ADR-2147](docs/research/09-decisions/adr-2147-a-violated-disequality-is-a-case-split-not-an-unknown.md)),
  QF_UFLRA 148 → 150, UFNIA 54 → 61
  ([ADR-2148](docs/research/09-decisions/adr-2148-nia-lemmas-versus-slice-versus-iteration.md)).
- The five weakest divisions each have a mechanism named at `file:line`
  ([stock-take, 2026-09-16](docs/plan/five-divisions-stock-take-2026-09-16.md)).

### Library, CAS, Lean

- **Facts** (counted 2026-10-05 over `artifacts/facts/*.json`): **2,971** —
  proved 2,692 · open 267 · computed 5 · refuted 4 · conjectured 3.
- **Trusted surface** (`docs/plan/lean-axiom-ledger-v1.json`, population as of
  2026-08-17, not re-run — `gen-lean-axiom-ledger.py --check` builds Rust):
  30 declared axioms, all in the `axreal` package; every other prelude 0.
  **Declared is not reached**
  ([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)):
  both are published, and the 30 are reached by no shipped route — the package
  is kept as the negative control those measurements are read against.
- **CAS** (`scripts/check-cas-trust-registry.py`, run 2026-10-05): 1,280 public
  functions — 151 certified, 110 checker, 1,019 uncertified; floor 151 held.
- **Lean replay** ([ADR-1661](docs/research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md),
  2026-09-10, not re-run): of 4,478 proved declarations pinned Lean accepts
  4,394; 50 are `Type`-valued theorems Lean refuses; 34 are blocked behind them.
  What "Lean compatible" means is fixed in
  [`14-lean-lang.md`](docs/math-department/14-lean-lang.md) (ADR-1668).

### Evidence

- **QF_BV certification** (`PARITY.md` evidence entry, 2026-08-17,
  `c799be2f7`, not re-run): 93/130 UNSAT certified (71.5 %), 79/130 re-checked
  from serialized text alone, 0 certificates failed. The other 37 are bare UNSAT.
- **SAT engine**: the native core is the only engine
  ([ADR-1908](docs/research/09-decisions/adr-1908-the-native-core-is-the-one-cdclt-driver-cdclt-is-demoted-to-an-oracle.md));
  BatSat is removed and the referee is an external CaDiCaL/Kissat binary on
  our DIMACS text
  ([ADR-1910](docs/research/09-decisions/adr-1910-the-sat-referee-is-an-external-binary-reading-dimacs-text-and-batsat-is-removed.md)).

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|
<!-- plan-generated: landed-changes -->

Rows come from active lane files; with none active the table is empty. The
2026-09-17 results above are the last landings.

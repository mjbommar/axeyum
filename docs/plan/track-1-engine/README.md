# Track 1 — Engine & Performance

Make axeyum a *real* solver: a fast bit-blasted QF_BV path competitive with Z3,
and the shared engine infrastructure (e-graph + CDCL(T) loop) that the theories
in [Track 2](../track-2-theories/README.md) need. This track owns the **first
load-bearing front (measured performance)** and **both engineering keystones**.

Reference reading: [`../references/z3-core.md`](../references/z3-core.md),
[`../references/bitwuzla-and-sat.md`](../references/bitwuzla-and-sat.md).

## Phases

| Phase | Title | Size | Depends on | Theme |
|---|---|---|---|---|
| [P1.1](P1.1-sat-inprocessing.md) | SAT inprocessing | L | P4.5 (measure) | subsumption → **BVE** → vivification, glue tiers |
| [P1.2](P1.2-preprocessing.md) | Preprocessing | L | P4.5 | word-level rewrite, solve_eqs, bv_slice/bounds/max-sharing, AIG 2-level rewrite |
| [P1.3](P1.3-sat-core-modernization.md) | SAT-core modernization | M–L | P1.1 | VSIDS/VMTF modes, EMA/Luby restarts, arena+packed watches, chrono BT |
| [P1.4](P1.4-egraph.md) | Incremental e-graph **[keystone]** | L | — | congruence closure + explanation + independent checker |
| [P1.5](P1.5-cdcl-t-loop.md) | CDCL(T) loop **[keystone]** | L | P1.4 | theory-as-extension, final-check, theory propagation |
| [P1.6](P1.6-theory-combination.md) | Theory combination | M | P1.4, P1.5 | th_eq bus, interface equalities (Nelson–Oppen) |
| [P1.7](P1.7-pbls-engine.md) | PBLS local-search BV engine | L | — | portfolio for hard satisfiable QF_BV |
| [P1.8](P1.8-strategy-tactics.md) | Strategy & tactics | M | — | combinators + probes + per-logic scripts |

## Sequencing within the track

1. **P4.5 first** (in Track 4) — no performance phase is "done" without the
   measured Z3 head-to-head.
2. **P1.2 + P1.1 in parallel** — preprocessing shrinks the problem feeding the SAT
   core (lower risk, easier to measure), BVE is the single biggest SAT-side win.
   Re-measure after each change.
3. **P1.3** once P1.1 has landed the high-value inprocessing.
4. **P1.4 → P1.5 → P1.6** — the keystone chain; build it once, then Track 2
   theories migrate onto it.
5. **P1.7** (PBLS) and **P1.8** (strategy) any time; P1.7 is the top new-capability
   candidate after the inprocessing/preprocessing wins.

## The performance discipline

Per the project methodology gate and [P4.5](../track-4-usecases-frontend/P4.5-benchmarking.md):
change **one** thing, re-run the committed slice against Z3, record PAR-2 and the
sat/unsat/unknown split in `bench-results/` and STATUS.md. Encodings/preprocessing
come before SAT-core micro-tuning. Never sweep the 41GB corpus; measure on the
committed slice.

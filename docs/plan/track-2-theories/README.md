# Track 2 — Theories & Breadth

Bring each theory to Z3 feature/behavior parity. The recurring upgrade is
**eager/one-shot reduction → lazy, e-graph-integrated** decision procedure on the
[CDCL(T) loop](../track-1-engine/P1.5-cdcl-t-loop.md). Most phases here depend on
the Track 1 keystones ([e-graph P1.4](../track-1-engine/P1.4-egraph.md),
[CDCL(T) P1.5](../track-1-engine/P1.5-cdcl-t-loop.md)); the independent ones
(LIA cuts, NRA/CAD, FP polish) can proceed any time.

Reference reading: [`../references/z3-theories.md`](../references/z3-theories.md).

## Phases

| Phase | Title | Size | Depends on | Note |
|---|---|---|---|---|
| [P2.1](P2.1-bv-lazy.md) | BV lazy blasting + word-level slicing + theory-checker | M | P1.4, P1.5 | foundation already strong |
| [P2.2](P2.2-arrays-lazy.md) | Arrays: lazy ROW axioms + extensionality + func_interp models | L | P1.4, P1.5 | biggest array scalability win |
| [P2.3](P2.3-euf.md) | EUF on the e-graph (from Ackermann to incremental) | M | P1.4, P1.5 | first theory on the loop |
| [P2.4](P2.4-lia-cuts.md) | LIA cut portfolio (GCD, Gomory, HNF, cube, Diophantine) | M–L | — | independent; high single-theory value |
| [P2.5](P2.5-nra-cad.md) | Nonlinear arithmetic: incr. linearization → ICP → NLSAT/CAC (+NIA) | XL | — | independent; the hard completeness gap — **expanded sub-program** [`P2.5-nra/`](P2.5-nra/) |
| [P2.6](P2.6-quantifiers.md) | Quantifiers (MAM e-matching, triggers, MBQI, QE/MBP) | L–XL | P1.4, P1.5 | e-matching walks the e-graph |
| [P2.7](P2.7-strings.md) | Strings (unbounded, length-aware, full `str.*`, regex) | L–XL | P1.6 (BV+LIA), P2.6 | needs combination + quantifier-ish reasoning — **expanded sub-program** [`P2.7-strings/`](P2.7-strings/) |
| [P2.8](P2.8-fp-polish.md) | FP polish (unspecified values, min/max ±0, lazy conversion) | S–M | — | already near parity |
| [P2.9](P2.9-datatypes-lazy.md) | Datatypes lazy (e-graph splitting + occurs-check) | M | P1.4, P1.5 | lower priority |
| [P2.10](P2.10-breadth-backlog.md) | Breadth backlog (sequences, sets/bags, sep logic, finite fields, co-datatypes, rec-fun, NIA gap) | per-item M–XL | P1.4, P1.5 | enumerated; the remaining theory *columns* Z3/cvc5 have and we don't |

## Order
After the Track 1 keystones land: **P2.3 (EUF)** first (it is the first
`TheorySolver` and validates the loop), then **P2.2 (lazy arrays)** and **P2.1
(lazy BV)**, then **P2.9 (datatypes)**. **P2.4 (LIA cuts)** and **P2.8 (FP)** any
time. **P2.6 (quantifiers)** after the e-graph. **P2.5 (nonlinear)** and **P2.7
(full strings)** are the multi-month frontiers — each is decomposed into a
full top-down sub-program (current state → literature survey → architecture →
phased build → evaluation) under [`P2.5-nra/`](P2.5-nra/) and
[`P2.7-strings/`](P2.7-strings/). **P2.10 (breadth backlog)** is
the enumerated tail — items there start only behind the keystones and behind the
fragments above, but the file keeps them *counted* so "feature coverage" is a
list, not a guess.

Every new `unsat` route gets either an independent checker or a
[trust-ledger](../track-3-proof-lean/P3.0-trust-ledger.md) entry, and ideally an
Alethe reduction proof ([P3.5](../track-3-proof-lean/P3.5-reduction-proofs.md)).

# S11a measured: the UF/QF_UF Ackermann cap blocks three files, not seventy

Date: 2026-09-06. Lane `s11a-uf-ackermann-cap`.
Inputs: [parity loss census](2026-09-05-parity-loss-census.md),
`bench-results/parity-losses-20260905/{QF_UF,UF}.census.tsv`,
`docs/plan/smt-parity-plan-2026-09-05.md` §2.5 and §4 row S11.
Artifacts: `bench-results/s11a-uf-ackermann-20260906/`.

## What the census said, and why it was wrong about the cause

The census classified all 70 reference-only files in QF_UF (38) and UF (32) as
`admission-decline` on a congruence-pair bound: 35 QF_UF on "eager Ackermann
elimination would emit N congruence constraints", 3 QF_UF + all 32 UF on
"declared-sort lazy CEGAR refuses N congruence pairs (bound 64)". The plan
recorded the conclusion literally: *"Neither division has a single
search-timeout file; 2.1's fix lands nothing here."*

That reading has two independent defects, both of which this lane measured.

**First, the census's `class` is the message of the LAST route in the trace,
and on this family the last route is a millisecond-scale tail after the budget
is already gone.** `explain_corpus --json --timed-trace` on the QF_UF files:

```
probe                    probe       9.6ms  fragment {uf}
dl-online                declined  516.4ms
euf-online               declined  23513.6ms  timeout in the online CDCL(T) QF_UF driver
qf-bv                    declined   14.6ms   eager Ackermann ... 14629 congruence constraints ... bound 64
```

`euf-online` is entered first and spends 23.5 s of a 24 s budget. The Ackermann
decline that named the class costs 14.6 ms and could not have been avoided by
any cap: the query has 14 629 pairs and eager expansion was never viable.

**Second, `explain_corpus` is not the front door.** It runs
`check_auto_explained` on the flat assertion view; its own banner records that
it disagrees with `solve_smtlib` on 134 of 397 committed benchmarks. The UF
division is entirely inside that disagreement. Re-measured through
`uf_unknown_probe` (which *is* `solve_smtlib`), `taskset -c 0-7`, 24 s, all 32
UF files:

| Front-door terminal reason | Files |
|---|---:|
| `Incomplete: query has quantifiers instantiation does not reach (nested, existential, or non-top-level)` | 23 |
| `ResourceLimit: quantified solve time budget exhausted after e-matching` | 7 |
| `Incomplete: instantiation is satisfiable; the universal may still be violated` | 2 |
| reached the declared-sort CEGAR bound | **0** |

The quantified ladder (`egraph-seg` / `match-seg` / `nested-quant` /
`uf-fmf-probe`, visible under `AXEYUM_QTRACE=1`) is what these files run and
what they die in. The 64-pair bound is not on their path.

## Why the routing lever the census named was already shipped

`dispatch_uf_fast_paths` (`crates/axeyum-solver/src/auto.rs`) orders the UF
ladder `uf-arith-lazy-overbound` → **`euf-online`** → `dispatch_ufbv_online` →
`euf-offline` → eager Ackermann (`qf-bv`). The online e-graph already runs
before the eager expansion, and `MAX_ACKERMANN_CONGRUENCE_PAIRS` already gates
only the eager fallback. `check_qf_uf_online_cdclt` carries **no admission
constant of its own** — it declines only on "no equality atoms", "boolean
skeleton outside the encoder", "timeout in the driver", and "model did not
replay". There was nothing to raise and nothing to reorder.

## The QF_UF baseline moved under the census

Re-run of all 38 QF_UF census files through the front door on today's main:

| Verdict | Files |
|---|---:|
| `unsat` | 24 |
| `sat` | 2 |
| `unknown` | 12 |

26 of the 38 "reference-only" files now decide. Of the 12 that do not, **9 are
`kind=Timeout`** and 3 are the CEGAR-bound declines. So the plan's "no
search-timeout file here" is the opposite of what the front door reports, and
S1's propagation work is the lever for the largest remaining QF_UF group.

## The three files the cap does block, and what admitting them costs

| File | pairs | before | after |
|---|---:|---|---|
| `QF_UF_Heap_ab_cti_max.smt2` | 68 | `unknown` @ 214 ms | `sat` @ 422 ms |
| `QF_UF_cambridge.7.prop2_ab_fp_max.smt2` | 1 009 | `unknown` @ 1 613 ms | `sat` @ 8 421 ms |
| `QF_UF_hanoi.3.prop1_ab_br_max.smt2` | 8 425 | `unknown` @ 2 620 ms | `sat` @ 8 717 ms |

All three are declared `sat`. All three converge well inside a 24 s budget. The
"before" column is the shape that matters: the route gave up after 214 ms of a
24 s budget and *nothing ran after it* — the budget was discarded, not spent.

Two changes were needed together, because either alone moves nothing.

**(a) A replay-confirmed `sat` is no longer discarded.** `check_qf_ufbv_lazy`
returned `Sat` only out of `project_replay_build`, which evaluates every
ORIGINAL assertion under the projected model through the ground evaluator and
declines on any non-`true` or indeterminate outcome — and the model it replays
is the lifted one, keyed by the original symbols. The route then threw that
`Sat` away unconditionally with "satisfiability does not transfer back because
the model interprets the encoding, not the original sort". Measured, the
premise is false for the queries that reach it: all three replay clean. Keeping
them is sound for the ordinary reason — an uninterpreted sort has no semantics
beyond equality and non-emptiness, so the bit-vector values are a legitimate
interpretation, and replay is what certifies that two symbols the query needs
distinct did not collide.

**(b) The pair bound is now a parameter, not a constant.** Every measured
failure recorded at the bound's check site is budget theft from an *enclosing*
search — the e-matching driver's rounds, the sledgehammer unsats it flipped.
`dispatch_declared_sort_ufbv_lazy` is the *terminal* rung of the
quantifier-free ladder: `euf-online`, `dispatch_ufbv_online` and `euf-offline`
have all declined above it and nothing runs after it, so there is no enclosing
search to protect. It now passes `DECLARED_SORT_CEGAR_PAIRS_TERMINAL_RUNG`
(16 384 — the same 1.6x-style margin over the newly measured deciding frontier
of 8 425 that `64` was over the then-measured 40, and well below the
44 537 – 1 549 516 range in which the original measurement found the refinement
not converging). The public `check_qf_ufbv_lazy` keeps `64` unchanged.

This is not a cap raised to buy breadth with time. The time is time the ladder
currently throws away, and the loop's own shared deadline — not the pair
count — is what bounds it. The count survives as the memory bound on the
`O(pairs)` preseed scan and lemma pool.

## Interleaved before/after on the 38 QF_UF census files

Both binaries on each file back to back so the arms share the machine load;
`taskset -c 0-7`, 24 s, front door.

| | before | after |
|---|---:|---:|
| decided | 27 | 29 |
| PAR-2 (s) | 798.2 | 690.8 |

Gained exactly the three files the cap blocks, all `sat`, all matching
`declared`. Verdict flips: 0. Verdicts contradicting `declared`, either arm: 0.
One apparent loss (`iso_brn_repgen004.smt2`) is 24 s-boundary noise in the
*before* binary — `sat` at 23 529 ms here, `Timeout` at 24 031 ms in an earlier
before arm of the same build.

**Not measured, and required before this change is validated:** the full
200-file `bench-results/parity-lists/{QF_UF,UF}.txt` sweeps through both arms,
which is what would show the 162 QF_UF and 85 UF already-decided files keeping
their route and their evidence. The 38-file sweep covers the losses, not the
population at risk.

## What this leaves for S11b

- **UF (32 files): quantifier reach, not finite-model finding.** 23 of 32 end
  at "quantifiers instantiation does not reach (nested, existential, or
  non-top-level)". A bounded finite-model-finding extension, which §2.5 names
  as the UF lever, does not address a query the instantiation engine never
  reaches. The lever is nested/existential/non-top-level trigger coverage.
  7 more are e-matching budget exhaustion (an S1/S2 shape). Only 2 are the
  "instantiation is satisfiable" shape a model finder would take.
- **QF_UF (9 files): `euf-online` search power.** All 9 spend the whole budget
  inside the online CDCL(T) QF_UF driver. That is S1/S2 territory, not S11.
- **`uf-fmf-probe` is expensive on quantified files** — 1.5 s, 8.1 s and 17.1 s
  of a 24 s budget on three of the five UF files traced, all declining. Worth a
  measurement of its own before the UF budget is re-divided.

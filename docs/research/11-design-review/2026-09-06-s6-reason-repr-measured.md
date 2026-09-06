# S6 measured: the native core's reason representation, alone

Date: 2026-09-06
Lane: `s6-native-reason-repr`
Subject: [`crates/axeyum-cnf/src/proof_sat.rs`](../../../crates/axeyum-cnf/src/proof_sat.rs)
Slice: S6 of the
[SMT parity plan](../../plan/smt-parity-plan-2026-09-05.md) §4 — the
prerequisite for S7.

## What changed

`reason[v]` was `Option<CRef>` — an arena clause, or a decision. The slice-2
design memo
([§4.4 (ii)](../../plan/adr-1701-slice-2-design-2026-09-05.md)) named a third
case the theory layer needs and called it "the unmeasured cost of slice 2".
This lane made it a packed one-word `Reason`:

```rust
Reason { Decision, Clause(CRef), Theory(ExplanationId) }   // 8 bytes
```

`analyze`, `lit_redundant` and `analyze_final` resolve a `Theory` reason by
asking the theory for its clause, installing it in the arena as an **input**
clause (ADR-1704) and rewriting the reason in place, then continuing as if it
had always been a clause reason. `theory_round` now acts on theory
*propagations*; theory *conflicts* and dynamic atom registration are still
declined with the undecided `Interrupted`, because those need the conflict half
of ADR-1704's two-stream artifact, which is S7.

Measured with **no theory attached**: every shipping entry point constructs
with `NullTheory`, which never propagates, so no `Reason::theory` is ever
created and the lemma list stays empty.

## Result 1: per-variable memory went DOWN

| representation | size |
|---|---:|
| `Option<CRef>` (before) | 16 bytes |
| `enum Reason { Decision, Clause(CRef), Theory(ExplanationId) }` (naive) | 16 bytes |
| packed `Reason` (landed) | **8 bytes** |

`usize` has no niche, so the `Option` discriminant cost a whole extra word and
the naive three-variant enum costs the same. The two-bit tag packing carries
one more case in half the space.

Pinned by `tests::reason_is_one_word_and_no_wider_than_the_option_it_replaced`,
which compares against `size_of::<Option<usize>>()` rather than against a
literal, so it measures the compiler and not the author's memory.

## Result 2: the DRAT stream is byte-identical

New instrument:
[`crates/axeyum-cnf/examples/drat_stream_dump.rs`](../../../crates/axeyum-cnf/examples/drat_stream_dump.rs).
It prints the exact proof text for the DIMACS files it is given plus a seeded
random 3-SAT family generated in-process (splitmix64, 5 sizes × 6 repeats at
the 4.26 threshold ratio), so the second half of the corpus needs no committed
files and is identical in any checkout of any commit.

A verdict comparison would have been far too weak here: `analyze` and
`lit_redundant` decide *which* literals survive minimization, so a defect there
changes the learned clauses — and therefore the proof — while leaving every
verdict intact.

Corpus `corpus/micro-cnf/*.cnf` + the 30 generated instances = 33 instances,
10 unsat / 23 sat, 38,333 bytes of proof text (PHP(7,6) alone is 23,989):

```
BEFORE (merge-base 287ca85c0)  sha256 09704208…f731459a
AFTER  (dfbb2e691)             sha256 09704208…f731459a     identical
```

**Teeth check on the instrument**, in a `lane-snapshot.sh` copy, never the
shared tree: a one-line mutation making `lit_redundant` always return `false`
(no minimization) moved the same dump from 38,333 to 47,904 bytes, and `cmp`
reported a difference at byte 62. Mutation reverted, baseline re-confirmed
byte-identical. So "identical" here is not two empty files comparing equal.

## Result 3: about +3% on the PHP microbenchmark, and the null control that says so

Host s4 (i5-12600K, hybrid P/E), `taskset -c 0-7`, prebuilt release binaries
(never through `cargo-serialized.sh`, which holds a host-wide flock and would
have made the timing measure the queue), 20 interleaved BEFORE/AFTER pairs per
row.

| comparison | paired median | second slower in | min-of-20 | median-of-20 |
|---|---:|---:|---:|---:|
| **null control** — merge-base built twice, second build perturbed in code *layout* only | **−0.4%** | 9/20 | +2.0% | +1.1% |
| S6 as landed | +2.8% | 16/20 | +3.9% | +1.9% |
| S6 + `theory_round` inline split | +3.0% | 20/20 | +2.0% | +3.4% |
| S6 + cold `resolve_reason` | +3.4% | 15/20 | +5.2% | +4.2% |
| S6 + `&self` re-probe for `lit_redundant` | +3.5% | 19/20 | +4.3% | +1.9% |

The null control is the load-bearing row. It is the **same source**, built
twice, with `#[inline(never)]` added to `analyze_final` in the second build — a
change that alters where the compiler puts things and nothing else; the two
builds produce identical verdicts and identical proofs. It still measured
min-of-20 at +2.0%.

**So min-of-N is not a usable statistic on this box: it carries about 2% of
pure code-layout noise.** The paired median is usable, and by it the null
control is −0.4% at 9/20 while every S6 variant is +2.8% to +3.5% at 15–20/20.
The ~3% is real.

Machine reference frame: load average 12–26 on a 16-thread box throughout,
from other lanes' `axeyum_cas` and `axeyum_fp` suites at 300–500% CPU each.
Within-arm spread reached 30–50%, which is why every row above is a paired
design.

### What the +3% is NOT

Three hypotheses were built and measured, and all three are refuted by the
table:

1. **`theory_round` stopped being inlined.** Its body grew a propagation loop,
   so `NullTheory`'s early return could have become a real call returning a
   large enum by `sret` per iteration. Splitting it into an
   `#[inline(always)]` gate plus a body did not move the number.
2. **`resolve_reason`/`install_theory_lemma` bloated the hot loops.** Making
   both `#[cold] #[inline(never)]` did not move the number.
3. **`lit_redundant`'s `&mut self` receiver stopped LLVM hoisting the arena,
   header, level and reason base pointers out of the minimization walk** —
   because the cold `resolve_reason` call can grow the arena, so those
   pointers would have to be reloaded each iteration. A variant keeping
   `lit_redundant` at `&self`, returning a three-way
   `Redundant / Keep / Unresolved(var)` and letting `minimize` resolve and
   re-probe, was written, tested and measured. **No difference.** It was
   **reverted**: complexity justified by a false attribution does not belong
   in the tree.

The first two are kept anyway — the shape is right and neither costs
anything — but the commit and the code comments say they are structural, not
measured wins. The cause of the remaining ~3% is **not attributed**, and the
next lane should not inherit a guess. The cheapest unrun experiment is to
apply *only* the type change to the merge-base (packed `Reason`, `enqueue`,
`is_decision`, `as_clause`) with none of the theory plumbing, and measure that
alone; if it also shows +3%, the cost is intrinsic to the representation
(which would be surprising, since it is strictly smaller), and if it shows 0%
the cost is somewhere in the `theory_round` / lemma-installation plumbing that
`NullTheory` never executes.

## Result 4: p4dfa is unchanged

The 20 p4dfa CNFs the slice-2 spike lane dumped, at a 20 s per-file budget,
through `crates/axeyum-cnf/examples/native_core_sweep.rs`, `taskset -c 0-7`:

| | BEFORE | AFTER |
|---|---:|---:|
| decided | 9 / 20 | **9 / 20** |
| verdict changed on any file | — | **none** |
| total wall | 262,261 ms | 258,452 ms (**−1.45%**) |

Reference frame: load average 22 at the start of **both** sweeps, falling to
8.7 during the AFTER one. The AFTER arm therefore ran on a quieter machine and
the *sign* of −1.45% is not significant. The reportable result is the bar the
plan set: **total time within 3%, decided count unchanged, no verdict moved.**

Per-file, the seven files that finish move between −25.9% and +2.4% and the
eleven that exhaust the budget move within ±2.2% — i.e. the movement is on the
short-running files, where a 20 s budget makes a few hundred milliseconds a
large percentage, and is not visible on the search-bound ones.

## Result 5: the theory path is exercised, and the two-stream contract holds

Requirement 3 of the slice: a mock theory that hands back a clause on demand.
`LazyImplyingTheory` in `proof_sat.rs`'s `theory_hooks` test module encodes one
implication the CNF does not contain, `¬x1 → x3`, and hands back `(x3 ∨ x1)`
only when asked.

The fixture is deliberately **Boolean-satisfiable** and unsatisfiable only with
that implication, so the search's whole path past the first conflict depends on
the lemma being installed, and the emitted stream cannot be a refutation of the
CNF alone. Measured, both directions:

```
check_drat(cnf ++ lemmas, stream) == Ok(true)      # a checkable refutation
check_drat(cnf,           stream) != Ok(true)      # and NOT of the bare CNF
extended.len() - cnf.len() == lemmas.len() == 1    # ADR-1704 §1's subtraction
theory.explains == 1                                # the lazy channel is lazy
```

The lemma is registered with `learned[cid] = false`. That is ADR-1704's
classification — a theory lemma extends the *input* formula — and it
simultaneously discharges the soundness obligation the slice-2 memo §4.5 names
("a theory reason clause must be locked exactly as `is_locked` locks a
propagation reason, or `reduce_db` can delete the justification of an assigned
literal"). `reduce_db` only ever considers clauses with `learned[cid]`, so a
theory reason clause is not a deletion candidate at all; the `is_locked`
protection is not relied on.

**Mutation, in a `lane-snapshot.sh` copy of the landed commit:** make a lazy
theory reason be enqueued as a `Decision`
(`TheoryExplanation::Lazy(_) => Reason::DECISION`). Baseline 51/51 →
**47 passed, 4 failed**, and the four are exactly the theory-reason tests:

- `a_lazy_theory_reason_is_resolved_into_an_input_clause_and_analysis_continues`
- `the_boolean_stream_checks_over_the_extended_formula_and_not_over_the_cnf`
- `the_theory_lemma_count_is_read_off_the_artifact_not_asserted`
- `an_explanation_is_resolved_at_most_once_per_assignment`

The other 47 are untouched, which is the right shape: the mutation is on the
theory path only, and the `Clause`/`Decision` behaviour it does not reach must
not move. Mutation reverted, baseline re-confirmed at 51/51.

## What S7 inherits

- A `Theory` reason case that exists, is exercised, and costs no per-variable
  memory.
- The ADR-1704 lemma stream (`Cdcl::theory_lemmas`) populated by construction
  rather than by a producer's assertion, with a test that reads the count off
  the artifact.
- Three things still declined with `Interrupted`, each with a test that says
  so: a theory conflict from `assert`, a propagation onto a falsified literal,
  and dynamic atom registration.
- An unattributed ~3% on `proof_sat_solve_php_6_7`, three refuted hypotheses,
  and the one experiment that would settle it (above).
- A reusable byte-identity instrument, with its own teeth check.

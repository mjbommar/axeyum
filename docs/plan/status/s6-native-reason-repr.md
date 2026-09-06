# Lane: s6-native-reason-repr — the reason is one word, carries a theory case, and got smaller

<!-- plan-section: lane-status -->

**S6 of the [SMT/SAT parity plan](../smt-parity-plan-2026-09-05.md) landed: the
native core's `reason[v]` is a packed one-word `Reason { Decision, Clause(CRef),
Theory(ExplanationId) }`, the theory case is resolved lazily into an ADR-1704
input clause, the DRAT stream is byte-identical to the merge-base, and p4dfa's
decided count is unchanged** (`DONE`, s6-native-reason-repr, 2026-09-06).

Commits `521b4405a`, `905ca6b1c`, `dfbb2e691`, and this one. Full measurement:
[the S6 note](../../research/11-design-review/2026-09-06-s6-reason-repr-measured.md).

## What landed

1. **`Reason` is one word — and per-variable memory went DOWN, not up.**
   `Option<CRef>` is 16 bytes (`usize` has no niche) and so is the naive
   three-variant enum; the two-bit tag packing is **8 bytes** and carries one
   more case. `tests::reason_is_one_word_and_no_wider_than_the_option_it_replaced`
   compares against `size_of::<Option<usize>>()`, not against a literal.
2. **`analyze`, `lit_redundant` and `analyze_final` resolve a `Theory`
   reason** by asking the theory for its clause, installing it in the arena as
   an **input** clause and rewriting the reason in place — so one handle is
   resolved at most once per assignment and the search never pays for an
   explanation it does not resolve against. That is the saving the lazy channel
   exists for.
3. **The lemma is registered `learned[cid] = false`.** That is ADR-1704's
   classification and it discharges the slice-2 memo §4.5 soundness obligation
   *by construction* rather than by a lock: `reduce_db` only ever considers
   learned clauses, so a theory reason clause is never a deletion candidate.
   Nothing is emitted to the DRAT sink for it — a lemma is an input clause, not
   a derived step.
4. **`theory_round` acts on theory propagations** (lazy → `Reason::theory`,
   eager → materialised now) and returns a three-way `TheoryRound` so a theory
   implication reaches Boolean fixpoint like any other. Theory *conflicts* —
   from `assert`, from a propagation onto a falsified literal, and from
   `final_check` — and dynamic atom registration are still **declined** with the
   undecided `Interrupted`; each has a test that says so.
5. **`crates/axeyum-cnf/examples/drat_stream_dump.rs`**, a reusable byte-identity
   instrument: the exact proof text for the DIMACS given plus a seeded random
   3-SAT family generated in-process, so two builds are compared with `cmp`.

No shipping entry point is affected: they all construct with `NullTheory`, which
never propagates, so no `Reason::theory` is ever created and the lemma list is
empty.

## Measured

| measurement | before | after |
|---|---|---|
| `size_of::<Reason>()` vs `size_of::<Option<CRef>>()` | 16 B | **8 B** |
| DRAT text, 33 instances (10 unsat), 38,333 bytes | sha256 `09704208…` | **identical** |
| p4dfa 20 CNFs @ 20 s — decided | 9 / 20 | **9 / 20**, no verdict changed |
| p4dfa 20 CNFs @ 20 s — total wall | 262,261 ms | 258,452 ms (**−1.45%**) |
| criterion `proof_sat_solve_php_6_7`, 20 paired runs | — | **+3% paired median** |

The p4dfa −1.45% sign is **not** significant: load average was 22 at the start
of both sweeps and fell to 8.7 during the AFTER one. The reportable result is
the bar the plan set — within 3%, decided unchanged.

## The +3% is real, and it is not attributed

A **null control** settles the statistics: the merge-base source built twice,
the second build perturbed in code *layout* only (`#[inline(never)]` on
`analyze_final` — identical verdicts, identical proof), measured the same way.

| comparison | paired median | second slower in | min-of-20 |
|---|---:|---:|---:|
| null control (same source, layout perturbed) | **−0.4%** | 9/20 | +2.0% |
| S6, four variants built and measured | +2.8% … +3.5% | 15–20/20 | +2.0% … +5.2% |

So **min-of-N carries about 2% of pure layout noise on this box** and is not a
usable statistic; the paired median is, and by it the ~3% is above the control.

Three hypotheses were built and refuted: `theory_round` losing its inline (a
gate/body split did not move it), `resolve_reason`/`install_theory_lemma`
bloating the hot loops (`#[cold] #[inline(never)]` did not move it), and
`lit_redundant`'s `&mut self` receiver blocking pointer hoisting (a `&self`
re-probe design was written, tested and **reverted** — complexity justified by a
false attribution does not belong in the tree). The first two are kept because
the shape is right, and the commit says they are structural, not measured wins.

**The cheapest unrun experiment**, for whoever picks this up: apply *only* the
type change to the merge-base (packed `Reason`, `enqueue`, `is_decision`,
`as_clause`) with none of the theory plumbing, and measure that alone.

## Mutation controls

| mutation | effect |
|---|---|
| a lazy `Theory` reason is enqueued as a `Decision` (`TheoryExplanation::Lazy(_) => Reason::DECISION`) | 51/51 → **47 passed, 4 failed**, and the four are exactly the theory-reason tests; the 47 the mutation cannot reach do not move |
| `lit_redundant` always returns `false` (no minimization) — the teeth check on the byte-identity instrument | DRAT dump 38,333 → **47,904 bytes**, `cmp` differs at byte 62 |

Both applied in `lane-snapshot.sh` copies, never the shared tree; both reverted
and the baseline re-confirmed (51/51 and byte-identical respectively).

## Gates

`test -p axeyum-cnf` **534 passed** · `test -p axeyum-cnf --features
batsat-reference` **546 passed**, including the native-vs-BatSat differential at
a **nonzero 3** (it collects 0 without the feature) · `test -p axeyum-solver
--lib --features full --test-threads=8` · `test -p axeyum-solver --features full
--test corpus_regression` · `check --workspace --all-targets` · `clippy -p
axeyum-cnf --all-targets --all-features -D warnings` · wasm32 build ·
`check-links.sh`.

## Not done

- The ~3% on `proof_sat_solve_php_6_7` is measured and **not attributed**. The
  next lane should run the isolation experiment above rather than inherit a
  guess.
- Theory conflicts and dynamic atom registration remain declined
  (`Interrupted`). Both need the conflict half of ADR-1704's two-stream
  artifact, which is S7, and both are pinned by a test so neither can be
  silently ignored.
- `Cdcl::theory_lemmas` is read by tests only; carrying it out through
  `ProofSolveOutcome` to the evidence front door is S7's plumbing, and there is
  no public entry point that could produce a non-empty one today.

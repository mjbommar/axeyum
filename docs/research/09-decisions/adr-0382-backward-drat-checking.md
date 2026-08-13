# ADR-0382: Backward (core-first) DRAT checking

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

`check_drat` (`crates/axeyum-cnf/src/drat.rs`, ADR-0011) is the trusted
component that discharges `unsat`: it walks a DRAT proof forward and
verifies that every added clause is RUP or RAT with respect to the clause
set accumulated so far. It is deliberately tiny — a few dozen lines with no
data structure more exotic than a `Vec` of clauses and a `HashMap`
assignment — because the whole trust story for a checked refutation is that
a person can read it.

It does not scale in *time*. Each step re-scans the entire live clause
database, repeatedly, until unit propagation reaches a fixpoint, so the cost
of checking grows superlinearly in the proof length. Measured this session
on a single instance of 35,858 clauses (release build):

| proof length | `check_drat` |
|---|---|
| 1,674 steps | 2.3 s |
| 38,015 steps | 200.6 s |
| 145,836 steps | 1,031.6 s |
| ~1.2M steps | unfinished after 30 minutes |

On the same cells, *solving* was 470–670× faster than *checking*. That
inverts the entire premise of this workspace — "untrusted fast search,
trusted small checking" — and it is the binding constraint on which
mathematical results can be published with full certification: a result the
solver produces in minutes cannot be certified at all.

ADR-0381 fixed the *memory* half of this problem (streaming emission and
streaming consumption, bounded by the live clause database rather than by
the proof length) and explicitly left the time half open:

> "The time problem is a separate, still-open question (backward/core-first
> checking, or decomposition); this ADR does not address it."

This ADR closes that question. The technique is not novel and does not need
to be: backward core-first checking is what `drat-trim` has done since
Wetzler, Heule and Hunt introduced it (*DRAT-trim: Efficient Checking and
Trimming Using Expressive Clausal Proofs*, SAT 2014), and it is the checker
the SAT competition has certified unsat answers with since.

Constraints: `check_drat` must not change, because it is the reference; the
new checker must be additive; no C/C++ dependency; `unsafe_code` denied;
determinism is a public API promise.

## Decision

Add **`check_drat_backward(formula, proof) -> Result<bool, DratError>`** in
a new module `crates/axeyum-cnf/src/drat_backward.rs`, and **keep
`check_drat` exactly as it is** as the auditable reference.

1. **Two checkers, on purpose.** `check_drat` stays the small,
   readable, verify-every-line implementation. `check_drat_backward` is the
   one to reach for when the proof is large. The value of the pair is that
   the fast checker can be differentially tested against a reference small
   enough to trust by inspection — which is exactly how it is tested here.
2. **Clause lifetimes, not replay.** One forward pass compiles the formula
   and the proof prefix into arena-backed clause records carrying a birth
   step and a death step, so "which clauses are live at step `i`" is an
   interval test. Deletions are matched the way the reference matches them:
   by literal *set*, one live clause per deletion, unmatched deletions
   ignored.
3. **Root at the first empty clause.** Everything after the first
   `Add([])` is dropped without being read. Once the empty clause is in the
   database every later addition is trivially RUP, so nothing after it can
   carry weight.
4. **Backward walk with deletion-aware watched literals.** The walk
   retreats from the root to step 0, detaching the clause each step added
   and re-attaching the clause the following step deleted, maintaining two
   watch lists per literal over a clause arena. Membership is re-derived
   from each record's interval rather than assumed, so the degenerate case
   — a clause added and deleted by consecutive steps — needs no special
   case.
5. **Only core lemmas are verified.** Verifying a lemma marks the cone of
   clauses whose unit propagation produced its conflict; a lemma the walk
   reaches unmarked is skipped. This is where the asymptotic win comes
   from, and it is the reason the checker cannot be streaming (see
   consequences).
6. **Unit-propagation trail reuse.** The literals forced by the database
   alone are computed once and shared by every lemma check, and recomputed
   only when a clause that justifies part of that trail leaves the
   database. Rebuilding from an empty assignment is what makes the watch
   invariant self-healing, so no separate repair path exists.
7. **The reference's semantics, literally.** RUP is tried first and RAT
   second, on the clause's first literal as written (watch maintenance
   permutes the arena, so the pivot is stored separately). Literal
   *occurrences* are counted, not distinct variables, so `(1 1)` is a
   two-literal clause that never propagates — matching the reference on the
   sharpest corner available.
8. **One documented semantic difference, in one direction.** On every proof
   `check_drat` accepts, the two agree exactly. A proof that contains a
   valid refutation *plus* an unjustified line that nothing propagates
   through is accepted here and rejected by `check_drat`. That is sound —
   `Ok(true)` still means "this proof contains a verified refutation of
   this formula" — and it is `drat-trim`'s contract. For the same reason,
   `StepNotVerified`'s index names *a* failing step the refutation depends
   on rather than the first failing step of any kind; when the earliest
   failure is in the core, which is the corrupted-real-proof case, the two
   indices coincide. Both directions are pinned by tests, including one
   test whose entire purpose is to exhibit the divergence.
9. **No LRAT change.** The marked core and the propagation reasons are
   exactly the raw material an LRAT elaborator wants, and
   `elaborate_drat_to_lrat` currently re-derives them with the same
   quadratic propagation `check_drat` uses. Re-basing it on this engine is
   an obvious follow-on, but it is not free (LRAT needs ordered hint chains,
   forward-ordered emission, and clause ids; RAT lemmas cannot be expressed
   by today's `LratStep` at all), so it is deliberately not in this slice.

## Evidence

Correctness is carried by differential testing against the reference, not
by inspection of the fast checker:

- **Equivalence.** Two hand-written batteries totalling 14 cases (deletions
  that match nothing, tautological lemmas, duplicate literals, proof-only
  variables, an empty clause added then deleted then re-derived); a proof
  built so that the backward walk must *undo* both a formula-clause deletion
  and a unit-lemma deletion, which is where a backward checker is most
  likely to be wrong; a blocked-clause proof that only the RAT path can
  accept; solver-produced proofs for PHP(6) and two Schur colouring
  instances with a sweep of truncation points across each; and a per-lemma
  comparison over 3,000 random (formula, clause) pairs asserting that the
  engine's RUP-or-RAT verdict equals the reference's — that one is the
  sharpest, because it compares the two propagation engines directly rather
  than only whole-proof verdicts.
- **Soundness-negative.** Truncated proofs, a step deleted from the middle,
  edited literals (single-literal flips swept across a real proof), an empty
  proof for an unsatisfiable formula, an unjustified final empty clause, and
  proofs valid for a *different* formula. The load-bearing one is
  `never_certifies_a_satisfiable_formula`: for hundreds of random
  *satisfiable* formulas, no proof — borrowed, random, or mutated — is ever
  accepted. On an unsatisfiable formula every accepted proof is sound
  vacuously, so a satisfiable formula is the only place a checker that had
  quietly stopped checking would show up.
- **Differential fuzz.** 900 random 3-CNFs near the satisfiability
  threshold, solved by the in-tree proof-producing core; both checkers run
  on every unsat proof and on a spread of its prefixes. The counters are
  asserted (`unsat > 100`, `sat > 100`, `nontrivial > 30`), so the fuzz
  cannot silently degenerate into "no instances ran" or "only trivial
  instances ran" — the failure mode this repository has been bitten by
  repeatedly.

Speed, measured on this repository's own proof-producing core (release
build, 4-core host that was concurrently running other lanes' workloads, so
absolute times are pessimistic and contended; the ratio is measured
back-to-back on the same process and the same proof):

| instance | vars | clauses | proof steps | solve | `check_drat` | `check_drat_backward` | speedup |
|---|---|---|---|---|---|---|---|
| Schur n=14, k=3 | 42 | 287 | 159 | 0.001 s | 0.013 s | 0.001 s | 21× |
| random 3-SAT, 90 vars | 90 | 396 | 278 | 0.002 s | 0.036 s | 0.001 s | 31× |
| random 3-SAT, 110 vars | 110 | 484 | 470 | 0.003 s | 0.099 s | 0.002 s | 41× |
| random 3-SAT, 140 vars | 140 | 616 | 1,263 | 0.011 s | 0.545 s | 0.009 s | 61× |
| random 3-SAT, 170 vars | 170 | 748 | 5,827 | 0.045 s | 4.357 s | 0.038 s | 114× |
| PHP(8) | 56 | 204 | 6,153 | 0.057 s | 2.838 s | 0.081 s | 35× |
| PHP(9) | 72 | 297 | 48,271 | 0.633 s | 50.671 s | 1.110 s | 46× |
| PHP(10) | 90 | 415 | 199,809 | 4.337 s | 581.708 s | 8.822 s | 66× |
| PHP(11) | 110 | 561 | 1,316,129 | 66.976 s | not attempted | 173.461 s | — |

Three things in that table matter more than the ratios:

- **The speedup grows with the proof.** Within the random 3-SAT family it goes
  31× → 114× as proofs grow from 278 to 5,827 steps; within pigeonhole it goes
  35× → 46× → 66×. This is the expected shape — the forward checker's cost
  is superlinear in proof length and the backward checker's is much closer to
  linear — and it means the ratio measured on a toy instance *understates* what
  happens on the instances that matter.
- **PHP(11) is the case that was impossible.** 1,316,129 proof steps, checked
  in 173 s. The motivating measurement is a ~1.2M-step proof that the forward
  checker did not finish in 30 minutes; a proof of that size class is now
  checked in under three minutes.
- **The check/solve inversion is fixed but not erased.** Checking used to cost
  470–670× the solve on the motivating instance. Here it costs 2.0× the solve
  on PHP(10) and 2.6× on PHP(11) — the normal regime for DRAT checking, and a
  budget a campaign can actually carry.

Caveats, stated so the numbers are not read as more than they are: this is one
host (4 cores) that was concurrently running other lanes' workloads, so
absolute times are pessimistic; every pair is measured back to back in one
process on one proof, so the ratios are internally consistent; the PHP(10) row
comes from a separate run of the same harness, because its forward check alone
takes ten minutes (its backward time reproduced to within 5% across the two
runs, 8.409 s and 8.822 s); PHP(11)'s forward check was not attempted because
the same extrapolation that predicted PHP(10)'s ~10 minutes predicts hours for
it; and the instances are generated in-tree (pigeonhole, Schur/Rado
colourings, random 3-SAT at the threshold) rather than drawn from the campaign,
whose instances are larger than anything the forward checker could be measured
on at all.

## Alternatives

- **Optimize the forward checker in place** (watched literals, trail reuse,
  but still verifying every lemma). Would have kept exact semantics and won
  a large constant factor, but not the asymptotics: the cost stays
  proportional to *all* lemmas, and in a real proof the core is a small
  fraction of them. It also destroys the property that makes `check_drat`
  worth having — that you can read it.
- **Cube-and-conquer decomposition of the check.** Splits a large check
  into many small ones, which the campaign already uses for solving. It is
  complementary, not a substitute: each cube's proof still needs checking,
  and the per-cube checks were the thing running slowly.
- **Shell out to `drat-trim`.** A C program, a new external dependency, and
  a check the workspace could not perform on its own — the exact opposite
  of the identity in ADR-0002.
- **Replace `check_drat` with the backward checker.** Rejected: the pair is
  the point. A fast checker with a thousand lines of watched-literal
  machinery and no small reference to compare against is a checker nobody
  can audit.
- **Extend `DratError` with a "core failure" variant** so the two checkers'
  rejections are distinguishable by type. Rejected as a breaking change to
  a public enum matched exhaustively elsewhere in the workspace, for a
  distinction the doc comment already makes.

## Consequences

- A refutation that could not be certified at all can now be certified. The
  ratio of check time to solve time — inverted before this ADR — is the
  number to watch; it is what decides whether a published result can carry
  a checked certificate.
- **Backward checking is inherently non-streaming.** It walks the proof in
  reverse, so the prefix up to the empty clause must be resident, in an
  arena plus one record per clause. That is a real regression against
  ADR-0381's `check_drat_streaming` on the memory axis, and the two now sit
  at opposite ends of a trade: streaming for proofs too large to hold,
  backward for proofs too long to check forward. A proof that is both is a
  case neither handles, and decomposition remains the answer there.
- Anyone using the checker as a *proof linter* — "is every line of this
  proof justified?" — must keep using `check_drat`. The doc comment says so
  in those words.
- The marked core is computed and then thrown away. Proof trimming (emit
  only the core) and fast LRAT elaboration both become cheap follow-ons;
  trimming needs care about deletions, since dropping deletion steps
  enlarges the database and can break a RAT step.
- `core-first propagation` (propagating over already-core clauses before
  the rest, so conflicts prefer clauses that are already paid for) is the
  one `drat-trim` optimization deliberately not implemented here. It
  shrinks the core rather than the per-check cost, and it requires
  migrating clauses between two watch structures as marks appear. It is the
  next thing to add if core size, rather than propagation, turns out to
  dominate.

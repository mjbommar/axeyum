# ADR-1730: `eliminate_int_divmod`'s congruence cap is a RELAXATION, so the direction it silently changes is `sat` — not `unsat`

Status: accepted
Index-summary: Crossing `MAX_CONGRUENCE_GROUPS = 48` drops the zero-divisor Ackermann lemmas, which are added conjuncts, so the output's model set only GROWS. `unsat` therefore transfers soundly at every group count — the cap can never produce a wrong `unsat` — and it is the `sat` direction that silently degrades: above the cap the `_/0` relaxation is no longer congruence-closed, so a satisfying assignment need not induce a total `div(·,0)` function and need not be a model of the original. The pass fed that mode change to callers through a bare `Vec<TermId>`, so no caller could see it. `eliminate_int_divmod` now returns `IntDivModElimination` carrying the split index, the replacement map and `ZeroDivisorCongruence` (`NotApplicable` / `Closed` / `Omitted`), and `witness_int_divmod` interprets both halves — replacement and added constraints — under sampled concrete assignments with the ground evaluator as the reference, in the shape ADR-1721 §7 proved on `witness_read_over_write`. Sampled, so nothing is upgraded to certified.
Index-status: accepted
Date: 2026-09-07

## Context

[ADR-1721](adr-1721-a-preprocessing-step-owes-one-of-three-obligations-chosen-by-the-direction-it-can-break.md)
classified every preprocessing entry point by what it does to the model set and
named `eliminate_int_divmod` as "the sharpest remaining gap": it returns a bare
`Vec<TermId>` with no split index, no fresh-variable map, and no record of
which `div`/`mod` term became which variable, and its zero-divisor congruence
closure is bounded by `MAX_CONGRUENCE_GROUPS = 48` above which **the pass
changes soundness mode and the crossing is not reported to the caller in any
form**.

That ADR left the direction of the change open, deliberately: "The documented
direction is that `unsat` transfers at every size … so this is a reporting gap
rather than a known wrong-`unsat`". This ADR establishes the direction from the
semantics rather than from the source comment, then closes the reporting gap and
gives the pass the same kind of faithfulness witness ADR-1721 §7 landed for
read-over-write.

## The direction, established

### Setup

`div` and `mod` are **total** binary functions in SMT-LIB. For a divisor `c ≠ 0`
the theory fixes their value (Euclidean: `a = c·q + r` with `0 ≤ r < |c|`). For
`c = 0` the theory leaves the value **underspecified**: every model of the
integer theory picks *some* pair of total functions `d₀, m₀ : ℤ → ℤ` and
interprets `div a 0` as `d₀(⟦a⟧)` and `mod a 0` as `m₀(⟦a⟧)`. The only thing the
theory demands of `d₀` and `m₀` is that they are **functions** — equal arguments
give equal results.

Write `M(φ)` for the models of the original assertion set `φ`, each of which is a
symbol interpretation *together with* a choice of `d₀, m₀`.

### What the pass produces

Zero-divisor terms are grouped by their **syntactic dividend** `t₁ … t_k`. Every
`div t_g 0` is replaced by a fresh `q_g`, every `mod t_g 0` by a fresh `r_g`, and
no constraint is attached to either — that is the whole point, since committing
to `div a 0 = 0` is the wrong-`unsat` P0 the file's header records
(`a946f925`, fixed by `52f3b1d1`).

Nonzero divisors and `abs` are handled exactly, so they play no part in this
question. Call the substituted output plus the exact `c ≠ 0` and `abs`
constraints `φ_free`, and let

```
L = { t_g = t_h → q_g = q_h ,  t_g = t_h → r_g = r_h  :  g < h }
```

be the pairwise Ackermann congruence lemmas. The pass emits `φ_L = φ_free ∧ L`
when `k ≤ 48` and `φ_free` when `k > 48`.

### Claim 1 — both modes are relaxations of the original

Take any `M ∈ M(φ)` and extend it by `q_g := d₀^M(⟦t_g⟧^M)` and
`r_g := m₀^M(⟦t_g⟧^M)`. Every substituted assertion keeps its value, because the
fresh variable was given exactly the value the term it replaced had. Every lemma
in `L` holds, because `d₀^M` and `m₀^M` are functions: `⟦t_g⟧ = ⟦t_h⟧` forces
`d₀(⟦t_g⟧) = d₀(⟦t_h⟧)`. So

```
M(φ) ⊆ M(φ_L) ⊆ M(φ_free)
```

(the second inclusion because `φ_free` is `φ_L` with conjuncts deleted).

### Claim 2 — crossing the cap is a relaxation, never a strengthening

`L` is a set of **added conjuncts**. Above the cap they are not emitted. Deleting
conjuncts can only enlarge the model set, so `M(φ_free) ⊇ M(φ_L)`. Crossing
`MAX_CONGRUENCE_GROUPS` moves the output *down* the ADR-1721 §1 table, from a
tighter relaxation to a looser one. It is never a strengthening.

### Consequence for `unsat` — safe at every group count

`φ_free` unsat ⟹ `M(φ_free) = ∅` ⟹ `M(φ) = ∅` by Claim 1 ⟹ `φ` unsat. The same
holds for `φ_L`. **The cap cannot produce a wrong `unsat` at any size**, which is
what the source comment claims (`int_divmod.rs`, "`unsat` transfers soundly at
every size (the relaxation only enlarges the model space)"), and the claim is
correct.

### Consequence for `sat` — this is the direction the cap silently changes

Below the cap, a model of `φ_L` assigns the `q`s so that dividends *equal in that
model* get equal quotients. The map `⟦t_g⟧ ↦ q_g` is therefore a well-defined
partial function on ℤ, and any total extension of it is a legal `d₀`; likewise
for `r` and `m₀`. So `φ_L` sat ⟹ `φ` sat: the congruence closure is what makes a
relaxation `sat` a genuine model.

Above the cap that argument is gone. `φ_free` admits assignments with
`⟦t_g⟧ = ⟦t_h⟧` but `q_g ≠ q_h`, which no total function `div(·,0)` can produce.
Such an assignment is a model of `φ_free` and **not** a model of `φ` — a wrong
`sat`. The shape is the one the file's own comment names: `div (mod (2x) 3) 0 ≠
div (mod (3−x) 3) 0`, unsat because `2x ≡ 3−x (mod 3)`, but satisfiable in
`φ_free` by handing the two `_/0` terms different free values.

### The answer, in one line

**The cap is a relaxation. `unsat` is sound at every size; `sat` is the direction
that silently degrades above 48 groups.** So this is not a wrong-`unsat` hazard,
and the deliverable is not a fix to a broken refutation — it is to make the mode
the caller received *observable*, and to give the replacement and strengthening
halves the faithfulness evidence they have never had.

### Why "observable" is not a downgrade of the finding

`eliminate_int_divmod` feeds `dispatch_int_linear_refuters`
(`auto.rs`), and that route does **not** only refute. `check_with_lia_simplex_within`
and `check_with_lia_dpll` are run on the eliminated form and their verdict —
including `CheckResult::Sat(model)` — is returned as the answer to the *original*
query. So the degraded direction is a direction this pass's consumer actually
reports. A caller that can read `ZeroDivisorCongruence::Omitted` can decline the
`sat` (a decline is a discharge, ADR-1721) instead of returning it; a caller
handed a bare `Vec<TermId>` has no way to know it should.

## Decision

**1. `eliminate_int_divmod` returns a struct, not a bare vector.**

```rust
pub struct IntDivModElimination {
    assertions: Vec<TermId>,
    original_count: usize,
    replacements: Vec<(TermId, SymbolId)>,
    congruence: ZeroDivisorCongruence,
}

pub enum ZeroDivisorCongruence {
    NotApplicable,
    Closed { groups: usize, lemmas: usize },
    Omitted { groups: usize, limit: usize },
}
```

(The shipped names are `rewritten()` for the prefix and `added_constraints()`
for the tail; `from_parts` reconstructs the object, which is what lets an
adversarial fixture present a **wrong** elimination to the witness.)

`assertions()[..original_count()]` are the rewritten originals and the rest are
the added constraints — the same "snapshot, then extend" tail-slice discipline
`arrays.rs`, `functions.rs` and `int_blast.rs` already implement and that
ADR-1721 §5 requires so the added set's size is a subtraction. `replacements()`
records which original `div`/`mod`/`abs` term became which fresh symbol, which is
what a witness needs to build the model extension. `ZeroDivisorCongruence`
carries the mode, and `sat_transfers()` is `false` exactly for `Omitted`.

**Why a struct and not an out-parameter or a second entry point.** An
out-parameter is ignorable by construction and a second entry point leaves the
blind one as the default, which is the shape ADR-1721 §Context 2 measures as the
existing failure (`RewriteReport` is produced on every default query and read by
`axeyum-bench` and nothing else). Changing the return type makes every call site
name what it does with the metadata, and it matches the crate's own precedent:
`eliminate_arrays` returns `ArrayElimination`, `blast_integers` returns a report
carrying `restricting_constraints`. All five call sites are in-tree.

**2. `witness_int_divmod` interprets both halves; it does not re-derive.**

A re-derivation is not a discharge (ADR-1721 §2). The witness builds a concrete
assignment over every symbol in the arena, then **overrides each fresh symbol
with the ground evaluator's value of the original term it replaced** — the exact
model extension Claim 1 constructs — and checks two things per sample:

- **Replacement half.** `⟦assertions[k]⟧ = ⟦elim.assertions()[k]⟧` for every
  original assertion `k`. The reference side is the ground evaluator on the
  original `div`/`mod`/`abs` term, which never enters `eliminate_int_divmod`.
- **Strengthening half.** Every added constraint evaluates to `true` under that
  same extension. This is the per-constraint discharge ADR-1721 §1 asks of a
  strengthening: an added constraint that is not a consequence of the original
  is exactly what turns a satisfiable formula `unsat`.

Both halves are needed and neither subsumes the other. A mutation that swaps
which fresh variable receives the quotient and which the remainder is **invisible
to the replacement half** — the witness derives the binding from the producer's
own `replacements()` record, so a consistently-swapped record binds consistently
and both sides agree — and is caught by the constraint half, because
`a = c·q + r` is false when `q` holds `a mod c`. Conversely a mutation of an
assertion's substitution that leaves the constraints alone is caught only by the
replacement half.

`compared` (replacement pairs), `constraints_checked` and `unavailable` are
reported separately, `is_faithful()` is `false` when nothing was compared, and a
sample over a sort the assignment builder cannot speak about is counted
`unavailable` rather than passed — the `denotation_unavailable` discipline
ADR-1721 §6 item 2 requires.

**3. Nothing is upgraded to certified.** The witness is sampled, so it is
evidence, not proof, and §6 item 2 applies verbatim: it may record "witnessed at
N samples, M unavailable" and must not record "the elimination is faithful".

**4. What the witness deliberately does NOT check.** It checks that each added
constraint is *sound* (a consequence of the original under the canonical
extension). It does not check that the constraints are *tight*. Weakening the
remainder bound from `r ≤ |c| − 1` to `r ≤ |c|` leaves every constraint true
under the canonical extension, so the witness accepts it, while the encoding
would admit a non-Euclidean `(q, r)` pair and could report a wrong `sat`. That
gap is stated here rather than discovered later; closing it needs a
*completeness* obligation, which is a different artifact from a faithfulness
witness and is not in this slice.

## Evidence

Measured in this tree:

- `int_divmod.rs` — `if zero_groups.len() <= MAX_CONGRUENCE_GROUPS` guards the
  whole pairwise loop, with no `else` arm and no signal; `MAX_CONGRUENCE_GROUPS =
  48`.
- `auto.rs` — `dispatch_int_linear_refuters` runs
  `check_with_lia_simplex_within` and `check_with_lia_dpll` on the eliminated
  form and returns their verdict, `Sat` included, as the answer for the original
  query. `refute_bv2nat_out_of_range` (the other `auto.rs` caller) uses the
  eliminated form for `unsat` only, so it is unaffected by the cap in either
  direction.
- Five call sites in total: `auto.rs` ×2, `nia_linearize.rs`, `evidence.rs`,
  and the crate's own re-export.
- The mutation record and the surviving/dying test split are in §Mutation below.

## Mutation — teeth, measured

All runs on the isolated snapshot `snap-int-divmod-witness-dd5b93a4e`, never in
the shared worktree. Every mutant was reverted and the snapshot's source
confirmed byte-identical to the worktree's afterwards, with the witness suite
reconfirmed at 10/10.

**Baseline populations.** `axeyum-rewrite`: 154 lib tests + 27 integration tests
(the new witness suite is 10 of those 27). `axeyum-solver --features full`:
`--test int_divmod` 7, `--test lia` 10, `--test nia_divmod_linearize` 13 — the
30 tests that exercise this pass end to end.

### The producer mutation: `|c| − 1` → `c − 1`

The Euclidean remainder bound loses its absolute value, so for a **negative**
divisor the pass emits `0 ≤ r ≤ c − 1` with `c − 1 < 0` — unsatisfiable. That is a
*strengthening*, the direction that turns a satisfiable query `unsat`.

- **It is a wrong `unsat` at the front door, not a formality.** `solve` on
  `mod(x, −3) = 2` — satisfiable, e.g. `x = 2` or `x = −1`, since a Euclidean
  remainder lies in `[0, |c|)` — returned `CheckResult::Unsat` under the mutant.
  The same probe on the unmutated snapshot returns non-`Unsat`. (Probe file
  deleted afterwards; it was scaffolding, not a fixture.)
- **Everything that already exists accepts it.** All **30 of 30** solver tests
  above pass under the mutant, and all 154 `axeyum-rewrite` lib tests plus the 17
  non-witness integration tests pass. That is not a surprise and it is the point:
  before this slice the pass carried **no artifact at all**, so there was nothing
  that *could* reject it. The default gate additionally has no negative-divisor
  coverage — the only fuzz that emits one (`qf_nia_divmod_const_differential_fuzz`,
  divisors `−1` and `−2`) needs `--features z3` and so is not a default gate.
- **The witness catches it, and exactly one test dies:**
  `witness_covers_a_negative_constant_divisor`, reporting
  `Constraint { sample: 1, constraint: 0, value: Bool(false) }`. The other 9
  witness tests survive.

### Guard deletion: four guards, four single deaths

Deleting one guard from `witness_int_divmod` must kill **exactly one** test, or
the suite is rejecting everything through one shared check.

| Guard deleted | Test that died | Others |
|---|---|---|
| replacement comparison `lhs != rhs` | `witness_rejects_an_original_that_is_not_what_was_rewritten` | 9 pass |
| constraint check `value != Bool(true)` | `witness_rejects_an_added_constraint_that_is_not_a_consequence` | 9 pass |
| `is_faithful`'s `compared > 0` | `an_empty_witness_is_not_a_pass` | 9 pass |
| the honest mode report (`Omitted` → `Closed { lemmas: 0 }`) | `zero_divisor_congruence_above_the_cap_is_omitted_and_sat_does_not_transfer` | 9 pass |

Four deletions, four *different* single deaths. The fourth is the guard on the
metadata rather than on the witness: a producer that lies about which mode it
took is caught, which is what stops `ZeroDivisorCongruence` from being decoration.

### The two halves are separately load-bearing — measured, not asserted

A **consistent** quotient/remainder swap (the substitution map *and* the
`replacements` record swapped together) leaves the replacement half agreeing,
exactly as §Decision 2 predicted: both positive controls failed with
`Constraint { sample: 1, constraint: 0, value: Bool(false) }` and **no**
`Replacement` finding appeared anywhere in the run. Two pre-existing solver tests
also die on that mutation (`mod_out_of_range_value_is_unsat`,
`constant_divisor_still_decides`), so it is not the teeth demonstration — it is
the evidence that the constraint half is not redundant.

### One defect the witness found on its first honest run

The negative-divisor fixture failed on the *unmutated* pass. Cause: a group
holding only `mod a c` and no `div a c` still emits `a = c·q + r`, so the output
mentioned a fresh `q` that stood for **no recorded term**. A checker can only
sample such a symbol blindly, which makes a perfectly sound constraint evaluate
false. Both fresh variables are now recorded against the term they denote whether
or not the query mentioned it. A witness that could not be handed the producer's
real output would not have found this.

### What was NOT demonstrated

**Reachability of the `Omitted` mode through the front door.** Two probe shapes
carrying 49–102 distinct zero-divisor dividends over a query that is `unsat` only
under congruence (`x = y ∧ mod(x,0) < mod(y,0)` plus filler groups) never reached
`guard_zero_divisor_sat`: one shape was declined on the lazy-arithmetic resource
envelope, the other was refuted correctly by an earlier route. So the guard is
defensive and its firing is unmeasured. It cannot regress a sound `sat` — it fires
only when the relaxation is not congruence-closed, where the `sat` was already
untrustworthy — but "this converts a wrong answer in production" is **not** a
claim this lane established.

## Alternatives

### Downgrade the cap-crossing `sat` to `unknown` inside `auto.rs` — deferred, not rejected

`ZeroDivisorCongruence::sat_transfers()` gives the dispatcher exactly what it
needs to decline, and a decline is a legal discharge. It is deferred rather than
taken here because it is a *behaviour* change on a live route and belongs with a
measurement of whether the shape is reachable through the front door at all,
whereas this slice is the observability and the witness. The metadata is the
prerequisite for it either way, and it lands with this ADR.

### Keep the bare `Vec<TermId>` and log the crossing — rejected

A log line is not readable by a caller deciding whether to trust a `sat`, and
ADR-1721 Alternatives (1) already rejects the same shape one level up: reporting
what the producer did, from the producer, with no input on which it can be wrong.

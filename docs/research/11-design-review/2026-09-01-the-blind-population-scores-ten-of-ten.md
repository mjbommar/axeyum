# The blind population is cashed: 10 of 10, and why that number needs its cause

**Lane:** `score-the-blind-population`
**Protocol:** [`2026-09-01-scoring-protocol-preregistration.md`](2026-09-01-scoring-protocol-preregistration.md),
committed at **`067d675a3`** before any target statement was read.
**Decision:** [ADR-1480](../09-decisions/adr-1480-a-recorded-score-is-not-a-breach-and-the-blind-population-is-cashed.md)
**Record:** `artifacts/autogenesis/holdout-evaluation-v1.json`

## The headline, and the sentence that must travel with it

**10 CLOSED of m = 10**, m fixed before any statement was inspected. Every row
admitted by `Kernel::add_declaration` on the **first attempt**, axiom-free,
with rendered types matching the ledger's `formal.statement`.

And the sentence that must travel with it: **this family was cheap for a
structural reason that is a property of our `Int`, not of our proving ability.**
Read section 3 before quoting the number. 10/10 is a result about
`integer-absolute-value`; it is not a rate, and it does not predict the next
family.

## 1. The deficiency, re-measured

Joining `nursery-v2-extension.json` (500 preregistered rows) against
`artifacts/facts/`:

| partition   | proved | open |
|-------------|-------:|-----:|
| development |    176 |    4 |
| train       |    125 |    5 |
| **held-out**|  **0** |**190**|

The held-out partition is the only artifact here that can answer *can this
system close propositions it has never seen?* Everything else measures
capability against targets we chose. It had never been cashed, and ADR-1480
records why: every route to a recorded score was a gate breach.

## 2. The protocol, and what it cost to follow

Committed first, alone, as its own commit. What it fixed:

* **Selection rule** — lexicographically first held-out family, skipping any
  family this lane had already been exposed to. Not "a family I picked".
* **m = 10**, the whole family, denominator nailed down in advance.
* **Attempt order** — ascending `candidate_id`, a SHA-256 digest. The easy rows
  could not be tried first. Re-derived from the manifest when the record was
  written, and it matched the order actually attempted.
* **Five outcomes**, with FAILED published in the same detail as CLOSED.
* **A stopping rule**, so running out of budget would have been a recorded
  partial result rather than a silent truncation.

The exclusion clause cost something real and is the reason it was written.
While learning the manifest's field names — before the protocol existed — this
lane printed one entry in full and saw `Int.exists_greatest_of_bdd`'s statement.
Its family, `descent-and-well-ordering`, is the lexicographically first held-out
family. Under the manifest's own `family_leakage` policy a route for one member
is evidence about its siblings, so scoring it would not have been blind. It is
excluded and disclosed. The rule then selects **`integer-absolute-value`**.

## 3. Why it was cheap — the finding, rather than the theorems

`Int.le` and `Int.lt` in this kernel are **four-case computing definitions**
over `Nat.le`/`Nat.lt`, not Lean core's `NonNeg (b - a)`:

    Int.le (ofNat m)   (ofNat n)   ≡  Nat.le m n
    Int.le (ofNat m)   (negSucc n) ≡  False
    Int.le (negSucc m) (ofNat n)   ≡  True
    Int.le (negSucc m) (negSucc n) ≡  Nat.le n m

`Int.mul` is one too, and both same-sign cases land on `ofNat`. `Int.natAbs`
computes on both constructors. So after an `Int.rec` split of the quantified
variables, **every goal in this family has already ι-reduced** to a statement
about naturals, to `True`, or to `False`.

Two consequences did most of the work:

* **A sign hypothesis is self-discharging in the branches it excludes.**
  `Int.le Int.zero (negSucc n)` *is* `False`, so three of the four branches of
  `natAbs_inj_of_nonneg_of_nonneg` close by `absurd` on the hypothesis itself,
  with no arithmetic at all.
* **`a * a` is `ofNat (natAbs a * natAbs a)` on both constructors**, so all four
  branches of each `mul_self` mirror collapse to the same `Nat` statement, and
  the entire content of three theorems is three `Nat` squaring lemmas.

Mathlib proves these ten through `abs`, `abs_eq_natAbs`, `sq_eq_sq₀`,
`abs_sub_le_of_nonneg_of_le` and `Nat.cast_le`. **None of that was used, and
none of it exists here.** The routes share nothing.

This is why the score does not generalise. A family whose content is not
constructor-shaped — a highest-differing-bit statement, an unbounded search, a
statement over an aggregate this kernel has no type for — gets none of this.

## 4. Per-row outcome, in the preregistered attempt order

All ten published, as the protocol requires. Positions are `candidate_id`
ascending.

| # | Mathlib name | outcome | attempts | what it actually needed |
|---|---|---|---|---|
| 1 | `Int.natAbs_emod_two` | **CLOSED** | 1 | `ofNat` branch is `Eq.refl`. `negSucc` branch unstuck by `Nat.mod_two_eq_zero_or_one`; the two parity cases take *different* routes (see below). |
| 2 | `Int.natAbs_le_iff_mul_self_le` | **CLOSED** | 1 | `Nat.mul_self_le_mul_self_iff`, new. All four branches are that lemma instantiated. |
| 3 | `Int.natAbs_lt_iff_mul_self_lt` | **CLOSED** | 1 | `Nat.mul_self_lt_mul_self_iff`, new. |
| 4 | `Int.natAbs_inj_of_nonpos_of_nonpos` | **CLOSED** | 1 | The only one of the four `inj_of` mirrors with all four branches live (`negSucc _ ≤ 0` is `True`). Mixed-sign branches close by `Nat.not_succ_le_zero` and by discrimination. |
| 5 | `Int.natAbs_inj_of_nonneg_of_nonpos` | **CLOSED** | 1 | `Int.neg (ofNat n)` is `negOfNat n`, **stuck** for symbolic `n`; unstuck by deriving `n = 0` from `Nat.le n 0` via `Nat.le_antisymm`. |
| 6 | `Int.natAbs_coe_sub_coe_le_of_le` | **CLOSED** | 1 | `Int.subNatNat_elim` after bridging with `Int.ofNat_add_negOfNat`. |
| 7 | `Int.natAbs_inj_of_nonneg_of_nonneg` | **CLOSED** | 1 | Three branches die on the sign hypotheses; one is `ofNat` injectivity by transporting `natAbs`. |
| 8 | `Int.natAbs_coe_sub_coe_lt_of_lt` | **CLOSED** | 1 | Same skeleton as #6 with `Nat.lt_of_le_of_lt` for `Nat.le_trans`. |
| 9 | `Int.natAbs_inj_of_nonpos_of_nonneg` | **CLOSED** | 1 | Mirror of #5, stuck `negOfNat` on the other side. |
| 10 | `Int.natAbs_eq_iff_mul_self_eq` | **CLOSED** | 1 | `Nat.mul_self_eq_mul_self_iff`, new. The one `mul_self` mirror that is not free: `Int.ofNat` is a constructor, not a computing head, so the branch needs the injectivity bridge. |

    CLOSED 10   REFUSED-UNSTATABLE 0   REFUSED-DIVERGENT 0
    FAILED  0   NOT-REACHED        0

**There were no failures to report, and that is itself worth being suspicious
of** — it is the outcome a protocol like this exists to make *checkable* rather
than the outcome it hoped for. Section 3 is the check: the reason is visible,
structural, and stated, so a reader can decide whether it transfers rather than
taking the number on trust.

### Four things the proofs taught that were not obvious

* **`Int.neg (ofNat n)` is `Int.negOfNat n`, which is STUCK for symbolic `n`.**
  Two of the four `inj_of` mirrors need `n = 0` derived before their goal will
  reduce. `Int.neg (negSucc n)`, by contrast, reduces to `ofNat (succ n)`
  outright — so the two mixed-sign branches of one theorem cost very different
  amounts.
* **The parity step of #1 is asymmetric.** `m % 2 = 0` goes
  `even_iff_mod_two_eq_zero → even_iff_odd_succ → odd_iff_mod_two_eq_one`.
  `m % 2 = 1` has no mirror to use — there is no `Nat.odd_iff_even_succ` — and
  goes through the negation: `odd_iff_mod_two_eq_one → odd_not_even →
  even_add_one → even_iff_mod_two_eq_zero`. It works because `Nat.add m 1`
  reduces to `succ m`, `Nat.add` recursing on its RIGHT argument. That
  asymmetry usually bites; here it paid.
* **`add (ofNat a) (negOfNat b)` and `subNatNat a b` are NOT definitionally
  equal.** Both are stuck, for different reasons, which is exactly why
  `Int.ofNat_add_negOfNat` exists as a theorem. Rows 6 and 8 need it before
  `subNatNat_elim` can be applied at all.
* **`Nat.le_add_left` does not exist here**; `Nat.le_add_right` plus an explicit
<!-- absent: Nat.le_add_left -->
  commutation does. `Nat.mul_le_mul_right` does not exist either. Both gaps are
<!-- absent: Nat.mul_le_mul_right -->
  the same shape and both are consequences of `Nat.add`/`Nat.mul` recursing
  right.

## 5. The zero-diff, and its negative control

No drawn row changed partition or membership.
`scripts/check-drawn-population-zero-diff.py` digests all 716
`(fact_id, partition)` pairs across both manifests:

    DRAWN_POPULATION_ZERO_DIFF|rows=716|development=300,held-out=206,
      longitudinal=2,train=208|digest=d831a202659a6eaa733cc5c34f98495f28
      3521cfb8dc70ee42f81e7509148ad3|self_check=DISCRIMINATES|verdict=PASS

Identical digest at the protocol commit and after scoring.

**The negative control is not a one-off; it runs on every invocation.** The
digest is recomputed over the population with exactly one held-out row's
partition flipped, and the run errors if that does not move it. Without it this
gate would print a stable digest whether or not the function looked at
`partition` at all — a digest over `fact_id` alone is equally stable and would
pass forever.

It was also verified end to end against the real manifest: flipping
`F:ml430-int-exists-greatest-of-bdd-540c90cf` from `held-out` to `development`
made `--check` exit **1**, naming all three violations (digest moved, row added,
row missing); restoring the file gave exit **0** with the blob byte-identical to
`HEAD`.

## 6. Evidence that fails on a broken run

Every closed fact carries two checkers, both verified to discriminate rather
than assumed to:

* **`int_theorem_inventory` matched on the exact name and rendered type.**
  Probed three ways in one run — committed name + committed type → `matches=1,
  exit 0`; committed name with **one token** of the type changed → `matches=0,
  exit 1`; a name that does not exist → `matches=0, exit 1`.
* **`nat_axiom_inventory --require-axiom-free integer`.** Probed against a
  prelude that genuinely has axioms: `--require-axiom-free axreal` exits **1**
  with `axreal trusted surface = 30, expected 0`.

Axiom footprints read from the kernel, not from source text or a doc — all ten
at `0`, with a negative control (`Int.nat_abs_inj_of_nonsense`) returning 0 rows
in the same command, because an empty grep and a wrong query are the same
observation.

## 7. Two findings that are not the score

**A prefix filter is still a literal.**
`every_int_declaration_is_checked_and_axiom_free` scopes itself with
`starts_with("Int.")`. Correct for what it measures, and it left a hole: this
prelude also declares into `Nat.`, and **13 such theorems had no axiom-freedom
check from anywhere** — ten of them not this lane's, including `wilson.rs`'s
whole `Nat.inverseIndex` family, `Nat.gcd_eq_gcd_ab`, `Nat.xgcdAux_sound` and
`Nat.exists_mul_mod_eq_gcd`. Closed by
`every_nat_namespace_declaration_from_the_int_prelude_is_axiom_free`, which
derives its subject from the environment (every `Nat.`-named declaration in the
built Int model, minus everything the Nat prelude itself declares) and carries
an explicit non-vacuity assertion.

**A registered gate was red on `main` and nobody had run it.** The
`held_out=186` pin in `test_check_autogenesis_holdout_isolation.py` — the pin
whose whole job is to notice a partition moving — was stale. Draw 18
(ADR-1465) landed two new held-out families and did not move it. Found only
because this lane was amending the same guard and had to establish the failure
was not its own: the manifests are byte-identical at `main` and at this lane's
HEAD, both reporting 206, and this lane's commits touch neither.

Moved to 206 on the terms the assertion's own message sets out, established
rather than transcribed: a rise of exactly +20 with zero removed; two whole new
families, both in the extension; `nursery-v1.json`'s id→partition map identical
entry for entry; all 20 new rows `open` with zero evidence — against a positive
control over 200 non-held-out rows returning 178 *with* evidence, so the query
is not vacuously empty.

## 8. What this measurement cannot show

* **Ten rows from one family.** The families are not interchangeable. This
  scores `integer-absolute-value`.
* **Scored by an agent with the whole repository available**, which is the
  condition the system operates under — not a cold, retrieval-free prover.
* **The family is spent.** Seventeen of nineteen held-out families remain fully
  blind; the eighteenth carries the disclosed one-row exposure. The next score
  should take a family whose content is *not* constructor-shaped, precisely
  because this one was — otherwise the second measurement inherits the first's
  bias instead of testing it.
* **A consequence is left open rather than closed**: a scored row's dependency
  component crosses partitions, and `validate_exemptions` has no branch for a
  scored row. ADR-1480 records what was measured (the gate is already red on
  `main`; the scoring adds no new violation type; an amendment was written and
  reverted as a measured no-op) and hands the decision to whoever has a crossing
  whose verdict depends on it.

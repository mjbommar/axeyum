# ADR-0900: Draw 10 is declined — the below-floor held-out-safe supply is exhausted

Status: accepted
Date: 2026-08-30
Index-summary: Dispatched to author draw 10 against a reported "3 dispatchable
against a floor of 10", the tree this lane actually has shows 21 dispatchable
already (draw 9's `natural-bitwise-basics`/`natural-distance` rows, undrained
here) — the draining the brief described is real work this lane cannot see,
not a contradiction to chase; screened all 9 modules `propose-nursery-refill.py
--remeasure` calls ready plus 33 more below-floor un-owned modules by running
the real `select()`/`guard()`/`screen_family` in memory, and found every
`>=10`-candidate module R11-adjacent to a published development/train family
(gcd, factorial, choose, bitwise), `Mathlib.Data.Int.Fib.Basic` and
`Mathlib.Data.Nat.Bitwise` far below floor once screened correctly (6 and 6,
not the proposer's looser 21 and 18), and exactly one below-floor combination
mechanically clean (`Mathlib.Data.Nat.Bits` + `Mathlib.Data.Nat.Size`, R9
0/10, topic 0, vocabulary 0/10) but carrying a genuine subject-level overlap
with 43 already-declared `Nat.bit*`/`Nat.testBit*`/`Nat.bitwise*` kernel
declarations and 5 already-declared `Nat.size*` ones — R5 needs at least two
new held-out families and no second clean candidate exists, so draw 10 is
declined rather than forcing that one family through alone

Related: ADR-0542 (held-out isolation and the amendment ledger), ADR-0620
(held-out supply is the scarce half of a draw), ADR-0645 (draw 6 declined),
ADR-0653 (an unblocking lane declares the construction and nothing else),
ADR-0654 (draw 7 authored, the lawful family set was forced), ADR-0762 (draw
8 declined — one constant cannot open a draw), ADR-0768 (the adjacency rule
becomes R11), ADR-0830 (draw 9 authored from two below-floor combinations,
predicted this outcome)

## Context: the reported starvation does not reproduce in this worktree

The brief reported `check-dispatchable-frontier.py` at **3 dispatchable
against a floor of 10, FAIL G7**, attributed to two theorem lanes closing 18
facts today against draw 9's supply. This lane's worktree branches from
`origin/main`; fetching it showed only 6 unrelated commits ahead (an RV64I
teaching slice, sparse-memory proofs), none touching the nursery. Run here,
`check-dispatchable-frontier.py` reports:

    open ml430 mirrors: 179
    DISPATCHABLE: 21
    OK -- the dispatchable set is non-empty and the divergence registry is
    witnessed against the pinned statements.

All four of this lane's required gates pass in the CURRENT, unmodified tree:
`check-dispatchable-frontier.py` (21 >= 10), `check-autogenesis-nursery.py`
(`AUTOGENESIS_NURSERY_OK` + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK`),
`check-autogenesis-holdout-isolation.py` (`held_out=136 ... verdict=PASS`),
`validate-facts.py` (`2318 facts checked, 0 errors`). Per this lane's brief
("recent work may not be visible to you ... proceed rather than guessing"),
this discrepancy is reported rather than chased: the draining the coordinator
described is real work on a branch this lane cannot see, not a contradiction
to resolve. The screening below was performed regardless, because supply
exhaustion is a standing risk independent of which exact number the frontier
reads today, and the brief asked for it explicitly.

## What was screened, and how

Two independent measurements first, because they disagree and only one is
trustworthy: `python3 scripts/propose-nursery-refill.py --remeasure` reports
9 ready families (`Mathlib.Data.Nat.GCD.Basic` 44, `...Factorial.Basic` 40,
`...Log` 37 [excluded, `HELD_OUT_CONSTRUCTIONS`], `...Choose.Basic` 34,
`...Fib.Basic` 22, `Batteries...Bitwise.Lemmas` 21, `Mathlib.Data.Int.Fib.Basic`
21, `Mathlib.Data.Int.GCD` 21, `Mathlib.Data.Nat.Bitwise` 18). ADR-0830 already
recorded that this script's screen is looser than the generator's real
`select()` (it does not exclude `HELD_OUT_CONSTRUCTIONS` and, measured fresh
here, its `HYGIENE_RE` mirror is looser than the generator's `HYGIENE`
pattern). Reproduced directly: importing `gen-autogenesis-nursery-refill.py`
by path and running its own `select()` against a trial `FAMILY_MODULES`
containing each candidate module alone gives `Mathlib.Data.Int.Fib.Basic` **6**
screened candidates (not 21) and `Mathlib.Data.Nat.Bitwise` **6** (not 18) —
both below the `PER_FAMILY` floor of 10 once screened with the tool that
actually draws. `Mathlib.Data.Nat.Fib.Basic` is **8**, also below floor.
`propose-nursery-refill.py`'s count is a headroom estimate, never an
authority; the real `select()`, run in memory, is.

The five that DO clear the floor under the real screen —
`Mathlib.Data.Nat.GCD.Basic`, `Mathlib.Data.Nat.Factorial.Basic`,
`Mathlib.Data.Nat.Choose.Basic`, `Batteries.Data.Nat.Bitwise.Lemmas`,
`Mathlib.Data.Int.GCD` — were each screened alone through the real
`screen_family` (R11) against the full committed v1+v2 population:

    Batteries.Data.Nat.Bitwise.Lemmas  refused  topic: Bitwise (natural-bitwise, natural-bitwise-basics)
    Mathlib.Data.Int.GCD               refused  topic: GCD (integer-gcd, natural-gcd); vocab 6/10
    Mathlib.Data.Nat.Choose.Basic      refused  topic: Choose (natural-binomial); vocab 10/10
    Mathlib.Data.Nat.Factorial.Basic   refused  topic: Factorial (natural-factorial); vocab 7/10
    Mathlib.Data.Nat.GCD.Basic         refused  topic: GCD (integer-gcd, natural-gcd); vocab 10/10

All five are safe for MORE development/train (contamination there is a
feature, not a defect — the standing rule since ADR-0653), and none is
held-out-safe. This matches ADR-0762's and ADR-0830's finding for the
identical reason: every subject with real supply left is a subject some
published family already owns.

## The below-floor search

A full re-screen of every un-owned module with at least one surviving
candidate under the real `select()` logic (42 modules, replicating
`select()`'s per-record filter exactly rather than `propose`'s looser mirror)
found combinations tried and their real, measured verdicts:

    Mathlib.Data.Nat.{Fib.Basic,Int.Fib.Basic} combined (14 rows)
        -> R11 refused: topic Fib (published by BOTH v1 integer-fibonacci
           AND natural-fibonacci, train), vocab 10/10

    Mathlib.Data.Nat.{BinaryRec,Bits,Size} combined (19 rows)
        -> R9 CONTAMINATED 2/10 (Nat.bit_div_two, Nat.bit_false already
           declared) -- a hard guard failure, not a judgement call

    Mathlib.Data.Nat.BinaryRec + Mathlib.Tactic.IntervalCases +
    Mathlib.NumberTheory.SumTwoSquares (10 rows)
        -> R9 CONTAMINATED 3/10 (adds Nat.bit_true) -- BinaryRec's whole
           subject is Nat.bit, and Nat.bit is exhaustively developed natively
           (43 kernel declarations match the stem, including bit_true,
           bit_true_pos, bit_false, bit_false_le_bit_true, bit_mod_two,
           bit_div_two -- literally the decode lemmas this module's
           candidates restate)

    natural-factorization-structure: Factorization.{Basic,PrimePow},
    Factors, Multiplicity, Int.NatPrime, Choose.Sum, IntervalCases,
    Factorization.Induction, Factorial.BigOperators, GCDMonoid.Nat,
    Batteries.Data.Nat.Gcd (15 rows)
        -> R11 refused: topic Gcd/Choose (integer-gcd-algorithm,
           natural-gcd-algorithm, natural-binomial); vocab 8/10

    natural-number-theory-miscellany: NthRootLemmas, SumTwoSquares,
    IntervalCases, Prime.Infinite, PrimesCongruentOne, PrimeCounting,
    FactorisationProperties, FieldTheory.Finite.Basic (10 rows)
        -> R11 refused: topic Prime (natural-primes, natural-prime-arithmetic,
           natural-prime-characterizations); vocab 6/10 (Nat.Prime, Nat.ModEq,
           Nat.totient, Nat.Coprime all touched)

    Mathlib.Data.Nat.{Bits,Size} combined, alone (12 rows, take 10)
        -> R9 clean (0/10), R11 topic 0, R11 vocabulary 0/10 -- the ONLY
           mechanically clean below-floor combination found

`natural-bit-decode` (the Bits+Size combination) mechanically passes every
guard rule with only a `disclosure` requirement pending (ADR-0653's
environment-sweep signal, not a threshold): the "bit" stem's top hit is
`CReal.integralSplitArbitrary` — a false positive, "bit" is a substring of
"Arbitrary" and the two subjects share nothing. The "size" stem's hit is
genuine: `Nat.lt_pow_size`, `Nat.sizeAux`, `Nat.size_zero`, `Nat.size_aux_lt_pow`
are already declared, and together with the 43 `Nat.bit*` declarations above
they show this kernel has already built substantial native machinery for
exactly the primitive `Nat.bit`/`Nat.size` these ten rows restate lemmas
about, even though none of the ten candidate NAMES collides (R9 0/10) and no
published nursery family claims the TOPIC (R11 topic 0). This is the
`natural-square-root` precedent's shape (draw 8 found `Nat.sqrt`,
`Nat.sqrt_zero`, `Nat.sqrt_one` already declared and proceeded after
confirming none is a literal mirror of a drawn row) — but that precedent
still leaves a judgement call, and it does not by itself solve this draw:
**R5 requires at least two new held-out families**, and this is the only one
found.

## Decision

**Decline draw 10.** `FAMILY_MODULES`, `FAMILY_ROUTES`, both nursery
manifests, and every fact under `artifacts/facts/` are untouched by this ADR
except for one unrelated repair (below). No row moved partition, no
attestation count was raised, no held-out row was touched, and no marginal
family was forced through to manufacture a passing `--check`.

The reason is not "no candidate exists" — one does, mechanically clean. The
reason is that R5's two-family minimum cannot be met without either (a)
accepting a second family this search shows is genuinely R9-contaminated
(`natural-binary-recursion`, 3/10, a hard failure) or R11-refused (every
other combination tried), or (b) the construction-only route ADR-0762 and
ADR-0830 both already named. Building a construction (declaring `Nat.nthRoot`
or a comparable primitive in the Rust kernel) is Rust engineering work, not a
nursery screening edit, and is out of this lane's scope
(`gen-autogenesis-nursery-refill.py`'s two dicts, `artifacts/autogenesis/`,
new fact rows) — recorded here as the next lane's unblock, not attempted.

## An unrelated repair landed alongside this decline

`artifacts/autogenesis/nursery-v2-extension.json`'s own `extension_sha256`
did not match its body: commit `5f2664b5a` (a sibling lane extending the
nursery component-split gate) added a new top-level key,
`cross_population_component_split_exemptions`, directly to the committed
JSON without recomputing the digest through the generator's own `digest()`.
This blocked `gen-autogenesis-nursery-refill.py` entirely — `frozen_partitions()`
raises on load, before `select()`/`guard()` run at all — which would have
blocked ANY future draw, authored or declined. Confirmed by recomputation:
`digest(body without the new key)` reproduces the recorded hash exactly;
`digest(body with it)` does not. Fixed with a 1-line diff recomputing
`extension_sha256` against the current body; `check-autogenesis-nursery.py`
does not read `extension_sha256` and passes identically before and after.

**Residual, not fixed here:** `build_extension()` in
`gen-autogenesis-nursery-refill.py` does not know about
`cross_population_component_split_exemptions`, so a REAL (non-`--check`) run
of the generator would still overwrite the file and drop that key, and
`gen-autogenesis-nursery-refill.py --check` reports the file "stale" for this
reason, unrelated to this ADR's content. Not one of this lane's four required
gates; belongs to whoever extends that schema next.

## Consequences

- `check-dispatchable-frontier.py`, `check-autogenesis-nursery.py`,
  `check-autogenesis-holdout-isolation.py` and `validate-facts.py` all pass in
  the state this ADR leaves the tree in (21 dispatchable, `AUTOGENESIS_NURSERY_OK`
  + `AUTOGENESIS_NURSERY_CROSS_POPULATION_OK`, `held_out=136 ... PASS`, `2318
  facts checked, 0 errors`) — unchanged from before this lane started, because
  no draw was authored.
- **The below-floor un-owned held-out-safe supply is genuinely exhausted, not
  merely thin.** Every remaining un-owned module with `>=10` real (not
  proposer-estimated) survivors is R11-adjacent to a published
  development/train family. Every below-floor combination this lane could
  construct from the remaining ~40 tiny modules was either R9-contaminated
  (the `Nat.bit` primitive is exhaustively developed natively) or R11-refused
  (gcd/choose/prime/fib/modular-equivalence/totient vocabulary is
  unavoidable once the obviously-adjacent modules are excluded).
- The next draw needs one of: (1) ADR-0762's construction-only route
  (`Nat.nthRoot`, still unbuilt, still judged clean at the time it was
  screened), (2) a second construction alongside it, since R5 needs two new
  held-out families and one construction opens at most one, or (3) a
  genuinely new source of un-owned Mathlib modules — this lane's pinned
  inventory (`mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson`, 9,729
  records) is scoped to `Nat`/`Int`, and no wider inventory has been pinned.
- `Mathlib.Data.Nat.Bits` + `Mathlib.Data.Nat.Size` remain in the un-owned
  pool for a future lane that wants to accept the `natural-square-root`-style
  judgement call and pair it with a genuine second held-out family (from a
  construction or a wider inventory) rather than the two this lane found and
  rejected.

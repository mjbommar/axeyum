# Notes: 316-queue-sweep

Detail moved out of [`../status/316-queue-sweep.md`](../status/316-queue-sweep.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`docs/plan/status/287-nat-totient.md`, `291`, `295`, `301`, `313` are all
prior totient-family lanes. `301-totient-multiplicative.md` and
`313-totient-mult-finish.md` between them landed real machinery toward the
coprime multiplicative formula
(`Nat.totient_mul_of_coprime : Coprime m n → totient(m*n) = totient(m)*totient(n)`)
— `Nat.gcd_comm`, `Nat.coprime_mul_of_coprime`, `Nat.totient_coprime_totient_iff`
are all landed and axiom-free — and explicitly left the remaining piece
(`Nat.count_range_row_major`, `301`'s "Step 4") unbuilt, both for budget
reasons and because it is "the one genuinely novel induction."

**Even with `totient_mul_of_coprime` in hand, none of the three targets here
would close.** All three are stated for GENERAL `a, b` (not assumed
coprime). `totient_dvd_of_dvd` and `totient_gcd_mul_totient_mul` need the
formula applied to shared prime-power structure between `a` and `b` — i.e.
multiplicativity extended via a full prime-factorization / arithmetic-function
framework, which does not exist in this kernel (no `Nat.factorization`,
no general multiplicative-function machinery, no unique-factorization
induction). `eq_or_eq_of_totient_eq_totient` needs that plus a genuine
classification argument. `301` names this explicitly ("further work beyond
the coprime case") and neither prior lane attempted it. I did not either —
sizing it honestly, it is at minimum comparable to the entire `287`→`313`
totient effort again, not a same-session extension of it.

## Correction: `301`'s Step 4 ("`count_range_row_major`") is FALSE as stated, not merely unbuilt

`301` states the target

```
Nat.count_range_row_major : ∀ P Q m n,
  countRange (fun x => Bool.and (P (mod x m)) (Q (mod x n))) (mul m n)
    = mul (countRange P m) (countRange Q n)
```

and claims: "No coprimality hypothesis needed here at all — this is pure
counting combinatorics... verified numerically at several NON-coprime pairs
too, e.g. `(4,6)`: holds regardless" and separately "Numerically verified:
`count_range_row_major`'s conclusion checked directly... at every one of the
12 tested pairs plus two NON-coprime pairs `(4,6)`, `(6,9)`."

**This is wrong. I re-ran the actual identity (not the pointwise predicate
iff, which IS unconditionally true and is a different, weaker claim) at
`(4,6)` and `(6,9)` directly and it fails at both**, and at every one of the
26 non-coprime pairs `(m,n)` with `1 ≤ m,n ≤ 9`:

```
m=2 n=2  AND-count(mn)=2   product(m)*product(n)=1   totient(4)=2, totient(2)*totient(2)=1
m=4 n=6  AND-count(mn)=8   product=4                 totient(24)=8, totient(4)*totient(6)=4
m=6 n=9  AND-count(mn)=18  product=12                totient(54)=18, totient(6)*totient(9)=12
```

(`P`/`Q` taken as the actual totient predicates `gcd(·,m)=1`/`gcd(·,n)=1`,
matching what the assembly step would apply it to; the identity fails just
as badly for arbitrary `P`,`Q`, e.g. indicator functions.) The reason is
structural, not a fluke: the pointwise predicate identity (`301`'s Step 3,
`gcd(x,mn)=1 ↔ gcd(x mod m,m)=1 ∧ gcd(x mod n,n)=1`) IS true unconditionally
— it only uses the two shrink directions of coprimality, both true for any
`m,n` — but summing that pointwise-true predicate over `[0,mn)` and getting
a clean *product* of the two marginal counts requires the map
`x ↦ (x mod m, x mod n)` to be a **bijection** `[0,mn) → [0,m)×[0,n)`, which
holds **iff `gcd(m,n)=1`** (this is exactly CRT). Without it, some
`(residue mod m, residue mod n)` pairs are hit more than once and others
never — degenerately visible at `m=n=2`, where `x ↦ (x mod 2, x mod 2)` only
ever hits the diagonal.

So `301`'s own "Step 0" (the CRT bijection `g`, built from `nat_prelude/crt.rs`'s
`crt_unique` for injectivity plus `finite.rs`'s
`injective_on_imp_surjective_on` pigeonhole for surjectivity) — which that
doc explicitly says "turned out NOT to be needed" — **is in fact needed**,
and the row-major counting shortcut it was replaced with does not work. A
correct `count_range_row_major`-shaped lemma would have to either (a) carry
an explicit `Coprime m n` hypothesis and go through the bijection `g`
(reindexing `countRange` along a proven bijection, which is itself a lemma
this kernel does not yet have — "countRange is invariant under a bijective
reindexing of its domain" — a further building block), or (b) be abandoned
in favor of assembling `totient_mul_of_coprime` directly from the bijection
count without ever stating the row-major identity as a standalone,
coprimality-free lemma. Either way it is a materially larger and different
build than `301` sized it as, and I am not attempting it this session —
flagging it so the next lane does not spend a dispatch trying to prove a
false statement (a sound kernel cannot admit it, so time would be spent
constructing something impossible before the numeric check above would be
found, which is exactly what would have happened had I tried to build it
verbatim from `301`'s stated target).

I did not edit `301-totient-multiplicative.md` itself — per this repository's
own status-file convention, per-dispatch files are a historical record, not
a living document — this file is the correction of record; anyone building
on `301` should read this section first.

## Decision: all three targets declined this session

Not "structurally blocked by a divergence" (that registry category is for
mirrors where our definition and Mathlib's disagree) — these are
**correctly-stated mirrors of a construction our kernel does not yet have
the general theory to prove**, a different and normal reason to decline.
Left `open`, no evidence attached, `depends_on: []` unchanged (nothing to
derive against — no dependency proved this session).

## What would actually close them (for the next totient lane)

1. Fix `count_range_row_major` per the correction above (add `Coprime m n`,
   route through the CRT bijection `g`, build "countRange invariant under a
   domain bijection").
2. Assemble `Nat.totient_mul_of_coprime` (this closes nothing on the ledger
   by itself — no open fact states the coprime-restricted formula — but is
   the necessary base case for step 3).
3. Build a real multiplicative-function-over-prime-powers argument (or at
   minimum, strong induction on `Nat.minFac`-peeled factorizations) to lift
   step 2 to the *general* formula `totient_gcd_mul_totient_mul` needs.
   `totient_dvd_of_dvd` follows from that general formula at `gcd a b = a`.
4. `eq_or_eq_of_totient_eq_totient` needs a further classification argument
   on top of 3 (not merely the formula) — size it separately once 3 exists.

This is realistically several more dispatches, matching `287`→`313`'s own
pace on this family (5 lanes to land 3 lemmas plus this plan).

## Verification

No Rust file touched this session, so no kernel/prelude test run was needed
to validate a new declaration. Confirmed the tree is otherwise clean after
merging `main`:

- `python3 scripts/validate-facts.py` — 0 errors (fact count unchanged by
  this lane).
- `python3 scripts/check-mirror-statement-fidelity.py` — PASS.
- `python3 scripts/check-fact-depends-derived.py --fix` — `missing_edges=0`
  (nothing to fix; no fact flipped this session).
- `python3 scripts/check-test-attribute-integrity.py` — 0 findings.
- `cargo fmt --all --check` — clean.

## Commits (not pushed)

- This status file's own commit (the only change this lane makes).

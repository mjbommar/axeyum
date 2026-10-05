# Lane: first-supplementary-law

<!-- plan-section: lane-status -->

Status: **half landed** (2026-08-31). The non-residue direction is proved,
axiom-free. The residue direction is NOT, and the blocker is named precisely.

## What landed

| declaration | statement | footprint |
| --- | --- | --- |
| `Int.firstSupplementaryLawNotResidue` | `∀ m, PrimeCond (succ (mul 2 m)) → Nat.Odd m → Not (IsQuadraticResidue (ofNat (succ (mul 2 m))) (neg one))` | 0 |
| `Int.isQuadraticResidue_of_modEq` | `∀ n a b, ModEq n a b → IsQuadraticResidue n a → IsQuadraticResidue n b` | 0 |
| `Int.prodRange_split` | `∀ f a b, prodRange f (add a b) = prodRange f a * prodRange (fun k => f (add a k)) b` | 0 |

`crates/axeyum-lean-kernel/src/int_prelude/first_supplementary.rs`.
ADR-1230. Facts `F:int-firstsupplementarylawnotresidue` and
`F:int-isquadraticresidue-of-modeq` (plus the two Euler-criterion facts they
depend on, which were unregistered).

## The route, and the premise that was wrong

The brief pointed at the converse of Euler's criterion as the likely blocker.
It is the blocker for the OTHER half. What stood in the way of this half was
smaller and nobody had named it: **every quadratic-residue theorem in
`qr_criterion.rs` is stated over a NATURAL representative `ofNat aa` with
`0 < aa < pp`**, and `-1` is not a natural.

`Int.isQuadraticResidue_of_modEq` closes that — about 25 lines, the witness is
unchanged so it is `ModEq.trans` plus an `Exists` re-introduction. With it,
`Int.euler_criterion_neg_one_imp_not_residue` is applied at `aa := 2*m` and the
conclusion transported back to `-1`.

The hypothesis is `Nat.Odd m`, not `p mod 4 = 3`, for the reason the brief gave
and it held exactly: `Nat.Odd`'s witness EMITS `m = succ (k+k)`, from which
`Le 1 m` is `succ_le_succ (zero_le (k+k))` with no division anywhere.

## What remains, and the route sized

`p ≡ 1 (mod 4) ⟹ -1 IS a residue` needs a witness. **Wilson's theorem supplies
one and needs no converse**: `(p-1)! = (-1)^m (m!)^2`, so at even `m` Wilson
gives `(m!)^2 = -1 [p]` and `m!` is the witness outright. Verified at 94 and 44
primes respectively by the ADR's checks script.

Present already: `Int.wilson`, `Int.prodRange_permute` (the reversal),
`Int.modEq_prodRange_lt` (the pointwise congruence), and
`Int.prodRange_scaledIndexEqPowMulFactorial` at `a := -1` (collapses
`∏ (-1)·(k+1)` to `(-1)^m · m!` in one step).

The blocker that was missing — a `prodRange` SPLIT at a symbolic point —
**is now landed** (`Int.prodRange_split`, above). `prod.rs` peeled one front
term (`prodRange_shiftFront`) and one back term (`prodRange_succ`); neither cut
the range in two.
<!-- was-absent: Int.prodRange_split -- built by this same lane (ADR-1230). The
     sentence above is history, not a live claim; this marker is what lets
     check-absence-claims.py expire it rather than count it forever. -->

**The remaining blocker, checked rather than assumed: `InjectiveOn` and
`MapsInto` for the reflection `k -> sub (pred m) k` on `[0,m)`**, which
`Int.prodRange_permute` needs. Neither exists. `count_range_reversal.rs` is
about that exact reflection and does NOT go through a permutation — it runs its
own well-founded induction on the range length, so there is nothing to reuse
there.

What DOES exist: `transposition.rs`'s private `injective_of_involutive` ("any
involution is injective", three lines, generic). `k -> sub (pred m) k` is an
involution on `[0,m)`, so promote it rather than rebuilding.
`Nat.conjugate_injective` is the public form. `MapsInto` is the genuinely new
piece, and `Nat.sub`'s truncation is where it will bite.

## Verification

- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 63 passed, 0 failed.
- `python3 docs/research/09-decisions/adr-1230-first-supplementary-checks.py` —
  six claims over 94 odd primes, every control refuted.
- Eight mutations, both columns, none surviving: 4 kernel-rejected,
  4 test-caught. Table in ADR-1230.

Two of my own numeric claims were WRONG on first run and the checks script
caught both: `(p-1)! = (-1)^m (m!)^2` had the square dropped in transcription,
and "all three side conditions fail at `m = 0`" is false — `2m < p` is `0 < 1`
and holds. Both are corrected in the module doc and the fact `notes`.

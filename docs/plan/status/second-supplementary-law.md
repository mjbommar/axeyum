# Lane: second-supplementary-law -- the second supplementary law of quadratic reciprocity

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, second-supplementary-law, 2026-08-31).**

**Status:** complete (2026-08-31) — the second supplementary law of quadratic
reciprocity is proved, axiom-free, in its Legendre-symbol form.

## What landed

Three kernel declarations, **all admitted on the first attempt**, all with an
empty `Kernel::axiom_footprint` ([ADR-1150](../../research/09-decisions/adr-1150-the-second-supplementary-law-needed-a-double-parity-split-not-a-mod-8-one.md)):

| declaration | statement |
| --- | --- |
| `Int.secondSupplementaryLaw` | for an odd prime `p = 2m+1`: `2^m ≡ 1 (mod p)` exactly when `p ≡ ±1 (mod 8)`, `≡ −1` exactly when `p ≡ ±3 (mod 8)` |
| `Nat.half_ceil_parity` | the parity of `sub m (div m 2)` is decided by `m mod 4` |
| `Int.pow_neg_one_of_even` / `_of_odd` | `Nat.Even n → (−1)^n = 1`, `Nat.Odd n → (−1)^n = −1` |

Files: `crates/axeyum-lean-kernel/src/nat_prelude/half_ceil_parity.rs` (new),
`crates/axeyum-lean-kernel/src/int_prelude/second_supplementary.rs` (new).

Ledger: `F:int-secondsupplementarylaw`, `F:nat-half-ceil-parity`,
`F:int-pow-neg-one-of-even`, `F:int-pow-neg-one-of-odd`.

## The handoff's blocker did not exist

[ADR-1130](../../research/09-decisions/adr-1130-gauss-lemma-closes-and-the-handoffs-remaining-blockers-were-not-needed.md)
recorded this as blocked on "a `p mod 8` case split" that no module provided.
It is not needed, and **could not have been used if built**: `Nat.div`/`Nat.mod`
are stuck at a symbolic argument, so a mod-8 *hypothesis* would first have to be
turned back into a shape. `Nat.even_or_odd` runs the other way — it PRODUCES
`m = h+h` or `succ (h+h)` with the half computed — and applying it twice, at `m`
and then at `h := div m 2`, hands over all four classes with no division ever
reducing.

## Parity table (verified before any Rust, re-runnable)

```sh
python3 -c "
import collections
agg=collections.defaultdict(set)
for m in range(0,200):
    p=2*m+1; N=m-(m//2)
    agg[m%4].add((p%8, N%2))
for k in sorted(agg): print(k, sorted(agg[k]))
"
# 0 [(1, 0)]   1 [(3, 1)]   2 [(5, 1)]   3 [(7, 0)]
```

## Checks run

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 278 passed, 0 failed.
- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — 61 passed, 0 failed.
- `python3 scripts/validate-facts.py` — 2400 facts, 0 errors.
- `python3 scripts/check-settled-fact-statements.py` — PASS, 2214/2214 pinned.
- The registered `checker_command` was executed and shown to discriminate
  (prints `1`; exits 1 with a named error on a misspelled theorem).

## Not claimed

The classical `IsQuadraticResidue` form is **not** established. The `≡ −1` half
composes with `Int.euler_criterion_neg_one_imp_not_residue` to give "2 is not a
residue mod `p` for `p ≡ 3, 5 (mod 8)`" — one application, left to a caller. The
`≡ 1` half needs the converse of Euler's criterion; `qr_criterion.rs`'s recorded
gap is unchanged.

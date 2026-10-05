# Lane: nat-coprime-family — all nine `Nat.Coprime` mirrors closed

<!-- plan-section: lane-status -->

**DONE for this dispatch (`nat-coprime-family`, 2026-08-29).** All nine
target facts closed: `epistemic_status: proved`, `proof_route: kernel-lean`,
`axiom_footprint: []`.

## The task

```
F:ml430-nat-coprime-coprime-div-right-7a8ce438
F:ml430-nat-coprime-coprime-dvd-left-2ce391d2
F:ml430-nat-coprime-coprime-dvd-right-4a2670ae
F:ml430-nat-coprime-coprime-mul-left-fb5bd11a
F:ml430-nat-coprime-coprime-mul-left-right-910d7d8f
F:ml430-nat-coprime-coprime-mul-right-70e4e946
F:ml430-nat-coprime-coprime-mul-right-right-9599ecd3
F:ml430-nat-coprime-dvd-of-dvd-mul-left-b0608cb9
F:ml430-nat-coprime-dvd-of-dvd-mul-right-efc3a4ec
```

All nine mirror `Init.Data.Nat.Coprime` — Lean **core** (not mathlib4
itself). Confirmed by reading the pinned toolchain source directly:
`~/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Init/Data/Nat/Coprime.lean`.
`Nat.Coprime m n := gcd m n = 1` there, matching this prelude's own
convention (`rel_prime.rs`'s module doc: `Coprime` is never given a separate
name here, always spelled `gcd _ _ = one` inline) — so every mirror-flip
here is the honest kind (same definition, not a theorem about a different
one).

## Step 0 — two were already proved

`primes.rs`'s `Nat.coprime_of_dvd_left`/`Nat.coprime_of_dvd_right` (built
for an earlier, differently-named fact) state the IDENTICAL propositions as
`coprime-coprime-dvd-left`/`coprime-coprime-dvd-right` once `Coprime` is
unfolded — checked by comparing argument roles against the doc comment, not
by name. Closed as thin one-line wrappers under the Mathlib name rather than
aliases, to keep the one-fact-one-declaration correspondence the ledger's
checkers lean on.

## The other seven

New file `crates/axeyum-lean-kernel/src/nat_prelude/coprime_lemmas.rs`
(all nine declarations, one dispatcher `declare_coprime_lemmas`, called from
`build_nat_prelude` right after `declare_coprime_of_dvd_both`):

- **`coprime_mul_right`** / **`coprime_mul_right_right`**: `m ∣ (m*k)` /
  `n ∣ (n*k)` is `Nat.dvd_mul` DIRECTLY (no `mul_comm`), feeding
  `coprime_of_dvd_left`/`coprime_of_dvd_right`.
- **`coprime_mul_left`** / **`coprime_mul_left_right`**: same route, but
  need `m ∣ (k*m)` / `n ∣ (k*n)` — `dvd_mul` gives the OTHER factor order,
  so each transports along one `mul_comm` first.
- **`dvd_of_dvd_mul_left`**: `Nat.gauss_lemma` (`lcm.rs`) VERBATIM — same
  argument order, no rewriting at all.
- **`dvd_of_dvd_mul_right`**: `gauss_lemma` at `(k, n, m)`, with the
  hypothesis `dvd k (mul m n)` transported along `mul_comm m n` first (the
  lemma wants `dvd k (mul n m)`).
- **`coprime_div_right`**: the one genuine case split, on the divisor `a`
  (mirrors Lean core's own proof shape — `Coprime.coprime_div_right` there
  is `(cmn.symm.coprime_div_left dvd).symm`, itself case-split on `a` inside
  `coprime_div_left`). Built directly rather than via a `coprime_div_left` +
  double-`symm` detour, since `Coprime` here has no separate predicate to
  `.symm` on:
  - `a = 0`: `dvd 0 n` forces `n = 0` (`zero_mul` + `dvd_elim`'s witness),
    and `div _ 0 = 0` (`div_zero`) collapses `n` and `n/a` to the same
    value, so the hypothesis transports straight across.
  - `a = succ a'`: the witness `q` from `dvd a n` (`n = a*q`) recovers
    `div n a = q` via `div_mul_cancel_of_dvd` at the now-positive `a` — the
    same "exact factor divided back out" route `lcm_gcd_lemmas.rs`'s
    private `div_eq_of_mul_eq` uses (copied here per this crate's
    established per-file local-helper convention — see that file's own doc
    comment listing five other copies).

## The one bug, and how it was found

First attempt failed `the_nat_prelude_declares_no_axioms` with an opaque
`TypeMismatch` and no other signal (a bad declaration poisons the WHOLE
shared prelude build — CLAUDE.md's standing gotcha). Bisected by commenting
out each of the nine `declare_*` calls in `declare_coprime_lemmas` one at a
time against that single fast test, which isolated it to
`declare_coprime_div_right` (the other eight were clean on the first
attempt).

The bug: `div_eq_of_mul_eq(d, p, k, a, b, k_pos, mul_eq)` needs
`mul_eq : Eq (mul k a) b` (confirmed by reading its two existing call sites
in `lcm_gcd_lemmas.rs`, which pass an already-`symm`'d equation for exactly
this reason) — but `dvd_elim`'s continuation hands you `eq_proof : Eq b
(mul k a)`, the OPPOSITE direction. Fixed with one `d.symm` before the call.
This is the "swapped `symm` builds an unreversed term, surfacing only as an
opaque `TypeMismatch`" trap CLAUDE.md already names, from the other
direction (a MISSING `symm` rather than a swapped one).

## Verification

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
  nat_prelude::` — **170 passed, 0 failed** (169 baseline + 1 new). The new
  test, `coprime_div_right_applies_at_both_branches_of_its_case_split`,
  exercises BOTH branches of the case split concretely (`m=1,n=0,a=0` for
  the zero branch; `m=3,n=10,a=2` for the succ branch, with the conclusion's
  residue checked by `def_eq` against `Coprime 3 (div 10 2)` rather than
  merely "some `gcd _ = 1` type", so a wrong theorem that left `n`
  unchanged would be caught).
- `every_nat_declaration_is_checked_and_axiom_free` (the environment-derived
  coverage assertion) required adding all nine names to `theorem_names` —
  it fired on the first run after the build succeeded, exactly as designed.
- `the_build_is_deterministic`'s pin moved `93 + 538` -> `93 + 547` (9 new
  theorems), taken from the panic's own mismatch (640 vs 631), not
  hand-incremented.
- `rustfmt --edition 2024` (per-file, not workspace `cargo fmt`) on all
  three touched files; `cargo clippy -p axeyum-lean-kernel --all-targets --
  -D warnings` clean; `python3 scripts/check-test-attribute-integrity.py`:
  0 findings.

**Commits** (not pushed): `b71fffdf5` (the nine kernel declarations + test +
pin), `e6331e625` (the fact-ledger closures).

## Fact ledger

Each fact's `evidence` carries a `kernel-term` row
(`cargo test -p axeyum-lean-kernel --lib nat_prelude::`, plus
`every_nat_declaration_is_checked_and_axiom_free` by name) and an
`exhaustive-enumeration` axiom-freedom row discriminating on
`theorem_axiom_footprint`'s exact `nat<TAB>Name<TAB>0<TAB>` row — hand-
verified (`/usr/bin/grep -xFc`, ANSI-C-quoted literal tabs) that all nine
return count 1 on the real name and count 0 on a fabricated one, both in
the same script run.

`depends_on` populated by `scripts/check-fact-depends-derived.py --fix`
(24 edges from the proof terms' actual direct dependencies, not
hand-maintained) rather than by hand.

`python3 scripts/validate-facts.py`: 2074 facts, **0 errors**.

## Nothing left for this family

All nine targets closed; no further mirrors in `natural-coprime` remain
from this dispatch's list.

# Notes: 358-totient-dvd-chain

Detail moved out of [`../status/358-totient-dvd-chain.md`](../status/358-totient-dvd-chain.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Target 3 needed the SAME chain with the multiplier tracked, which is also
what the ADR said — but "track the multiplier" turned out to need a genuine
new lemma (`Nat.totient_mul_cofactor_bound`) with its own well-founded
induction and its own single-prime-step case analysis
(`single_prime_step_bound`, not published as a `Nat.*` declaration — an
internal helper), not merely "the same induction with a counter bolted on".
The ADR's one-paragraph sketch of the depth-≥2 argument (kprime = 2 forces
the next value even, ruling out the coprime-q=2 leaf) was directionally
right but under-specified: getting it to type-check needed a DIRECT
`Nat.dvd_mul_left` argument for the q=2 sub-case (bypassing
`coprime_or_dvd_of_prime`'s decision entirely, since we already know 2
divides `a*2`), not a re-use of the generic single-step helper with an
after-the-fact "impossible branch" argument. That refinement was found here,
not inherited from the ADR.

## The key construction bug this lane found and fixed (Target 1)

`ops.rs`'s `cases_zero_succ` (`Nat.rec` discarding the induction hypothesis)
is **not usable inside a well-founded fix's step function** when the proof
needs to invoke the outer `ih` at a value related back to the fix's own
bound variable. The plain `Nat.rec` case split hands back a proof for an
unrelated FRESH predecessor variable, with no equation connecting it to the
actual `x` the fix is stepping on — so `Lt kprime x` (what `ih` needs)
cannot be derived from facts built about the fresh predecessor. The fix is
`Nat.zero_or_succ` (`x = 0 ∨ ∃ p, x = succ p`), which hands back a genuine
equation naming `x`, transportable in both directions. `totient_dvd_chain.rs`'s
module doc explains this at the point it matters; recorded here too because
it will recur for any future well-founded-fix proof whose step needs both a
shape case-split AND the outer `ih`.

`Nat.totient_mul_cofactor_bound`'s induction did NOT need this device: its
family carries `Le two k` as an ordinary hypothesis (the `factorization.rs`
"guard arrow" pattern), so `k < 2` is handled vacuously and the well-founded
`x` variable is used directly, with no case split at all.

## Numeric checks, as re-executable commands

```sh
python3 scripts/tests/check-totient-dvd-chain-numerics.py   # 10 checks, 0 failed
```

Extends (does not replace) the two prior scripts, both re-run and still
green:

```sh
python3 scripts/tests/check-totient-prime-power-numerics.py   # 37 checks, 0 failed
python3 scripts/tests/check-totient-mul-coprime-numerics.py   # exit 0
```

Every positive check paired with a genuinely-failing negative control,
verified before writing any Rust:

| claim | check | control |
| --- | --- | --- |
| `totient a \| totient (a*k)` — no hypothesis at all | 1 | (unconditional; Target 1's whole point) |
| Target 1 itself | 2 | 2N — fails at 2634 non-dividing pairs |
| bound lemma: `k>=2 -> totient(a*k)>=2*totient(a) OR (k=2 AND equal)` | 3 | 3N — `k>=2` guard load-bearing, fails at every `a` when `k=1` |
| Target 3 itself | 4 | 4N-dvd (fails at 143 pairs), 4N-eq (fails at 161 pairs) |
| every `2a=b` witness has `a` odd | 5 | 0 even witnesses found |
| the second disjunct is reachable ONLY at cofactor `k=2` | 6 | observed `k` values: `[2]` |

One bug the script itself caught while writing it (not in the Rust): a
naive `a==0 or (...)` list comprehension made every `(0, b)` pair "bad"
regardless of `b`, because Python's `or` short-circuits on the first
disjunct. Fixed with a proper `divides(a, b)` helper (`a=0` divides only
`b=0`).

## Which closed, and why the other one (not assigned to this lane) still isn't

Both facts assigned to this lane closed. The third `natural-totient`
mirror ADR-0668 names, `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`
(`φ(gcd a b) · φ(a·b) = φ(a)·φ(b) · gcd a b`), was **not** part of this
lane's task and was **not touched** — it is a different, larger induction
(on `gcd(a,b)`, reducing via `Nat.gcd_mul_right` to a four-leaf `ε` truth
table) that the ADR sizes as its own separate piece of work.

## Debugging technique note (for whoever hits this next)

Every direction bug in `declare_totient_mul_cofactor_bound` (five of them:
a `symm` built with `a`/`b` swapped, an `and_intro` slot fed the un-symm'd
hypothesis, a missing `Or.inr` wrapper, a `transport` substituting the wrong
argument position of `Le`, and a `congr` built against the wrong-direction
equation) was found via a temporary `#[cfg(test)] mod debug_probe` calling
`Kernel::render_lean` on the `TypeMismatch { expected, got }` payload —
never by hand-tracing the construction to the end. Each fix was a one-line
correction once the exact mismatched pair was visible; hand-tracing alone
did not reliably predict which line was wrong even when the surrounding
reasoning was correct. The probe was removed before the final commit.

## Landed changes

| what | where |
| --- | --- |
| four theorems + private helpers | `crates/axeyum-lean-kernel/src/nat_prelude/totient_dvd_chain.rs` |
| names, docs, dispatch | `crates/axeyum-lean-kernel/src/nat_prelude.rs` |
| 4 tests + coverage list entries | `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` |
| 10 numeric checks | `scripts/tests/check-totient-dvd-chain-numerics.py` |
| two ledger facts flipped to `proved` | `artifacts/facts/F-ml430-nat-totient-dvd-of-dvd-9622e44a.json`, `artifacts/facts/F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7.json` |

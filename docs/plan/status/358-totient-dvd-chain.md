# Lane: totient-dvd-chain — both ADR-0668 divisibility mirrors closed

<!-- plan-section: lane-status -->

**DONE (`totient-dvd-chain`, 2026-08-30).** Both facts assigned to this lane
closed axiom-free, first attempt after fixing bugs found via
`Kernel::render_lean`-based debugging (never by hand-tracing to the end):

    F:ml430-nat-totient-dvd-of-dvd-9622e44a            a | b -> totient a | totient b
    F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7  a | b -> totient a = totient b
                                                          -> a = b \/ 2*a = b

Four new theorems landed in a new file `nat_prelude/totient_dvd_chain.rs`:

```text
Nat.totient_dvd_totient_mul     forall k a, Dvd (totient a) (totient (mul a k))
Nat.totient_dvd_of_dvd          Dvd a b -> Dvd (totient a) (totient b)
Nat.totient_mul_cofactor_bound  Le 1 (totient a) -> Le 2 k ->
                                 Or (Le (2*totient a) (totient (a*k)))
                                    (And (k=2) (totient (a*k) = totient a))
Nat.eq_or_eq_of_totient_eq_totient  Dvd a b -> totient a = totient b ->
                                     Or (a=b) (2*a=b)
```

`nat_prelude::` **206 passed, 0 failed** (202 baseline + 4 new tests).
`cargo fmt --all --check` clean (checked via `-p axeyum-lean-kernel`);
`clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean;
`validate-facts.py` **2265 facts, 0 errors**;
`scripts/check-fact-depends-derived.py --fix` applied cleanly to the second
fact (12 direct-lemma edges added).

## ADR-0668's claim: did "only the induction remains" hold?

**Yes, for Target 1 outright; yes for Target 3 with one addition ADR-0668
did not spell out precisely enough to skip verifying.**

Target 1 needed exactly what the ADR named: a well-founded induction on the
cofactor `k := b/a`, chaining `Nat.totient_dvd_totient_mul_prime` along a
prime peeled one at a time by `Nat.exists_prime_dvd`. No new number theory.

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

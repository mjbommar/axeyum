# ADR-1055: Number theory's row 3 becomes citable -- four facts, and a CRT independence gap found and fixed

Status: accepted
Date: 2026-08-31
Index-summary: ADR-1030 found `crates/axeyum-cas/src/ntheory_certify.rs` has four independently-checkable number-theory certificate routes (Pratt primality, compositeness, factorization, CRT) with ZERO facts naming them -- the same defect ADR-0875 found for EVT, recurring undetected. This ADR closes it: registers `F:cas-ntheory-pratt-primality-mersenne89`, `F:cas-ntheory-compositeness-certificate`, `F:cas-ntheory-factorization-certificate`, `F:cas-ntheory-crt-certificate`, each `cas-internal` (ADR-0601 SS2) with a `checker_command` proven to fail on broken input. Reviewing the module for independence also found a real gap: `check_crt_certificate`'s leastness and conflict guards called `ntheory::lcm`/`ntheory::gcd` directly, contradicting the module's own stated design and ADR-0745's claim that its arithmetic is independent of `ntheory`. Fixed before registration. Also corrects ADR-1030's count: it names six `check_*` functions in this module including `check_irreducible_certificate`/`check_irreducible_certificate_independent`; the current tree has exactly four, and no irreducibility-certificate function exists anywhere in `axeyum-cas` (confirmed by name grep and `git log -S` over the crate's whole history).
Lane: row3-citability

## Context

[ADR-1030](adr-1030-evt-is-conceded-number-theory-has-a-row-two-and-row-three-is-unciteable.md)
verified the Pareto-dominance argument for decidable subjects (ADR-0716 §4:
"one statement, one trust anchor, three artifacts -- the theorem, an
executable, and a certificate a third party re-derives") and found the third
artifact, row 3, unciteable everywhere it should carry the argument. For
number theory specifically:

> Row 3 is where the decidable-subject dominance argument is supposed to be
> **strongest** and is the row with the **least bookkeeping** behind it -- the
> certificates now exist in code for primality, factorization and CRT with
> **no fact naming them**.

Confirmed with a positive control in the same command:

```
crates/axeyum-cas/src/ntheory_certify.rs : 4 verify/check entry points
facts naming ntheory_certify            : 0
control -- facts naming verify_extremum_certificate : 3
```

This ADR closes that gap.

### Correcting ADR-1030's count

ADR-1030 states this module has **six** `check_*`/`verify_*` functions:
`check_primality_certificate`, `check_composite_certificate`,
`check_factorization_certificate`, `check_crt_certificate`,
`check_irreducible_certificate`, `check_irreducible_certificate_independent`.

Reading the module directly (`crates/axeyum-cas/src/ntheory_certify.rs`,
`^pub fn check_` / `^pub fn verify_`) finds exactly **four**:
`check_primality_certificate`, `check_composite_certificate`,
`check_factorization_certificate`, `check_crt_certificate`. No
`check_irreducible_certificate` exists anywhere in `axeyum-cas` -- neither by
exact-name grep across the crate nor by `git log -S check_irreducible_certificate
-- crates/axeyum-cas/` across the whole history of the file (empty result;
`ntheory_certify.rs`'s own history is four commits: the initial WIP, the
adversarial fixtures, the mutation-control test, and this ADR's independence
fix). `gfp.rs` has an unrelated `is_irreducible` (Rabin's test for
irreducibility over 𝔽ₚ, a PRODUCER with no independent checker), which may be
what was conflated with the two missing names.

This does not change ADR-1030's conclusion -- zero facts named any of them
either way -- but the four routes registered here are the complete current
set, not four of six. Filed per the standing rule that a document recording
obstacles or counts accumulates stale ones by construction (CLAUDE.md,
"THE LEMMA YOU NEED USUALLY EXISTS..." and the handoff-pessimism entry): verify
a cited measurement in the tree before building on it, including one this
project's own ADRs make.

## What each entry point verifies, and against what producer

Read directly from `crates/axeyum-cas/src/ntheory_certify.rs`. All four
checkers are pure `i128`/`u128` computation with no floating point.

1. **`check_primality_certificate(n, &PrattCertificate)`** -- Pratt (Lucas)
   primality. Producer: `certify_prime` (via `ntheory::is_prime` for the
   initial decision and `ntheory::factorize` for the `n-1` factor list, plus a
   bounded witness search). The checker re-derives, from `n` alone: the stated
   factors of `n-1` multiply to exactly `n-1` (completeness -- omitting one
   factor makes the test unsound, demonstrated by the module's own forged-91
   fixture), every factor base is itself Pratt-certified prime (recursively,
   through this SAME checker, not the producer), `witness^(n-1) = 1 (mod n)`,
   and `witness^((n-1)/q) != 1 (mod n)` for every factor base `q`. Its modular
   arithmetic (`mul_mod`/`pow_mod`) is written independently of
   `crate::ntheory`'s, on the stated principle that "a defect in a shared
   `mod_pow` would fool the producer and the checker identically" -- verified
   by grep: zero `ntheory::` calls inside `check_primality_certificate`'s body.
   **Fully independent as found; no fix needed.**

2. **`check_composite_certificate(n, &CompositeCertificate)`** -- a single
   divisor `d`. Producer: `certify_composite` (via `ntheory::factorize`). The
   checker is three inequalities and one modulus (`1 < d`, `d < n`,
   `n % d == 0`) with **zero** calls into `crate::ntheory` at all -- the
   simplest and most obviously independent of the four.
   **Fully independent as found; no fix needed.**

3. **`check_factorization_certificate(n, &FactorizationCertificate)`** --
   canonical prime factorization. Producer: `certify_factorization` (via
   `ntheory::factorize`, plus `certify_prime` per factor). The checker
   re-derives the ascending-bases/positive-exponent guards and the product
   identity `prod(base^exp) = |n|` directly, and re-certifies each base's
   primality via `check_primality_certificate` (the CHECKER) rather than
   trusting the producer's own factor list or calling `certify_prime` (the
   PRODUCER) -- verified by reading the F5 guard. **Fully independent as
   found; no fix needed.**

4. **`check_crt_certificate(residues, &CrtCertificate)`** -- CRT, both
   directions (a `Solution{solution, modulus}` or an `Inconsistent{left,
   right}`). Producer: `certify_crt` (via `ntheory::crt`, an incremental
   pairwise merge through `ntheory::extended_gcd`). **NOT fully independent as
   found -- see below.**

## The CRT independence gap, found and fixed

`check_crt_certificate`'s R4 guard (the certified `modulus` must be the LEAST
common multiple of the input moduli, not merely a common one -- the module's
own adversarial fixture demonstrates a common-multiple-but-not-least forgery
that only this guard rejects) and its R6 guard (a claimed conflict between two
congruences is real) called `ntheory::lcm(acc, m)` and
`ntheory::gcd(m_left, m_right)` directly:

```rust
// R4, as found:
let Some(next) = ntheory::lcm(acc, m) else { return false; };
// R6, as found:
let common = ntheory::gcd(m_left, m_right);
```

This is correct arithmetic, and it is not independent of the crate this
checker exists to check. It contradicts two things directly:

- This module's own stated design principle, at the top of the file: "Written
  here rather than reused from `ntheory` on purpose: a defect in a shared
  `mod_pow` would fool the producer and the checker identically" -- true for
  `mod_pow`/`mul_mod`/`add_mod`, not extended to `gcd`/`lcm`.
- [ADR-0745](adr-0745-number-theory-certificates-are-cas-internal-and-adversarially-gated.md)'s
  explicit claim: "**4. The modulus must be the LEAST common multiple**... The
  modular arithmetic is this module's own, not `ntheory`'s." As written, that
  claim did not in fact cover `gcd`/`lcm`.

Note what this gap is NOT: `ntheory::crt` (the CRT *producer*) does not call
`ntheory::gcd`/`ntheory::lcm` either -- it uses `ntheory::extended_gcd`, a
separate implementation. So the checker was not literally sharing code with
its own producer function; it was sharing code with a DIFFERENT function in
the same untrusted crate, which is the weaker but still real form of the
defect this module's design principle exists to prevent.

**Fix** (landed in this lane before any fact was registered, commit
`43e598ead`): added `checker_gcd`/`checker_lcm` -- a from-scratch Euclidean
algorithm, independent of `crate::ntheory::gcd`/`crate::ntheory::lcm` -- and
routed R4 and R6 through them instead. Added
`ntheory_certify_tests::independent_gcd_lcm_agree_with_ntheory` (72
comparisons across eight `a` values times nine `b` values, including
`i128::MAX`-adjacent primes), mirroring the module's existing
`independent_modular_exponentiation_agrees_with_ntheory` discipline for
`pow_mod`. Bumped `scripts/check-ntheory-certificates.sh`'s ratchet 33 -> 34.

Re-ran the module's adversarial mutation sweep
(`scripts/tests/test-ntheory-certificate-guards.sh`) after the fix: R4 and R6
are each still killed by their existing forgery fixtures
(`forged_crt_modulus_is_a_common_multiple_but_not_the_least`;
`forged_crt_rejects_a_fabricated_conflict_over_a_solvable_system` +
`forged_crt_rejects_out_of_range_conflict_indices`), `measured=23 survivors=3`
unchanged (G1/G5/G10, the three documented resource guards). The fix changes
where the arithmetic comes from, not what the checker accepts or rejects.

### A mutation of `checker_gcd` hung rather than failing cleanly, and that is informative

While proving the new `independent_gcd_lcm_agree_with_ntheory` checker_command
can fail (see below), the first attempted break -- changing the Euclidean
step from `a % b` to `a / b` -- did not produce a clean assertion failure. It
hung: `checker_gcd(1, 1)` under that mutation computes `t = 1/1 = 1`, leaving
`(a, b) = (1, 1)` unchanged forever, an infinite loop. `(1, 1)` is the first
pair the test's nested loop tries (`1` is the smallest value in both the `a`
and `b` lists). The run was stopped (`TaskStop` on the backgrounded task
after it exceeded the 120s foreground timeout), the source reverted, and no
orphaned process remained (`ps` swept for reparented high-CPU processes,
per CLAUDE.md's orphaned-task entry, found none). The break used to
demonstrate this checker_command's evidence row instead mutates the test's own
pinned comparison count (72 -> 71), which fails cleanly (exit 1, 0 matches) --
see the break/restore log below.

This is not a defect in the shipped `checker_gcd` (which is the standard,
terminating Euclidean algorithm using `%`) -- it is a property of the
*mutation* used to probe it, and it is worth recording because it is a
concrete instance of a general hazard: proving a checker "can fail" by
mutating PRODUCTION arithmetic rather than the TEST's own assertions risks a
mutation that does not terminate rather than one that fails loudly. Preferred
technique for future breaks in this style: mutate the pinned expected value in
the test itself first; only mutate production arithmetic if that is
insufficient to demonstrate discriminating power, and be ready to stop a
hung run rather than wait on it.

## The four facts registered

- `F:cas-ntheory-pratt-primality-mersenne89` -- 2^89-1 (a 27-digit Mersenne
  prime, beyond `u64::MAX`) is prime, via the Pratt route. Two evidence rows:
  the single large instance (`certifies_a_prime_beyond_u64_max`), and breadth
  across the 95 primes below 500 (`certificate_route_agrees_with_is_prime_over_a_dense_range`,
  a pinned nonvacuous count).
- `F:cas-ntheory-compositeness-certificate` -- five composites including 561,
  the smallest Carmichael number (chosen to show this checker is a plain
  divisibility check, structurally immune to the Carmichael failure mode that
  defeats a bare Fermat test), and seven correctly-declined non-composites.
- `F:cas-ntheory-factorization-certificate` -- eight instances including
  negatives, units, and a large-prime-times-two; `n=0` correctly declined.
  `depends_on: [F:cas-ntheory-pratt-primality-mersenne89]` because its
  per-factor primality guard IS that fact's checker.
- `F:cas-ntheory-crt-certificate` -- four solvable systems (including a
  non-coprime-moduli case exercising the leastness guard) and two unsolvable
  systems, both directions independently re-checked; a second evidence row for
  the `checker_gcd`/`checker_lcm` agreement test added by the fix above.

All four: `proof_route: "cas-certificate"`, `formal.kernel_theorem: null`
(explicitly -- no kernel involvement of any kind, per ADR-0601's trust-anchor
taxonomy these are producer/checker pairs entirely outside it), classified
`cas-internal` by `scripts/validate-facts.py`'s
`classify_cas_certificate_checker` (every `checker_command` names only
`axeyum-cas`, never `axeyum-lean-kernel`) -- consistent with this module's own
doc, which labels itself `cas-internal` and explains why: a kernel
reconstruction of, say, `n = d*e` over the unary-numeral `Nat` prelude would be
an `Eq.refl`-shaped, substance-free reconstruction (the trap
`scripts/check-cas-substance.py` exists to catch for `cas-certificate` facts
that DO reconstruct), and it would hit the measured unary-numeral cost wall
documented in CLAUDE.md.

None of the four facts claims that `ntheory::is_prime` (Miller-Rabin),
`ntheory::factorize`, or `ntheory::crt` are themselves proved correct as
general decision procedures. Each claims only that the SPECIFIC instance
checked carries a certificate a checker sharing no code with the search
re-derives from scratch -- ADR-0603 row 3, decidable-fragment exact form, one
instance at a time. This is the same discipline ADR-0745 established at
landing time; this ADR just makes it citable.

## Proof that each checker_command can fail

Required per this lane's brief: "a `checker_command` nobody has watched fail
is not evidence." For each of the four primary tests (and the two supporting
tests), the relevant assertion was flipped or its pinned count decremented by
one, the exact `checker_command` from the fact was re-run confirming `grep -c`
returns `0` (pipeline exit `1`), then the edit was reverted and confirmed
byte-identical to `HEAD` via `git diff --stat` (empty output):

| test | break | result |
|---|---|---|
| `certifies_a_prime_beyond_u64_max` | `assert!(check_...)` -> `assert!(!check_...)` | 0 matches, exit 1 |
| `certificate_route_agrees_with_is_prime_over_a_dense_range` | pinned count 95 -> 94 | 0 matches, exit 1 |
| `certifies_composites_and_declines_primes` | `assert!(check_...)` -> `assert!(!check_...)` | 0 matches, exit 1 |
| `certifies_factorizations_including_negatives_and_units` | `assert!(check_...)` -> `assert!(!check_...)` | 0 matches, exit 1 |
| `certifies_crt_in_both_directions` | `assert!(check_...)` -> `assert!(!check_...)` (solvable leg) | 0 matches, exit 1 |
| `independent_gcd_lcm_agree_with_ntheory` | pinned count 72 -> 71 (after the `a/b` mutation above hung and was abandoned) | 0 matches, exit 1 |

After each break/restore, `cargo test -p axeyum-cas --lib ntheory_certify::`
was re-run to confirm the full 34/34 pass and `git status --porcelain` /
`git diff --stat` showed no residual change to the two source files before the
next break.

## Consequences

Row 3 for number theory has four citable facts where it had zero. It is still
not the whole of `ntheory_certify.rs`'s surface, and it is not the whole of
row 3 for number theory: `legendre_symbol`, `jacobi_symbol`, `euler_phi`,
`mod_inverse`, `divisor_sigma` and the rest of `ntheory.rs`/
`ntheory_advanced.rs` remain bare computation with no certificate at all (per
ADR-0745's own "Alternatives considered", deferred rather than rejected). So
"number theory has row 3" is defensible for exactly the four routes this ADR
names, not for the subject.

## References

- ADR-0601 -- three producers, one trust anchor
- ADR-0603 -- classical theorems land as graded statement families
- ADR-0745 -- number-theory certificates are cas-internal, and adversarially gated
- ADR-1030 -- EVT is conceded; number theory has a row 2; row 3 is unciteable
- `crates/axeyum-cas/src/ntheory_certify.rs`
- `scripts/check-ntheory-certificates.sh`,
  `scripts/tests/test-ntheory-certificate-guards.sh`

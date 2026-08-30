# ADR-0745: Number-theory certificates are `cas-internal`, and adversarially gated

Status: accepted
Date: 2026-08-30
Index-summary: Classical number theory gets independently re-derivable
certificates for primality (Pratt), compositeness, factorization and CRT —
measured against a crate where `ntheory.rs` and `ntheory_advanced.rs` carried
**0** verifiers between them across 68 functions, with `taylor.rs` at 8 and
`mvt.rs` at 9 as controls. Honestly labeled `cas-internal`: nothing
reconstructs through the kernel, because over unary numerals it would be the
`refl`-shaped reconstruction the substance gate exists to reject. Gated by
adversarial forgeries — a certificate that **91 is prime** passing every guard
but completeness, and a CRT modulus that is a common multiple but not the
least, over a **solvable** system. A 23-guard mutation sweep found three
provably-redundant guards nobody predicted.
Lane: `nt-certificates`

## Context

ADR-0716 and the accompanying curriculum analysis established something this
programme had not previously asked: what ADR-0603's **row 2** — the boundary
refutation — is in a subject that is decidable. The answer, measured rather
than argued, is that row 2 is *provably empty* for ℕ, ℤ and ℚ. The decision
principle each analysis row 2 extracts is already a proved, axiom-free theorem
there (`Nat.le_total`, `Int.le_total`, `Rat.le_total`, against `CReal.le_total`
absent). The one boundary that survives — the unrestricted least-number
principle — was then shown interderivable with excluded middle.

The consequence is structural: **for the rest of number theory, dominance
cannot come from row 2. It has to come from rows 1 + 3 — a statement, an
executable, and a re-derivable certificate.** That analysis then measured the
row-3 obligation and found it unmet.

I re-measured that claim rather than inheriting it, with positive controls in
the same command (GNU `grep`, not the interactive `ugrep`):

| file | `verify_`/`check_` fns | plain `fn`s |
| --- | --- | --- |
| `crates/axeyum-cas/src/ntheory.rs` | **0** | 39 |
| `crates/axeyum-cas/src/ntheory_advanced.rs` | **0** | 29 |
| `crates/axeyum-cas/src/taylor.rs` (control) | 8 | — |
| `crates/axeyum-cas/src/mvt.rs` (control) | 9 | — |

So the gap is real and it is total: 68 number-theoretic functions, zero
verifiers, in a crate whose analysis modules carry 8–9 apiece. `is_prime`,
`factorize`, `crt`, `legendre_symbol` compute and do not justify.

The shape that already qualifies, and therefore the model, is
`axeyum_solver::lia_gcd::check_diophantine_certificate`: a plain data struct, a
checker that re-derives from the **original** question, sharing no code path
with the elimination that produced the certificate.

## Decision

Add `crates/axeyum-cas/src/ntheory_certify.rs`: four certificate types with
four independent checkers, plus self-checking producers.

**1. The prime/composite asymmetry is kept explicit, never blurred.** They are
separate types with separate checkers:

- `CompositeCertificate` — a divisor `d` with `1 < d < n`. One division.
- `PrattCertificate` — the recursive Lucas test: a witness of multiplicative
  order exactly `n − 1`, which needs the *complete* prime factorization of
  `n − 1`, which needs a recursive certificate per factor base.

**2. `FactorizationCertificate`** carries the `(prime, exponent)` list plus a
Pratt certificate per base. The checker establishes both halves: the product
identity `∏ base^exp = |n|`, and the primality of every base. Strict ascending
order makes it a certificate for *the* factorization rather than *a* product of
primes. `n = 0` is never certifiable — the empty product is 1 and no finite
product of primes is 0.

**3. `CrtCertificate`** is an enum over the two directions the producer
distinguishes: a `Solution { solution, modulus }` where `modulus` must be the
**least** common multiple, or an `Inconsistent { left, right }` naming a
conflicting pair.

**4. The modular arithmetic is this module's own**, not `ntheory`'s. A defect
in a shared `mod_pow` would fool producer and checker identically, which is the
one failure an independent checker exists to rule out. Agreement with
`ntheory::mod_pow` is *tested* at 150 points including modulus `i128::MAX`,
which locates a divergence rather than letting a shared bug hide behind it.

### Trust anchor: `cas-internal`, deliberately

Per ADR-0601, CAS evidence must reconstruct through `Kernel::add_declaration`
or be visibly labeled. **Nothing here reconstructs, and that is the honest
call, not a shortfall.** A kernel reconstruction of `n = d · e` over the
unary-numeral `Nat` prelude would be an `Eq.refl` on a numeral tower — exactly
the `refl`-shaped, substance-free reconstruction `scripts/check-cas-substance.py`
exists to catch, and it would also hit the measured unary-numeral cost wall
(`gcd 512 1875` alone is 25.6 s). Adding a fifteenth reconstruction of that
kind would inflate a counter and establish nothing. The module doc says
`cas-internal` in its own words.

## Adversarial fixtures, not mutation testing, decide the format

The `nra_monomial_bound_cert` retrospective is the governing precedent: nine
guards there were each killed by exactly one test and the module was still
unsound, because the certificate did not *record* a distinction the producer
made. Mutation deletes guards that exist; it cannot find a guard never written.

So for every case the producer distinguishes there is a forgery over a
**true/satisfiable** instance in which every other guard passes. Every
forgery's numbers were verified in Python **before** any Rust — a rule this
repository adopted after a traced plan's "verified numerically" turned out
false at 26 of 26 test points.

Two are worth stating in full because they are the ones that could not exist if
the format were weaker:

**A forged certificate that 91 is prime.** `91 = 7 · 13`. Witness `3` has order
`6` mod `91`, so `3^90 ≡ 1` and `3^45 ≢ 1` — the Fermat check passes, the order
check passes, and the single claimed factor `2` is genuinely prime so the
recursion passes. **Only the completeness requirement `∏ base^exp = n − 1`
(`2 ≠ 90`) rejects it.** A Pratt certificate that recorded a *subset* of the
prime factors of `n − 1` — which is the natural thing to record, since that is
what the order checks consume — would accept a proof that a composite is prime.

**A forged CRT certificate over a solvable system.** `x ≡ 1 (mod 4),
x ≡ 3 (mod 6)` really has solution `9 mod 12`. The certificate
`(solution = 9, modulus = 24)` satisfies both congruences, is canonical in
`0..24`, and `24` *is* a common multiple of `4` and `6`. **Only leastness
rejects it.** A certificate recording "a common multiple" could not express the
distinction at all — the impossibility of writing that fixture would have been
the finding.

Also: a forged certificate that **15** is prime whose claimed factorization
`[(14, 1)]` multiplies to exactly `n − 1` and whose witness passes both order
checks, rejected only by the recursion refusing to accept `14` as prime.

## Consequences

### The row-1 + row-3 claim, stated precisely

Four routines now have rows 1 + 3 complete — a statement, an executable, and a
certificate an independent checker re-derives: **primality (both directions),
factorization, and CRT (both directions).** For those four the sentence
"number theory dominates on rows 1 + 3" is now defensible.

It remains **false** for the rest of `ntheory.rs` and all of
`ntheory_advanced.rs`. Of 68 functions across the two files, this ADR certifies
**4**. `legendre_symbol`, `jacobi_symbol`, `euler_phi`, `mod_inverse`,
`divisor_sigma` and the remainder are still bare computation. The honest
summary is *four routines, not a subject*.

Note also what a Pratt certificate does and does not remove. `is_prime` is
deterministic Miller-Rabin over a fixed witness set whose correctness rests on
an external literature result about that base set — unverifiable per call. The
Pratt route replaces that with a per-instance proof checkable from modular
exponentiation alone. That is a genuine strengthening of the *evidence*, not a
change of verdict: the two agree on every `n` in `2..500` (95 certified primes,
count pinned so a vacuous run cannot pass).

### Three guards are provably redundant, and the sweep found all three

`scripts/tests/test-ntheory-certificate-guards.sh` deletes each of 23 guards in
turn. Result: `measured=23 survivors=3 not_measured=0`. Twenty verdict-bearing
guards are each killed by at least one fixture (sixteen by one, four by two).

The three survivors — G1 (subject range), G5 (exponent and base bounds), G10
(recursion depth) — were **not predicted**; the sweep found them. Each provably
cannot change a verdict:

- **G1**: every `n < 2` is already excluded arithmetically — for `n ≤ 0` the
  `u128::try_from(n − 1)` fails, and for `n = 1` the target is `0` while a
  product of bases `≥ 2` is never `0`.
- **G5**: zero exponents are refuted by G9 and sub-two bases by G7. G5 alone
  bounds `checked_prod_pow`, which spins up to 4.29 × 10⁹ times at base 0 or 1.
- **G10**: a chain deep enough to matter is refuted by G8/G9 at the top level
  either way; the bound only stops the recursion exhausting the stack first.

All three are **retained**: a guard only ever rejects more, never less, so it
cannot make the checker accept a forgery. What is not acceptable is leaving the
redundancy implied, because an unkillable guard reads as coverage it does not
provide. Each is documented at its site and pinned in `EXPECTED_SURVIVORS` with
a **two-way** assertion — a new survivor fails the sweep, and an expected
survivor that *starts* dying also fails, since that means the reasoning went
stale.

The sweep also corrected a comment written confidently and wrongly:
`forged_primality_rejects_a_zero_exponent_entry` does **not** kill G5, it kills
G9. The guard a test appears to exercise and the guard it kills are different
questions, and only the sweep separates them.

And it caught itself twice before passing. Two mutation patterns matched in two
places each (the checker's guard and the producer's lookalike precondition), so
two guards were silently `NOT MEASURED` while the run still read as orderly.
Both source sites were reworded to be uniquely addressable. That the harness
has failed on real conditions, twice, is better evidence it can fail than a
synthetic control.

### Gating

`scripts/check-ntheory-certificates.sh` runs the fixture suite and asserts a
**ratcheted nonzero** count (floor 33) — a bare `cargo test --lib <filter>`
exits 0 when the filter matches nothing, which is the inert-gate shape this
repository has shipped before. Verified both directions: floor 33 passes at 33,
floor 999 exits 1. Registered in **both** `scripts/check.sh` and the
`justfile`; `check-aggregate-scope.sh` remains green at 64 recorded
divergences, confirming the registration is two-sided.

The mutation sweep runs ~23 incremental builds and is deliberately **not** in
the aggregate chain; run it whenever a guard is added, removed or reworded.

## Alternatives considered

**Kernel-reconstruct the compositeness certificate.** `n = d · e` is one
`Nat.mul` evaluation. Rejected: over unary numerals it is both a `refl`-shaped
reconstruction the substance gate exists to reject, and measurably expensive.
Labeling honestly is what ADR-0601 actually asks for.

**Certify `legendre_symbol` / `jacobi_symbol` too.** Deferred rather than
rejected. Euler's criterion gives a checkable route for the Legendre symbol at
a certified prime, and the Jacobi symbol reduces to a certified factorization —
both are natural next increments now that `PrattCertificate` exists. Claiming
them here without building them is what this ADR's own row-3 measurement
criticises.

## References

- ADR-0601 — three producers, one trust anchor
- ADR-0603 — classical theorems land as graded statement families
- ADR-0716 — graded statement families in number theory and linear algebra
- `crates/axeyum-solver/src/lia_gcd.rs` — the certificate shape this follows
- `docs/research/11-design-review/` — the `nra_monomial_bound_cert`
  retrospective on why mutation testing cannot find a missing distinction

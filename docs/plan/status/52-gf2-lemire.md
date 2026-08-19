# Lane: gf2-lemire — half-degree irreducibles and finite-field evidence

<!-- plan-section: lane-status -->

**The Lemire half-degree conjecture is an active CAS/evidence lane** (`WIP`,
gf2-lemire, 2026-08-18).  The exact target is the paper's non-strict bound
`deg(f-x^n) <= floor(n/2)`; the strict social-post wording fails at degree 2.
The existing general-prime-field code has no limits or evidence consumer and
takes about 6.45 seconds in release for the known degree-400 witness.

ADR-0480 is accepted and `81321fc65` lands the CAS-local, bit-packed
`GF(2)[x]` value layer with explicit resource limits and portable
Frobenius/Bezout irreducibility certificates before any finite-field IR or SMT
surface.  Exhaustive monic inputs through degree 10 agree with both the old
general-field test and independent trial division; the warmed release
producer-plus-checker regression for degree 400 is below 10 ms.  The reciprocal
lemma reduces the universal conjecture to a prime polynomial in the identity
class modulo `x^ceil(n/2)`.  The current mathematical blocker is a positivity
theorem at that exact fixed-field half-degree boundary. The exact integral
Hayes-class recurrence has now been specialized and independently matched to
direct counts through degree 20; its error has varying sign, so the remaining
target is aggregate cancellation rather than a termwise sign argument.
`fd1e8793b` adds an exact two-prime NTT/CRT oracle for that aggregate, and
`4b129601c` scales its fail-closed control range through `ell=22`. It identifies
the sufficient candidate lemma
`abs(N_n(1)-2^(n-ell)) <= 2^ell` at `n=2 ell+1, 2 ell+2` and verifies it only
through `ell=22`; the result is a finite proof target, not universal credit.
The same increment derives the exact family-norm degree
`(ell-2)2^ell+2`, showing that character-by-character Weil bounds necessarily
lose a factor asymptotic to `ell`; the missing proof must establish aggregate
family cancellation. An optimized exact `ell=22` replay on s7 matched every
control in 8m27s with 2.38 GB peak RSS and exit 0.

`1ff1ca6b7` closes the machinery gap exposed by that experiment. Accepted
ADR-0482 extracts a public, bounded `axeyum_cas::gf2_hayes` API for the
principal-unit cyclic decomposition, exact identity-class populations,
endpoint discrepancies, conductor layers, and exact bignum checking of the
conditional sufficient-bound implication. The transform now admits `ell`,
degree, group-order, and retained-table-cell limits before allocation. A Rust
checker and algebraically separate Python checker both prove that the explicit
target `8 j^12 2^((n+j)/2)` would finish the endpoint argument from `ell=194`,
with the certified degree-400 range covering the remainder; neither checker
claims that target itself. No SMT or finite-field IR surface was added because
there is no solver/model/proof consumer for the missing analytic family bound.
Independent C++ and refactored Rust transforms agree at `ell=23` on endpoint
discrepancies `57574` and `-88336`; the Rust replay completed in 20m23s with
4.96 GB peak RSS and exit 0.

The portable boundary is complete for bounded witnesses. `98f2d953f` adds
canonical JSON, a dense-coefficient second checker, and a standalone dual-check
CLI; `b678ec7e6` adds the fail-closed producer. `3718aab11` commits and gates the
188,458-byte degree-400 certificate (SHA-256 `30ae3f33...383d5`) from both
aggregate check paths.

`6e1372073` adds deterministic sparse shards and exact population checking.
Five single-threaded jobs on s1/s4/s5/s6/s7 produced 400/400 found receipts with
no exhaustion or candidate limit. `d308c7bc1` admits and gates every child:
227 trinomials, 172 pentanomials, degree-one `x`, 38,679 candidates total, and a
maximum of 870 at degree 349. This establishes the finite range `1..=400` under
both implemented checkers, not the universal theorem. `6aff45e82` records that
bounded proposition in the fact ledger using the accepted ADR-0481
`certificate-spec` language. Its canonical proposition is bound to the range
checker and has mutation controls; it creates no finite-field SMT, CAS-identity,
or kernel surface and gives the universal conjecture no credit.

**Next.** Prove a genuinely positive aggregate bound for the identity
principal-unit class at degrees `2 ell+1` and `2 ell+2` (where `ell` is the
number of prescribed zero coefficients), or find a universal construction.
Then reconstruct reciprocity and the central lemma through the kernel before
promoting the finite ledger fact or claiming a universal proof.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `1ff1ca6b7` | Extracted bounded reusable Hayes/principal-unit/conductor CAS APIs, dual-checked the conditional sufficient-bound arithmetic, retained the missing cancellation lemma as an explicit obligation, and independently reproduced `ell=23`. |
| 2026-08-18 | `4b129601c` | Extended the exact NTT/CRT endpoint oracle through `ell=22`, added an a-priori CRT uniqueness guard, reduced peak memory, and isolated the family-norm cancellation factor that the universal proof must recover. |
| 2026-08-18 | `6aff45e82` | Added accepted ADR-0481 and a canonical, mutation-checked certificate-spec fact for the dual-replayed degree-1-through-400 result without inventing finite-field SMT or kernel support. |
| 2026-08-18 | `30a004188` | Audited the tempting Hsu half-coefficient survey claim against the explicit bound and the 2023 Gao follow-up; neither supplies positivity at the exact fixed-`GF(2)` endpoint. |
| 2026-08-18 | `fd1e8793b` | Added an exact finite principal-unit Fourier oracle using two NTT primes and CRT, verified the sufficient endpoint-discrepancy candidate through `ell=18`, and kept the candidate explicitly outside the theorem and fact ledger. |
| 2026-08-18 | `d32ebbdb1` | Corrected the half-boundary parameterization, derived the exact integral Hayes recurrence, and gated its identity-class counts against an independent direct Rabin enumeration through degree 20. |
| 2026-08-18 | `6e1372073` `d308c7bc1` | Added deterministic content-bound search shards; five hosts produced and the repository admitted 400/400 dual-checked degrees, with finite-range credit explicitly separated from the universal conjecture. |
| 2026-08-18 | `98f2d953f` `b678ec7e6` `3718aab11` | Added canonical bounded artifacts, an algebraically separate dense checker, standalone producer/checker CLIs, and the dual-gated degree-400 witness; completion does not claim the universal theorem. |
| 2026-08-18 | `81321fc65` | Added bounded bit-packed `GF(2)[x]`, untrusted Rabin certificate production, independent identity checking, exhaustive degree-10 oracle agreement, certificate mutations, the exact Lemire theorem contract, and accepted ADR-0480. |

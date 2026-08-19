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
both implemented checkers, not the universal theorem.

**Next.** Prove a genuinely positive aggregate bound for the identity
principal-unit class at degrees `2 ell+1` and `2 ell+2` (where `ell` is the
number of prescribed zero coefficients), or find a universal construction.
Then reconstruct reciprocity and the central lemma through the kernel and fact
ledger before claiming a universal proof.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `30a004188` | Audited the tempting Hsu half-coefficient survey claim against the explicit bound and the 2023 Gao follow-up; neither supplies positivity at the exact fixed-`GF(2)` endpoint. |
| 2026-08-18 | `d32ebbdb1` | Corrected the half-boundary parameterization, derived the exact integral Hayes recurrence, and gated its identity-class counts against an independent direct Rabin enumeration through degree 20. |
| 2026-08-18 | `6e1372073` `d308c7bc1` | Added deterministic content-bound search shards; five hosts produced and the repository admitted 400/400 dual-checked degrees, with finite-range credit explicitly separated from the universal conjecture. |
| 2026-08-18 | `98f2d953f` `b678ec7e6` `3718aab11` | Added canonical bounded artifacts, an algebraically separate dense checker, standalone producer/checker CLIs, and the dual-gated degree-400 witness; completion does not claim the universal theorem. |
| 2026-08-18 | `81321fc65` | Added bounded bit-packed `GF(2)[x]`, untrusted Rabin certificate production, independent identity checking, exhaustive degree-10 oracle agreement, certificate mutations, the exact Lemire theorem contract, and accepted ADR-0480. |

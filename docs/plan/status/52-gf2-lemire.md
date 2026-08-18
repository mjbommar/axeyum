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
theorem at that exact fixed-field half-degree boundary; Gao's Hayes-class
formula is the first target for specialization.

The portable boundary is now complete for bounded witnesses. `98f2d953f` adds
canonical JSON, a dense-coefficient second checker, and a standalone dual-check
CLI; `b678ec7e6` adds the fail-closed producer. `3718aab11` commits and gates the
188,458-byte degree-400 certificate (SHA-256 `30ae3f33...383d5`) from both
aggregate check paths. This is one checked degree, not the range through 400 and
not the universal theorem.

**Next.** Add deterministic candidate enumeration and sharded manifests, then
run bounded, thermally conservative search/check shards on s1, s4, s5, s6, and
s7. Fleet completion alone earns no credit. In parallel, derive an exact
identity-class recurrence or sharpened positive count, then reconstruct the
reciprocal and central lemmas through the kernel and fact ledger before claiming
a universal proof.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `98f2d953f` `b678ec7e6` `3718aab11` | Added canonical bounded artifacts, an algebraically separate dense checker, standalone producer/checker CLIs, and the dual-gated degree-400 witness; completion does not claim the universal theorem. |
| 2026-08-18 | `81321fc65` | Added bounded bit-packed `GF(2)[x]`, untrusted Rabin certificate production, independent identity checking, exhaustive degree-10 oracle agreement, certificate mutations, the exact Lemire theorem contract, and accepted ADR-0480. |

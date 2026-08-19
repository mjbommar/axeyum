# ADR-0484: Bit-packed GF(2) polynomial certificates precede any solver surface

Status: accepted
Date: 2026-08-18
Index-summary: Build bounded bit-packed GF(2)[x] search in the CAS, with portable Rabin certificates checked independently of the search verdict, before adding a finite-field IR or SMT surface

## Context

Daniel Lemire's half-degree irreducible-polynomial conjecture is a useful test
of Axeyum's self-extension loop.  The existing `axeyum-cas::gfp` module can run
Rabin's test over a general prime field, but its dense `Vec<i128>` arithmetic is
slow at degree 400, has no operation budget, and returns only a Boolean.  No
solver route, term sort, evidence envelope, or kernel theorem consumes that
result.  Re-multiplying factors certifies a product but does not certify the
irreducibility of the factors.

Making finite fields an SMT surface now would therefore put a new logic ahead
of its semantics, resource, model, and evidence contracts.  Conversely, a
search-only script would leave a mathematical result outside Axeyum's trusted
checking architecture.

## Decision

Add a dedicated, bit-packed `GF(2)[x]` layer to `axeyum-cas` before adding any
finite-field sort or operator to `axeyum-ir` or SMT-LIB.

The layer has three boundaries:

1. normalized little-endian `u64` words for polynomial values;
2. explicit degree, Frobenius-step, and word-operation limits, with typed
   decline instead of panic or an ambiguous empty result; and
3. an untrusted certificate producer plus a checker that never calls the
   producer's irreducibility verdict.

An irreducibility certificate records every Frobenius reduction
`r_(i-1)^2 = q_i f + r_i`, the final equality `r_n = x`, and one Bezout identity
for `gcd(f, r_(n/p) + x) = 1` for every distinct prime divisor `p` of `n`.
The checker derives and validates the complete prime-divisor set, polynomial
identities, degree bounds, and final residue under its own operation budget.

The search procedure and distributed witness generation remain untrusted.
Serialized artifacts, a separate checker implementation, a solver bridge, and
Lean-kernel reconstruction are later increments.  The open general CAS/solver
dependency-direction question in `research-questions.md` is not closed by this
CAS-local decision.

## Evidence

On the pre-decision implementation, the known degree-400 witness
`x^400 + x^5 + x^3 + x^2 + 1` takes about 6.45 seconds in a release build and
17.77 seconds in a debug build.  The public general-field `add` path also
panics for modulus zero, despite module documentation claiming operations do
not panic.  Repository search finds no `gfp` consumer in the IR, query, solver,
kernel, fact ledger, or scripts.

The certificate is Rabin's finite-field irreducibility criterion expressed as
polynomial identities.  It transfers no trust from a fast search algorithm:
altering a quotient, remainder, prime-divisor list, or Bezout coefficient must
make checking fail.

The implemented producer-plus-checker degree-400 regression completes below
the test harness's 10 ms resolution in a warmed release build.  Exhaustive
enumeration of every monic polynomial through degree 10 agrees among the new
producer, the existing general-field Rabin implementation, and a test-only
`u128` trial-division oracle.  Focused tests include cross-word arithmetic,
division reconstruction, four certificate mutations, and typed resource
declines.  The complete CAS library passes 650 tests with two intentionally
ignored, and all-target CAS Clippy passes with warnings denied.

## Alternatives

- Optimizing the general `Vec<i128>` implementation was rejected for this
  characteristic-two workload because it preserves unnecessary coefficient
  and modular-arithmetic costs and still supplies no evidence object.
- Adding a finite-field SMT sort immediately was deferred because no public
  semantics, model lifting, or proof route exists for it.
- Treating a Boolean Rabin result or factor re-multiplication as a certificate
  was rejected because neither independently witnesses irreducibility.
- Trusting a fleet search transcript was rejected; fleet hosts produce
  candidates and certificates, never mathematical credit by completion alone.

## Consequences

- Degree-400 and larger experiments can use compact carryless arithmetic and
  bounded work.
- Certificate size is linear in the degree in Frobenius steps and polynomial
  data, trading compactness for a simple checker contract.
- CAS gains a real finite-field trust boundary without forcing the solver IR
  into a premature public logic.
- A later artifact schema and independent checker can preserve this identity
  contract while replacing or distributing the producer freely.

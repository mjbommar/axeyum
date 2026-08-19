# ADR-0486: Hayes class research stays in bounded CAS APIs, not SMT

Status: accepted
Date: 2026-08-18
Index-summary: Extract bounded principal-unit, Hayes endpoint, conductor-layer, and sufficient-bound APIs in axeyum-cas while leaving the solver IR unchanged

## Context

ADR-0484 established bit-packed `GF(2)[x]` values and portable Rabin
certificates before any finite-field solver surface. The Lemire investigation
subsequently isolated a different workload: exact type-II Hayes class counts,
finite Fourier transforms over principal units, exact-conductor decomposition,
and integer checking of the implication from a proposed cancellation estimate
to endpoint positivity.

The first implementation lived entirely in one diagnostic binary. It had exact
arithmetic and committed controls, but no reusable typed boundary and no public
resource admission. Conversely, placing these operations in SMT would require
new sorts, term semantics, model lifting, replay, and proof evidence without an
SMT decision problem or a current consumer. SMT cannot supply the missing
analytic cancellation theorem merely by representing its finite-field terms.

## Decision

Keep this research surface in `axeyum-cas` and extract a bounded
`gf2_hayes` module. Its public API provides:

1. the deterministic cyclic decomposition of
   `(1+x GF(2)[x])/(x^(ell+1))`;
2. exact identity-class populations reconstructed from two modular transforms
   with checked CRT uniqueness;
3. exact full-class inverse-Fourier distributions, bounded central absolute
   power sums, signed fourth-cumulant numerators, and a resource-bounded exact
   conductor filtration of the squared-discrepancy Fourier energy;
4. endpoint discrepancies and exact-conductor layers with a checked
   telescoping identity; and
5. exact bignum verification that explicitly supplied conductor or fourth-
   moment estimates, together with the separately certified finite range,
   imply the required endpoint and proper-divisor inequalities; and
6. exact finite-group removal of proper prime powers, including a structural
   odd-endpoint certificate that reduces `n=2ell+1` to
   `N_n(1)=1+n I_n(1)` without a Fourier transform.

Every expensive entry point takes explicit limits on `ell`, degree, group
order, and retained table cells and declines before allocation. The diagnostic
CLI consumes the library API and retains independent committed value controls.
The existing Python sufficient-bound checker remains as an algebraically
separate implementation.

Do not add a finite-field, character, ray-class, or analytic-bound sort or
operator to `axeyum-ir`, `axeyum-solver`, or SMT-LIB for this increment. A later
solver surface still requires the foundational semantics/model/evidence gates
and a demonstrated solver consumer.

## Evidence

The refactored endpoint CLI reproduces every committed discrepancy through the
default gate range and the conductor layers telescope exactly. Unit tests pin
the `ell=8` principal-unit factorization, endpoint values, layer values, full
class distribution, Parseval identity, fourth moment and cumulant, exact
sufficient-bound implications, the level-5 failure of the experimental moment
envelope, malformed inputs, and pre-allocation resource decline. The Python
checker independently reproduces the level-5 failure, the level-8 moments,
both arithmetic implications, and the conductor-bound negative controls.

The fourth-moment filtration additionally checks `C_0=M_2^2`,
`C_ell=2^ell M_4`, and nonnegative exact-level differences. Its mixed-radix
projection is controlled level by level against independently recomputed lower
Hayes distributions. The separate integer group-ring checker projects explicit
unit-polynomial representatives and reproduces both level-8 energy vectors;
the public CLI is exercised by the GF(2) artifact gate.

The prime-power inversion reconstructs every class population after removing
all lower-degree prime powers and fails on negative, indivisible, or
non-reconstructing results.  At odd endpoints, a separate structural report
enumerates every proper divisor, checks that its exponent is odd and its prime
degree is at most `ell`, and records the unique surviving `x^n` contribution.
Exact full inversion agrees with that constant-one population through
`ell=8`, including composite endpoint degree 15.

All-target, all-feature `axeyum-cas` Clippy passes with warnings denied. The
full Lemire range gate exercises the Rust and Python arithmetic implications,
the exact Hayes recurrence, the endpoint transforms, conductor diagnostics,
and every degree-1-through-400 witness checker.

## Alternatives

- Leave the transform inside the binary: rejected because it prevents other
  CAS experiments and Autogenesis dispatch from naming typed operations and
  hides allocation policy in an executable.
- Add QF_FF or a ray-class SMT theory now: rejected because there is no model or
  proof consumer and the open mathematical step is a uniform analytic bound,
  not a finite satisfiability query.
- Treat the sufficient-bound checker as proof of cancellation: rejected. It
  checks only the implication from a named assumption; the assumption remains
  an open obligation.
- Create a new crate: rejected under the minimal-split discipline. The module
  has one CAS research consumer and no proven independent dependency boundary.

## Consequences

- Lemire/Hayes experiments now use deterministic, reusable, bounded APIs rather
  than copying a one-off transform implementation.
- Exact finite evidence and a conditional arithmetic theorem remain sharply
  separated from the missing universal cancellation lemma.
- The universal conjecture and the selected fourth-moment obligation have
  explicit empty-evidence fact-ledger entries; neither is registered as an
  executable Autogenesis operation while no universal checker exists.
- Autogenesis can eventually register these CAS operations without confusing
  their output with a solver verdict or kernel theorem.
- No default dependency, native backend, SMT logic, or public IR operator is
  added.

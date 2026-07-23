# ADR-0363: Preregister source-guided quantified-UF default repair

Status: proposed
Date: 2026-07-23

## Context

ADR-0359 repairs only total defaults of relevant `Int`/`Real`-result functions
and grants SAT credit only through the independent finite-profile certificate
plus canonical original-query replay. Its candidate pool intentionally uses
only values already present in the ground model, zero, and one checked
predecessor/successor closure.

After ADR-0360 through ADR-0362, eight ordinary Z3-SAT cases remain Unknown in
the frozen 256-case quantified-UFLIA differential. The exact
[source-guided measurement](../../plan/quantified-uflia-source-guided-default-measurement-2026-07-23.md)
shows that their source formulas contain useful default candidates absent from
ADR-0359: integer literals and binder-independent integer subterms evaluable
under the unchanged initial candidate. Under ADR-0359's existing 32-value and
256-combination caps, these values produce five independently checked models.

This is default repair, not scalar completion. Seeds 150 and 242 have no
source-relevant free scalar, yet source-guided defaults certify them. The search
does not alter a scalar assignment or explicit function entry.

## Decision

**Add one bounded, deterministic, initial-candidate retry that augments
ADR-0359's default candidates with exact-source integer values while preserving
the existing evidence and resource envelope.**

The implementation will:

- leave ADR-0359's established model-only repair unchanged and run it first;
- run only in the outer MBQI invocation, only for the initial ground candidate,
  after ADR-0362's guarded fixed-query retry and ADR-0360's complete free-Int
  completion have declined;
- consider only functions required by the accepted quantified-UF source shape,
  require every result sort to be `Int`, preserve signatures and all explicit
  table entries, and change only total defaults;
- begin with ADR-0359's existing same-sort model/default/entry/zero values, add
  exact source `Int` literals, and add exact source `Int` subterms only when a
  binder-dependency pass proves them independent of every quantified binder and
  ordinary evaluation succeeds under the initial model;
- apply the predecessor/successor closure once, use stable deduplication, and
  decline without truncation above 32 values or 256 complete default tuples;
- check the caller-owned deadline before and during enumeration;
- skip the retry when it adds no candidate information and disable it inside
  ADR-0362's inner invocation; and
- return SAT only after the independent finite-profile checker accepts every
  original universal and canonical `check_model` accepts the exact full source.

Inner UNSAT/Unknown transfer does not arise: this mechanism constructs only
candidate models and returns either a checked SAT model or no result. On
decline, ordinary MBQI, E-matching, and ADR-0361 remain unchanged.

## Evidence gates

Acceptance requires:

1. Focused tests freeze deterministic collection of source literals and
   binder-independent evaluated source terms while excluding binder-dependent,
   non-`Int`, malformed, and overflowed candidates.
2. Existing scalar assignments, function signatures, and explicit table
   entries survive every default replacement; a candidate requiring an entry
   rewrite rejects.
3. The exact generated seeds 30, 32, 70, 150, and 242 return checked SAT with
   the measured pool/product sizes or default tuples; seeds 122, 175, and 182
   remain honest Unknowns for product overflow or bounded exhaustion.
4. ADR-0362 seed 111, ADR-0361 seeds 23/231, ADR-0360 seed 145, and prior
   SAT/UNSAT decisions remain unchanged.
5. The frozen 256-case direct-Z3 differential reaches at least 232 jointly
   decided agreements, exactly 215 replayed SAT models, and zero disagreement,
   error, or replay failure; the ordinary Z3-SAT residual is exactly
   `122, 175, 182`. The 232 floor covers the measured nine-versus-ten Z3
   timeout variance without weakening any Axeyum or replay invariant.
6. Solver Clippy, strict rustdoc, focused/full solver tests, branch-owned
   documentation, and proportional repository gates pass. Cross-lane retained
   evidence is reported separately and is never rewritten here.

## Alternatives

- **Increase the value or product cap.** Rejected: all five measured successes
  fit the existing 32/256 envelope, while seed 122's 289-product is a required
  decline.
- **Truncate or rank an overflowing source pool.** Rejected: search completeness
  within the declared pool must not depend on an unregistered order heuristic.
- **Rewrite explicit UF entries.** Rejected: ground constraints depend on those
  points, and ADR-0359's default-only boundary remains independently useful.
- **Use Z3 model values.** Rejected: the oracle adjudicates tests only and never
  contributes production candidates.
- **Run the expanded repair before established completion routes.** Rejected:
  additive capability must not steal prior decisions or their deadline.
- **Trust source-derived values as evidence.** Rejected: they are untrusted
  search hints. The finite-profile checker and exact replay remain authoritative.

## Consequences

The expected frozen differential moves from 228 to at least 232 jointly decided
cases and from 210 to exactly 215 checked SAT models without changing the
trusted checker, public evidence format, UNSAT route, or any cap. Prototype
runs observe 232/233 joint agreements solely with ten/nine independent Z3
timeouts. Three residual seeds remain a separate problem. This does not add
arbitrary arithmetic synthesis, scalar ranking, explicit-entry repair, general
UF models, or proof reconstruction.

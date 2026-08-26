# ADR-0556: GF(2) tensor decompositions use sparse supports and dense exact replay

Status: accepted
Date: 2026-08-25
Index-summary: Check portable GF2 rank-one tensor witnesses against independently generated targets by bounded coefficient replay

## Context

Three open-problem lanes need finite multilinear or circuit witnesses, beginning with the
published rank-17 decomposition of the full polynomial-multiplication tensor `P_6`.  Axeyum's
CAS already implements polynomial arithmetic over finite fields, but it had no public tensor
artifact, target generator, or coefficient checker.  Trusting a producer's reported rank or
using the producer's tensor object again would not test basis conventions, term transcription,
or the claimed identity.

## Decision

Add `axeyum_cas::gf2_tensor` with a versioned portable decomposition artifact.  A tensor is
three explicit dimensions plus the lexically interpreted coordinates whose coefficients are
one.  A rank-one term is the three sparse supports of its factor vectors.  The checker:

- requires the artifact version and exact dimension agreement;
- rejects zero dimensions, arithmetic overflow, duplicate coordinates/support indices, and
  out-of-range indices;
- admits work only under explicit coefficient, term, and support-entry limits;
- XOR-expands every admitted rank-one term into a dense bit vector; and
- compares every coefficient in stable lexicographic order, returning either verified rank
  and denominator or the first exact mismatch.

The first target constructor is full polynomial multiplication:
`sum_(i,j<n) a_i tensor b_j tensor c_(i+j)`.  It is generated independently of any witness
file.  The JSON CLI example returns zero only for a verified identity, one for a coefficient
mismatch, and two for malformed or resource-declined input.

This checker certifies an **upper bound** only.  It does not establish minimality, and a rank
search must not interpret failure to find fewer terms as a lower-bound certificate.

## Evidence

- The schoolbook rank-9 decomposition of `P_3` matches all 45 coefficients.
- Mutating one factor reports the first mismatch at `[0,0,0]`.
- Repeated sparse indices are rejected rather than silently cancelled.
- A coefficient cap below the target volume declines before dense allocation.
- Wang's published rank-17 `P_6` witness matches all 396 independently generated
  coefficients.  Removing its first `c0` entry exits one at `[0,0,0]`.

## Alternatives

### Reuse the producer's tensor and equality routine

Rejected.  Shared target construction would fail to detect a common basis or indexing bug.

### Store dense factors and target tensors

Rejected for the portable v1 artifact.  Sparse supports are canonical for binary vectors,
human-auditable, and compact; the checker still expands to a dense bounded comparison so
omitted zero coefficients are checked.

### Encode decomposition equality directly as SAT

Rejected as the positive-witness checker.  SAT is useful for finding a decomposition and
DRAT for proving nonexistence, but a supplied witness needs only transparent exact XOR/AND
replay.

## Consequences

- Bilinear-rank search has a reusable positive-certificate boundary before any rank-16 SAT
  encoding is admitted.
- The same sparse-factor primitive can support finite-field circuit synthesis, but S-box and
  SIMD semantics still need their own independently generated targets and replay layers.
- Kernel reconstruction of a checked finite identity remains a separate assurance upgrade;
  this decision does not claim it.

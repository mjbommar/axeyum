# ADR-0105: Affine-growth quantifiers to Lean

Status: accepted
Date: 2026-07-11

## Context

After ADR-0104, the quantified-LIA audit has two UNSAT proof gaps. The
ADR-0097 affine-growth class behind `repair-const-nterm` is

```text
forall xs. not (c*x - ite(x = p, a, b) >= t)
```

for positive literal `c`, where `p`, `a`, `b`, and `t` contain no bound
variable. ADR-0097 checks this theorem over untouched original IR and explains
two consecutive counterexamples, but does not reconstruct them in the Lean
kernel.

ADR-0104's trusted integer prelude now states the exact general fact needed:
for positive `c`, every `b+t` has `b+t = c*q+r` with `0 <= r < c`. Adding
division operations or another theorem-specific arithmetic axiom would duplicate
that foundation rather than reduce trust.

## Decision

Reconstruct the complete checked ADR-0097 structural class, not only the
committed target spelling. The reconstructor must regenerate and compare the
certificate, retain every original integer binder, accept both checked
subtraction/add-with-minus-one and equality orientations, and treat each
bound-variable-free parameter term as an opaque but consistently shared integer
value.

Encode the piecewise body denotationally as the conjunction

```text
(x = p  -> not (t <= c*x-a)) /\
(x != p -> not (t <= c*x-b)).
```

This is the exact proposition-level semantics of the integer `ite`; it neither
assumes a branch nor adds an `ite` axiom to the arithmetic prelude.

Apply `euclidean_decomposition` to `b+t` and `c`. For `x=q+1`, use `r<c` to
derive

```text
b+t <= c*q+c = c*(q+1),
t <= c*(q+1)-b.
```

Positive-slope monotonicity gives the same inequality at `q+2`. Each guarded
else implication plus its proved comparison yields a double-negated equality of
that candidate with `p`. If `q+1=p`, strict consecutiveness proves `q+2!=p`,
contradicting the second double negation; therefore `q+1!=p`, contradicting the
first double negation. This closes constructively, without excluded middle.

No new arithmetic prelude theorem, classical axiom, query-specific witness
axiom, certificate-refuter axiom, or div/mod proof operation is added.

## Acceptance

- The committed `repair-const-nterm` row reconstructs through the direct API and
  generic router.
- A signed/add-with-minus-one/equality-swapped multi-binder instance from the
  checked ADR-0097 class reconstructs.
- Tampered certificates and binder-dependent or non-positive near misses are
  rejected before proof construction.
- A fresh 12-row audit reports evidence checked/certified 9/9, Lean UNSAT 6/7,
  and dominant candidates 8/9, with zero mismatches, errors, timeouts, or trust
  holes.
- Focused tests, solver/evidence/bench splits, workspace Clippy,
  warning-denied rustdoc, links, foundational resources, formatting, and golden
  matrices pass. The known whole-workspace aggregate limitation is recorded.

## Alternatives

- **Expose integer `ite` as an uninterpreted operation plus branch axioms.**
  Rejected: the guarded proposition encoding is exact and uses the existing
  logic prelude.
- **Use one fixed candidate.** Rejected: it may equal `p` and select arbitrary
  `a`; two consecutive candidates are load-bearing.
- **Declare the generated affine inequality as an axiom.** Rejected: it follows
  from ADR-0104 decomposition and existing ordered-ring rules.
- **Restrict reconstruction to the exact corpus text.** Rejected: ADR-0097
  already exposes a broader checked signed/orientation class, and the proof
  architecture covers that class without additional trust.

## Consequences

- `repair-const-nterm` can receive kernel-checkable proof credit, leaving finite
  equality partition as the only current quantified-LIA UNSAT proof gap.
- The general Euclidean theorem is exercised by a second proof family, showing
  that ADR-0104's trusted-base expansion is reusable rather than target-specific.
- General affine CEGQI, nested piecewise Boolean structure, and function-valued
  parameters remain outside this structural class.

## Validation

- The committed ten-binder `repair-const-nterm` theorem reconstructs through
  both the certificate API and generic router as `IntAffineGrowth`.
- A three-binder control with reversed pivot equality, swapped additive order,
  explicit multiplication by `-1`, and signed pivot/branch/threshold terms also
  reconstructs, exercising the broader checked ADR-0097 class.
- A tampered coefficient is rejected before proof construction, and a
  binder-dependent satisfiable near miss does not classify or route.
- Fresh release audit artifact:
  `/tmp/axeyum-quant-lia-adr0105-audit.json`. Evidence is checked/certified 9/9;
  Lean checks 6/7 UNSAT rows; 8/9 decisions are dominant candidates. Mismatches,
  audit errors, timeouts, and trust holes are all zero.
- Focused all-feature tests pass 4/4; solver library 829/829; evidence 69/69;
  bench 7/7; capability/support goldens 2/2 and 12/12; workspace
  all-target/all-feature Clippy, warning-denied rustdoc, links, formatting/diff
  hygiene, and foundational resources (137 concepts, 174 packs) pass. The
  pre-existing Sturm nontermination remains the reason no whole-workspace
  aggregate is claimed.
- No external `lean` executable is installed, so the generated source is
  checked by the in-tree Lean kernel and renderer but not an additional Lean
  subprocess.

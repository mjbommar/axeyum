# ADR-0075: Externally Checked Array Select Congruence

Status: accepted
Date: 2026-07-09

## Context

ADR-0073 made array equality flags and observed reads part of canonical ABV/AUFBV
refinement. The direct contradiction

```text
a = b
select(a, i) != select(b, i)
```

already produced an in-tree-checkable Alethe proof through the generic EUF
emitter and reconstructed to a real Lean `False` term. The generic emitter,
however, deliberately renders interpreted operators with internal debug heads
such as `Select`. That representation is adequate for Axeyum's checker but does
not name SMT-LIB's built-in `select`, so the artifact was not directly checkable
by Carcara against the original QF_ABV problem.

This contradiction needs no array axiom. It is equality congruence over the
binary `select` function, with reflexivity for the shared index. Calling it
"extensionality" obscures the proof boundary: array extensionality is the
opposite-direction principle used to witness `a != b`; `a = b` implying equal
reads is ordinary congruence.

## Decision

Add and prefer a specialized direct certificate emitter,
`prove_qf_abv_select_congruence_alethe_carcara`, for one asserted array equality
and one asserted same-index select disequality.

- Match only direct equal bases and a syntactically shared read index. Both read
  orientations are supported; different indices and transitive array-equality
  chains decline to the existing wider fallback.
- Render array terms with literal SMT-LIB `select`/`store` heads rather than
  internal operator debug names.
- Emit an `eq_reflexive` unit for `i = i`, then an `eq_congruent` clause
  `not(a=b) or not(i=i) or select(a,i)=select(b,i)`. Resolve the two argument
  units to derive read equality.
- When the asserted disequality reverses the reads, use Carcara's premise-taking
  `symm` rule before the final resolution. The same rule is supported by the Lean
  reconstructor.
- Self-check every artifact with `check_alethe` before return. The zero-trust
  evidence dispatcher prefers this emitter before generic EUF congruence.
- Record no `TrustId::ArrayElim`: the proof uses no ROW, extensionality, or
  elimination premise.

## Soundness Argument

Equality is substitutive in every function argument. From `a = b` and the
reflexive `i = i`, congruence derives
`select(a, i) = select(b, i)`. Resolving that unit against the asserted negation
produces the empty clause. Reversing the read equality is justified by symmetry.

The matcher requires identical index `TermId`s and direct equality operands, so
it cannot silently assume an unproved index or transitive array equality. Both
the in-tree checker and Carcara validate the rule applications, and the final
artifact is reconstructed independently to a Lean kernel-accepted `False` term.

## Evidence

- In-tree tests cover forward and reversed reads, literal `select` rendering,
  and rejection of a different-index query.
- Installed Carcara accepts both forward and reversed QF_ABV artifacts against
  their original SMT-LIB problems.
- Carcara rejects a tampered `eq_congruent` clause with the array-equality
  antecedent removed.
- `produce_evidence` selects `UnsatAletheProof` with an empty trust-step list for
  the direct conflict.
- The 67-family representative reconstruction gate passes in the real Lean
  binary, with the reversed-read shape selected as the array-congruence
  representative.

## Alternatives

- **Keep the generic EUF artifact.** Sound and Lean-checkable, but its debug
  operator head is not a portable proof term for the original SMT-LIB problem.
- **Teach Carcara an Axeyum `Select` symbol.** Rejected because that would check a
  translated problem rather than the original array syntax.
- **Use a custom array rule.** Rejected because no array theory rule is needed;
  ordinary equality congruence is both smaller and independently supported.
- **Generalize immediately to transitive equality classes.** Deferred. The
  generic in-tree/Lean route remains sound for those cases; a portable class
  explanation should share the future merge-triggered array queue rather than
  duplicate an equality engine in this emitter.

## Consequences

- A canonical array-equality conflict now has one artifact accepted by the
  in-tree checker, Carcara, and Lean, with no reduction trust hole.
- The direct evidence route uses standard SMT-LIB operator names.
- This does not certify read-over-write instances, the disequality diff-witness
  direction of extensionality, arbitrary equality chains, or canonical online
  CDCL(T) proof logging. Those remain P3.5/P2.2 work.

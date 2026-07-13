# ADR-0138: Kernel-checked negated BV existential witnesses

- **Status:** accepted
- **Date:** 2026-07-13
- **Owners:** solver / evidence / Lean reconstruction
- **Extends:** ADR-0126, ADR-0135, ADR-0137

## Context

ADR-0126 certifies UNSAT for one closed top-level
`not (exists+ body)` over Bool and bit-vector binders. Search proposes a complete
typed witness for the positive body, and an independent checker evaluates that
witness against the untouched original IR. The public quantified-BV corpus has
three such rows (`NUM878`, `ari-syqi`, and `ari118-bv-2occ-x`), but their checked
evidence did not yet reconstruct to a genuine Lean proof.

The proof shape is simple at the source level: prove the positive body under the
carried values, introduce the existential binders, and apply the untouched
negated source theorem. The bit-level body is not simple operationally. Directly
expanding a large AIG into a proposition or computational term caused shared
kernel DAGs to be revisited as trees during abstraction, instantiation,
universe substitution, open-term inference, definitional equality, weak-head
normalization, and finally module rendering. Early `NUM878` attempts exhausted
a 4 GiB envelope.

The route must preserve the project's trust boundary. The host evaluator may
reject a bad certificate, but it cannot stand in for the exported proof. The
kernel must check the typed existential construction and the concrete body, and
the generated module must contain no theorem-specific refuter or `sorryAx`.

## Decision

Add a dedicated `NegatedExistentialWitness` reconstruction fragment for the
exact ADR-0126 source shape.

1. Re-run `check_negated_existential_witness` before constructing any proof.
   The original `not (exists+ body)` is introduced as the sole source axiom.
2. Represent every source binder by a typed computational Bool or a width-exact
   bit-vector datatype. Build the carried values with datatype constructors and
   introduce the binders with nested genuine `Exists.intro` applications.
3. Lower the untouched quantifier-free body through the existing Bool/BV AIG
   semantics. For AIGs of at most 512 nodes, construct an explicit logical proof
   for each evaluated gate. For larger AIGs, use computational Bool fields,
   shared reducible Bool `not`/`and` definitions, and local `let` bindings for
   AIG gates. Map the concrete root back to `Prop`; kernel reduction must close
   it with `True.intro`.
4. Apply the original negated-existential axiom to the constructed existential
   witness and require the result to infer exactly `False`. Render the checked
   declaration environment through the self-contained Lean module exporter.
5. Keep the ADR-0126 admission boundary unchanged: one closed direct negated
   existential, unique Bool/BV binders, widths 1 through 64 for Lean
   reconstruction, and the existing certificate binder/body resource caps.
   Open bodies, nested quantifiers, functions, arrays, and arithmetic sorts
   decline.

Make the kernel operations exercised by this route DAG-linear:

- memoize `abstract_fvars` and `instantiate` by expression and binder offset;
- memoize universe substitution by expression;
- cache open-expression inference and definitional equality only for the exact
  current local context, clearing both caches on every push or pop; and
- cache weak-head normalization by expression and append-only environment
  revision.

These caches change traversal cost, not kernel rules. Context-sensitive results
never survive a binder-stack change, and the environment revision prevents a
normal form from crossing a declaration update.

## Consequences

### Positive

- All three ADR-0126 public rows now produce genuine typed, kernel-checked Lean
  `False` proofs with no `sorryAx` or theorem-specific contradiction axiom.
- The proof router selects this source-bound fragment before generic existential
  reconstruction, and a representative is registered for external Lean
  checking. The current host has no `lean` binary, so the in-tree kernel is the
  executed checker here.
- The release-only three-row gate completes in 12.43 seconds of test time under
  a 4 GiB cap. The cold build-and-test command completes in 34.46 seconds and
  peaks at 1,941,680 KiB RSS on the reference host.
- The refreshed exact public audit remains 54/54 evidence-certified and
  rechecked with zero disagreement, audit error, or timeout; dominant candidates
  rise from 45 to 48 and Lean UNSAT coverage rises from 9/18 to 12/18.
- DAG-linear kernel traversal benefits other large shared proof terms without
  weakening declaration admission or definitional equality.

### Negative

- The computational large-AIG encoding is less human-readable than the small
  gate-by-gate logical proof and still has a material memory footprint.
- The 512-node switch is an engineering resource boundary, not a semantic
  distinction. Both sides need regression coverage.
- Kernel caches add trusted implementation state. Their keys and invalidation
  discipline are therefore covered by shared-DAG and local-context tests.
- This does not reconstruct the remaining ADR-0124/0127/0128/0129 quantified-BV
  UNSAT families, Lean SAT models, or general nested/alternating QSAT.

## Validation

- focused ADR-0126 evidence, routing, deterministic rendering, and tampered
  witness rejection tests;
- 164 `axeyum-lean-kernel` unit tests plus its doctest, including shared-DAG
  abstraction, instantiation, universe substitution, and open inference;
- release-only exact public-corpus gate under `MEM_LIMIT_GB=4`;
- external-Lean representative registration, which skips when `lean` is absent;
  and
- regenerated quantified-BV dominance audit and generated dominance dashboard.

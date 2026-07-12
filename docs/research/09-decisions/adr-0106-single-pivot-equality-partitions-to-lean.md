# ADR-0106: Single-pivot equality partitions to Lean

Status: accepted
Date: 2026-07-11

## Context

After ADR-0105, `cbqi-sdlx-fixpoint-3-dd` is the only decided quantified-LIA
UNSAT row without a Lean proof. ADR-0101 certifies a broad closed Bool/Int
fragment where each Int binder occurs only in equality tests against explicit
literals. Its executable checker enumerates every mentioned literal plus one
other representative, but using that evaluator as a Lean refuter axiom would
leave the semantic quotient outside the kernel.

The measured target uses one pivot, zero, for every Int binder. This gives a
general two-cell class `{c}` / `Int \ {c}` per binder, under arbitrary admitted
Boolean nesting, polarity, quantifier alternation, and Boolean/integer `ite`.
Proving universal truth or existential falsity over an arbitrary integer witness
requires deciding `x=c`. The current ordered-ring prelude does not expose
integer equality decidability.

## Decision

Add one explicit standard theorem to `IntPrelude`:

```text
eq_em : forall a b : Z, Or (Eq Z a b) (Not (Eq Z a b))
```

This is constructive decidable equality for integers, not unrestricted
propositional excluded middle. Standard integers remain a model of the trusted
prelude. The theorem's exact dependent type is kernel-checked at admission and
by an application test.

Add a proof-producing reconstructor for the ADR-0101 sub-class where every Int
binder is compared with at most one distinct literal. It must:

1. recheck the complete ADR-0101 certificate against untouched original IR;
2. lower the checked formula to a small semantic Boolean tree while preserving
   every original quantifier;
3. encode Int equality atoms as genuine `Eq Z`, Bool binders as the existing
   computational `Bool`, and integer `ite` equality as exact guarded branch
   propositions;
4. recursively produce either a proof or a refutation for every connective;
5. refute false universals and prove true existentials by concrete
   representatives;
6. prove true universals and refute false existentials by eliminating an
   arbitrary witness: `Bool.rec` for Bool and `eq_em` for the two Int cells; and
7. apply the resulting `Not assertion` proof to the original assertion axiom,
   with the final closed term inferred and definitionally checked as `False`.

The reconstructor may use ADR-0101's evaluator only as untrusted proof-search
guidance. Kernel inference of the independently assembled term is the
acceptance gate. No expanded finite formula, evaluator result, or
certificate-specific refuter becomes an axiom.

The broader multi-constant-per-binder ADR-0101 evidence class remains checked
but outside this first Lean route. Extending it requires an N-way equality
split and pairwise literal-disequality proofs; it is not silently credited.

All pivot and adjacent representative literals share the integer reconstructor's
4,096-unit proof budget. A larger checked partition declines before constructing
unary integer terms.

## Acceptance

- `cbqi-sdlx-fixpoint-3-dd` reconstructs through the direct API and generic
  router.
- Controls exercise nested positive/negative quantifiers, Bool binders,
  signed single pivots, implication/XOR/Boolean `ite`, and integer `ite`
  equalities.
- Tampered certificates, free/direct-arithmetic forms, and a valid
  multi-constant formula outside the Lean sub-class do not reconstruct.
- A fresh audit reports evidence checked/certified 9/9, Lean UNSAT 7/7, and
  dominant candidates 9/9, with zero mismatches, errors, timeouts, or trust
  holes.
- Focused tests, solver/evidence/bench splits, workspace Clippy,
  warning-denied rustdoc, links, foundational resources, formatting, and golden
  matrices pass; the known whole-aggregate limitation is recorded.

## Alternatives

- **Admit the evaluator's false result as an axiom.** Rejected: this is exactly
  the proof boundary being closed.
- **Translate Int binders directly to a finite enum.** Rejected: the kernel would
  check the quotient formula but not its equivalence to quantification over
  `Z`.
- **Add unrestricted classical excluded middle.** Rejected: integer equality
  decidability is the narrower standard theorem required by this fragment.
- **Claim all ADR-0101 formulas.** Rejected until N-way splitting and arbitrary
  signed literal disequality are reconstructed and tested.
- **Hand-prove only the corpus syntax.** Rejected: the two-cell partition is a
  reusable semantic class and the recursive proof engine should cover its
  admitted Boolean structure.

## Consequences

- The measured quantified-LIA audit can reach complete per-decision Pareto proof
  credit while keeping the three undecided large affine-ITE engine rows honest.
- The trusted integer prelude grows by one explicit decidable-equality theorem.
- Multi-constant equality partitions remain a documented proof-coverage
  extension, not a hidden trust step.
- More-specific quantified theorem fragments are dispatched before this generic
  partition route when their accepted source classes overlap.

## Validation

- `quant_eq_partition_lean` passes 5/5 with the real SDLX target, arbitrary
  Bool/Int quantifier controls, connective and `ite` coverage, certificate
  tampering, the multi-constant boundary, and unsupported arithmetic forms.
- `int_prelude` passes 7/7, including exact theorem-type inference and an
  applied `eq_em` proposition check.
- Fresh release audit artifact
  `/tmp/axeyum-quant-lia-adr0106-audit.json` reports checked/certified 9/9,
  Lean-checked UNSAT 7/7, and dominant candidates 9/9. Baseline mismatches,
  audit errors, timeouts, and trust holes are all zero.
- Solver library 829/829, evidence 69/69, benchmark 7/7, capability golden 2/2,
  and support golden 12/12 pass. Workspace all-target/all-feature Clippy with
  warnings denied, warning-denied rustdoc, links, formatting/diff, and the
  137-concept/174-pack foundational-resource gates also pass.
- No external Lean binary is installed on this host, so validation uses the
  in-tree Lean kernel and renderer. No whole-workspace aggregate is claimed
  because of the known pre-existing Sturm nontermination.

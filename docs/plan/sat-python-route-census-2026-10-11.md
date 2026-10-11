# Python SAT certificate route census — 2026-10-11

EVD-5 evidence and remaining work. Scheduling stays in [PLAN.md](../../PLAN.md)
and the [proof/API plan](proof-api-consumer-plan-2026-10-10.md). Representative
fixtures establish these cases, not universal theory coverage.

## Reproduction and identities

Run the [export example](../../python/examples/sat_certificate_export.py) with
`--output <new-directory> --census --lrat-check <pinned-checker>`. Build the
checker privately following the [guard instructions](../../scripts/patches/README.md#drat-trim-empty-clause-guard).
It writes each representative route's source, CNF, DRAT and optional LRAT,
plus `route-census.json`. The current example requires every source to reparse;
it fails rather than publishing a rejected rendering as executable SMT-LIB.
The initial measurement below predates that repair.

Measured native source: combined implementation `2a111e062bd6242c13e96dac8b098ba68d7a188a`.
Sealed package: `/var/tmp/axeyum-feedback-combined-gates-invfxf_7/package`;
native SHA-256 `831f35b5f744de86057caa8cdbeb3a23abe0b805f64227ad0641597a4b14238c`.
Checker: DRAT-trim `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, with the tracked
empty-clause RUP guard; binary SHA-256
`19863c56cd7ee5e5e69f85a6134e6de13262bb9062b08b89ae83cd5580f33daf`.
The unmodified checker accepts a satisfiable replacement CNF; do not credit it
as an independent validation pass. This private patch establishes only the
recorded guard controls, not global external-checker soundness.

Result artifact: `/var/tmp/axeyum-lrat-reference-1rg8dt6y/census-export-final/route-census.json`;
terminal example exit 0; full output in `census-final.log` in the parent directory.
All six public term-exporter names are derived from the native module; an added
exporter without a fixture fails the census. Three tests collected/three passed,
zero skips, 0.30 seconds, with the sealed package and guarded checker configured.

## Initial observed routes

All six rows below produced DRAT and LRAT, passed in-tree text replay and
external clausal LRAT checking, and had a paired SAT control with an independently
replayed lifted model (`verified`, actual verdict `sat`). These checks do not
independently validate the term/theory-to-CNF transformation.

| Public exporter | Representative contradiction | Source writer reparses | Constraint |
|---|---|---|---|
| `export_qf_bv_unsat_proof` | 8-bit `x < 1` and `x > 0` | yes | Boolean-only export is additionally exercised by the example. |
| `export_qf_abv_unsat_proof` | Same-index read after write differs from its stored value | yes | BV indices/elements, four bits. |
| `export_qf_aufbv_unsat_proof` | Equal function arguments, but read-after-write value differs from the equal argument's function result | yes | Exercises arrays and UF together, four-bit domain/range. |
| `export_qf_uf_unsat_proof` | Congruence of a unary function contradicted by unequal results | yes | Representative uses four-bit arguments/range. |
| `export_qf_lia_unsat_proof` | Integer `x = 1` and `x = 2` | yes | Explicit `int_width=8`: bounded translation, not an unbounded-LIA proof contract. |
| `export_datatype_unsat_proof` | Distinct nullary constructors equated | **no** | Writer emits `construct/0` and `construct/1` without declarations; parser rejects. |

The raw `cnf.solve_with_drat_proof` route emits DRAT, with no LRAT field or
elaboration claim. The example rechecks its small contradiction. SMT text
`smt.get_proof` exports Alethe or explicit `None`, not an `UnsatProof` clausal
bundle. General `solver.produce_evidence` returns an `EvidenceReport`; its evidence
kind and check outcome must be inspected rather than assuming every UNSAT has
DIMACS/DRAT/LRAT. Those last two are API classifications, not a new population
measurement or completed universal evidence census.

## Remaining evidence requirements

The `UnsatProof` bundle lacks a serialized source-to-CNF mapping. Separate
`BitLowering` and `CnfEncoding` APIs retain in-memory evaluation/lifting maps;
that is useful SAT replay support, not a portable proof that a CNF matches an
arbitrary source query. Source hashes establish artifact identity only.

Next implement deterministic export and replay of the complete applicable
lowering chain, with altered-source/map rejection controls. Theory reductions
need their own checking recipes rather than merely attaching a Boolean CNF.
The datatype source declaration/constructor repair and representative parse/proof
round trips are recorded below; broader datatype populations remain separate. Keep bounded-LIA limits explicit. Extend the
representative fixtures to a registered proof population and cover general SMT
and mixed-theory evidence routes separately. RAT elaboration remains EVD-4.


## Source export and replay follow-up

Datatype writer`b8b237c65` now exports names and the reachable recursive
sort/field declaration closure. Six Rust controls cover nullary, recursive,
mutually recursive, field-only dependency, array/UF signature and quoted names.
All six initial exporter fixtures now emit reparsable `source.smt2`; the census
requires this and fails on a regression. Independently running Z3 over each
exported source returns UNSAT. This is representative serialization/verdict
validation, not proof of the theory lowering chain.

Python native source`30a4e434e` adds saved-text construction and
`UnsatProof.recheck_for_bool_terms(arena, assertions)` (ADR8000). Native SHA256
`10021c3dfa772267b520db5c9744fd96c602717043a5e4da3edd97eaf57b84cc`.
Current export artifact:
`/data0/axeyum/artifacts/python/source-bound-sat-qualified-76lb7aij/export`;
example exits0 with the same guarded checker pinned above. The two Boolean/BV
example bundles replay against the caller's original terms and reject a
satisfiable substituted query. SAT/proof/OMT37 tests pass0 skips; proof/stub35
pass0 skips after fixing the CAS integer annotation shadow. Nine source-binding
controls include two producer-disabled child processes restoring saved text.
Private guard deletion makes exactly one of those nine tests fail; sources are
restored bytewise.

This new replay rebuilds the production bit-blast/Tseitin encoding and checks
exact DIMACS correspondence. It is a useful source-binding API behind an
explicit trusted-reduction boundary, not independent bit-blast verification.
Equivalent source propositions with the same encoding may replay; original text
provenance/authentication is a different contract. Array/UF/datatype and
finite-width LIA maps remain absent from serialized bundles.

The independent-reference miter producer already exists in Rust. Its portable
source-bound checker must reconstruct the expected subject miter, compare its
CNF, and bind the final UNSAT certificate to the same source, without invoking
proof search. Checking two arbitrary refutations from text alone does not prove
that correspondence. Exposing that audited route and complete theory mappings
is the next evidence increment; external LRAT and kernel admission remain
separate claims.

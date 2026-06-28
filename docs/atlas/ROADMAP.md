# SMT Fragment Atlas Roadmap

## Charter

Create a small, reviewed, machine-readable atlas of SMT fragments and Axeyum's
current relationship to them: parser support, IR coverage, solver routes,
model replay, proof/evidence routes, benchmark rows, dominance status, and open
gaps.

The atlas is not a marketing surface. It is a planning and audit artifact. A
fragment row should say "unknown" or "partial" whenever the evidence is not
strong enough.

## Current Status

The first artifact has landed:

- [smt-fragments.json](../../artifacts/ontology/smt-fragments.json)
  contains the initial ten rows from A1.
- [smt-fragments.schema.json](../../artifacts/ontology/smt-fragments.schema.json)
  defines the row shape.
- [validate-smt-fragment-atlas.py](../../scripts/validate-smt-fragment-atlas.py)
  validates JSON syntax, stable row IDs, required evidence fields, local source
  links, benchmark references, and dominance-audit citations.

A0 and A1 are complete for the incubator MVP. A2 is partially complete: the
validator exists and runs locally, but negative fixtures and CI wiring remain
open.

## Non-Goals

- Replacing the SMT-LIB standard.
- Mirroring the full SMT-LIB benchmark repository.
- Claiming parity from unmeasured capability rows.
- Encoding every internal solver heuristic.
- Hiding uncertainty behind broad fragment names.

## Audience

| Audience | Need |
|---|---|
| Solver contributor | Know the next practical blocker by fragment. |
| Proof contributor | See which proof route is expected for each unsat result. |
| User | Check whether their logic and operators are supported. |
| Benchmark maintainer | Map corpus rows to fragments and maturity labels. |
| Documentation author | Generate consistent capability/support prose. |

## Content Model

The first machine-readable artifact should be:

```text
artifacts/ontology/smt-fragments.json
```

Each fragment row should contain:

```json
{
  "id": "qf_bv",
  "smtlib_logic": "QF_BV",
  "scope": "quantifier-free fixed-width bit-vectors",
  "sorts": ["Bool", "BitVec"],
  "operators": {
    "supported_public": ["=", "bvand", "bvor", "bvxor", "bvadd"],
    "partial": ["bvmul", "bvudiv"],
    "declined": []
  },
  "parser": {
    "status": "validated",
    "notes": "SMT-LIB parser covers the committed benchmark slice"
  },
  "solver_routes": [
    {
      "name": "bit-blast-to-SAT",
      "status": "validated",
      "source": "crates/axeyum-bv; crates/axeyum-cnf; crates/axeyum-solver"
    }
  ],
  "model_replay": {
    "status": "required",
    "notes": "Every sat result replays against original terms"
  },
  "proof_routes": [
    {
      "name": "LRAT/Alethe/Lean",
      "status": "partial",
      "coverage": "bitwise/comparison plus selected arithmetic routes"
    }
  ],
  "benchmarks": [
    {
      "source": "bench-results/SCOREBOARD.md",
      "status": "measured",
      "disagree": 0
    }
  ],
  "dominance": {
    "status": "partial",
    "source": "bench-results/DOMINANCE.md"
  },
  "open_gaps": [
    "hard QF_BV performance",
    "complete arithmetic Lean reconstruction"
  ]
}
```

The JSON schema should live at:

```text
artifacts/ontology/smt-fragments.schema.json
```

## Source Links

Rows should link to local authoritative state before external prose:

- [PLAN.md](../../PLAN.md)
- [STATUS.md](../../STATUS.md)
- [capability matrix](../research/08-planning/capability-matrix.md)
- [support matrix](../research/08-planning/support-matrix.md)
- [trust ledger](../research/08-planning/trust-ledger.md)
- [dominance scoreboard](../../bench-results/DOMINANCE.md)
- [parity path](../PARITY-STATUS-AND-PATH.md)

External references should be used for terminology and benchmark context:

- [SMT-LIB](https://smt-lib.org/)
- [SMT-COMP](https://smt-comp.github.io/)

## Phases

### A0: Schema Sketch

Status: complete for the incubator MVP.

Exit criteria:

- Draft `smt-fragments.schema.json`.
- Draft one complete `QF_BV` row.
- Review that fields can express parser, solver, model, proof, benchmark, and
  dominance state without hand-wavy fragment labels.

### A1: First Ten Rows

Status: complete for the incubator MVP.

Initial rows:

- `QF_BV`
- `QF_ABV`
- `QF_UF`
- `QF_UFBV`
- `QF_LRA`
- `QF_LIA`
- `QF_DT`
- `QF_FP`
- `QF_NRA`
- `QF_NIA`

Exit criteria:

- Every row links to local capability and benchmark evidence.
- Every row has at least one explicit open gap.
- Rows distinguish "decides", "measured", "certifies", and "dominates".

### A2: Validation Tool

Status: partial. The local validator exists; negative fixtures and CI wiring are
still future work.

Add a small validator that checks:

- JSON parses.
- Fragment IDs are stable and lowercase.
- Local links exist.
- Every `proof_route.source` references an existing file or document.
- Every benchmark reference points to a committed artifact.
- No row can use `dominant` without a dominance source.

Exit criteria:

- Validator runs in CI or a documented local command.
- Negative fixtures prove the validator catches missing evidence.

### A3: Generated Documentation

Generate a Markdown table from the JSON atlas.

Exit criteria:

- Generated table includes fragment, parser status, solver route, proof route,
  measurement status, and top open gap.
- Generated output is deterministic.
- The checked-in generated file is updated only by the generator.

### A4: Cross-Link Existing Matrices

Start replacing duplicated capability prose with atlas links.

Exit criteria:

- `docs/sibling-projects.md`, support matrix, and capability matrix link to the
  atlas where useful.
- No capability claim exists only in the atlas; the atlas points back to the
  authoritative evidence.

### A5: Graduation Decision

Keep the atlas in this repo unless:

- another project consumes it independently;
- the schema grows into a public interoperability artifact;
- generated data becomes too large for ordinary review.

## Validation Checks

Minimum checks for the first complete slice:

```sh
./scripts/check-links.sh
python3 scripts/validate-smt-fragment-atlas.py
```

The validator does not need to exist in A0/A1, but the roadmap should keep the
shape check explicit so rows do not become unconstrained prose.

## Example Queries

The atlas should eventually answer:

- Which fragments are model-replay checked?
- Which fragments are Lean-kernel reconstructed?
- Which fragments are measured against Z3/cvc5?
- Which rows are pure Rust and `unsafe`-free by default?
- Where does Axeyum intentionally return `unknown`?
- Which rows are blocked by parser support versus solver support versus proof
  support versus performance?

## Graduation Criteria

The atlas graduates from "incubator note" to "project artifact" when:

- at least 20 measured fragment rows are represented;
- the JSON validates in CI;
- the generated Markdown is linked from user-facing docs;
- at least one benchmark or dominance script consumes the JSON;
- row updates are part of the normal capability-update workflow.

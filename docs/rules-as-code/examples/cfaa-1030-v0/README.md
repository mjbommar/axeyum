# Computer Fraud and Abuse Act V0 (18 U.S.C. § 1030)

The first rule pack built from real statute text rather than an invented rule.
It models the punishment clauses of 18 U.S.C. § 1030(c)(2)–(c)(4) and the civil
action of § 1030(g), compiled from a machine-lifted copy of the section (United
States Code, 2023 Edition, current through 2024-01-03).

This pack is not legal advice. It checks consequences of a human-authored
encoding of the text; it does not decide what "without authorization" or
"exceeds authorized access" means, which is where most CFAA litigation sits
(see *Van Buren v. United States*, 593 U.S. 374 (2021)).

## Pipeline

```text
GovInfo HTML ──uscode_lift.py──▶ lifted provision graph ──┐
 (sources/…sec1030.htm)          (lifted/usc-t18-s1030.json)│
                                                           ▼
                          rules.json ──rules_ir.py──▶ trace check ──▶ smt2/*.smt2 ──▶ Axeyum
                     (provision-keyed rules)          (anchors, literals,             (checked
                                                      dependencies, references)       evidence)
                                   │
                                   └──▶ Python evaluation ──▶ witnesses, query rows, validator sweep
```

1. [`scripts/uscode_lift.py`](../../../../scripts/uscode_lift.py) lifts the
   GovInfo rendering into an outline of 104 provisions with USLM-style
   identifiers (`/us/usc/t18/s1030/c/4/A/i/VI`), 29 internal cross-references
   resolved to 49 provision targets, 14 external citations, 13 definitions with
   their use sites, and 20 quantities (dollar thresholds with comparators,
   imprisonment maxima, periods, and counts). See
   [Lifting the U.S. Code](../../uscode/README.md).
2. [`rules.json`](rules.json) states 21 facts and 39 predicates. Each
   predicate names the provision it encodes and quotes an anchor phrase from it.
3. [`scripts/rules_ir.py`](../../../../scripts/rules_ir.py) refuses to emit
   anything until every anchor occurs verbatim in its provision, every numeric
   literal matches a quantity stated in that provision (value and comparator),
   every dependency between provisions is justified by the statute's structure,
   a resolved cross-reference, or a defined-term use, and every internal
   cross-reference leaving a modeled provision is consumed or declared out of
   scope. It then writes [`compiled.json`](compiled.json), the verbatim
   [`source.md`](source.md), and one SMT-LIB obligation per check.
4. `cargo test -p axeyum-solver --features full --test rules_as_code_examples`
   decides each obligation and re-checks its evidence.
5. [`scripts/validate-rules-as-code.py`](../../../../scripts/validate-rules-as-code.py)
   replays the witnesses and sweeps 221,184 fact patterns that cover every
   threshold region, requiring the rule model, the decision table in
   `rules.json`, and an independent clause-by-clause reading in the validator to
   agree on the applicable clauses and the maximum.

## Findings

| Check | Result | What it shows |
|---|---|---|
| `penalty-coverage-unsat` | unsat, certified | Every single-offense count under (a)(2)–(a)(7) is reached by some clause of (c)(2)–(c)(4). |
| `penalty-overlap-c2b-c2c-sat` | sat, replayed | (c)(2)(B) (5 years) and (c)(2)(C) (10 years) both reach a repeat (a)(2) offense with an aggravator: (c)(2)(A) excepts (B), but (B) has no first-offense limit. The model takes the larger maximum, an explicit modeling choice. |
| `value-threshold-mismatch-sat` | sat, replayed | $5,000 meets the (c)(4)(A)(i)(I) loss test ("aggregating at least $5,000") but not the (c)(2)(B)(iii) value test ("exceeds $5,000"). |
| `civil-gate-within-felony-factors-unsat` | unsat, certified | Conduct that opens the (g) civil gate always satisfies a (c)(4)(A)(i) factor. |
| `civil-gate-excludes-factor-vi-sat` | sat, replayed | The converse fails: damage to 10 or more protected computers (factor (VI)) supports the 10-year maximum of (c)(4)(B), but (g) lists only subclauses (I)–(V), so no civil action lies on that factor alone. |
| `max-term-monotone-unsat` | unsat, certified | For a fixed offense, adding an aggravating fact never lowers the maximum. |
| `implementation-equivalence-unsat` | unsat, certified | An independently written decision table agrees with the provision-keyed model on every input. |
| `buggy-implementation-counterexample-sat` | sat, replayed | The same table with `>= 5000` for (c)(2)(B)(iii) is wrong at exactly $5,000: 5 years instead of 1. |

## Reuse

The six harm factors of (c)(4)(A)(i) are encoded once (`harm_I` … `harm_VI`).
(c)(4)(A) uses them directly; (c)(4)(B) reaches them through the resolved
cross-reference "subclauses (I) through (VI) of subparagraph (A)(i)"; and (g)
reaches five of them through "subclauses (I), (II), (III), (IV), or (V) of
subsection (c)(4)(A)(i)". Because the dependency graph is checked against the
lifted cross-references, a model that let (g) consume factor (VI) is rejected
before any solver runs:

```text
predicate civil_factor_I_V (/g) uses harm_VI (/c/4/A/i/VI) with no textual justification
```

## Files

- [README.md](README.md): this page.
- [source.md](source.md): the modeled provisions, verbatim, generated from the lift.
- [model.md](model.md): the encoding and its modeling choices.
- [checks.md](checks.md): each obligation and how it is checked.
- [expected.md](expected.md): witnesses and expected results.
- [rules.json](rules.json): the provision-keyed rule model.
- [compiled.json](compiled.json): generated trace (dependency edges, references, obligations).
- [metadata.json](metadata.json), [expected.json](expected.json): validator inputs.
- `smt2/`: generated SMT-LIB obligations.

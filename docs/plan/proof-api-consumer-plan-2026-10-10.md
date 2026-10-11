# Proof export, SMT APIs and Rules-as-Code plan — 2026-10-10

Implementation detail for EVD-5/EVD-6 and CON-5/CON-6/CON-7. These are proposed
milestones; the [audit](user-feedback-audit-2026-10-10.md) records evidence and
[PLAN.md](../../PLAN.md) owns scheduling. Read the
[foundational DAG](../research/08-planning/foundational-dag.md) before adding any
public syntax, sort, evidence artifact or proof route. Public contracts need ADRs.

## EVD-5: make existing SAT certificates useful from Python

Inventory fresh-build results for raw CNF, pure Boolean terms, BV bit-blasting,
SMT text and mixed-theory solving. For each, identify verdict API, certificate
API, source-to-CNF map, DRAT availability, LRAT availability and replay method.
Existing `UnsatProof` exposes DIMACS/DRAT/optional LRAT and byte accessors; adding
another export object should require a concrete missing contract.

Clarify the user's meaning of "SAT trace": LRAT certifies an UNSAT refutation;
a SAT model is replayed; decisions/propagations are a diagnostic event stream.
For clause IDs, preserve the DIMACS input order, stable derived IDs, ordered
premises and deletions. Bind the refutation to the exact original query and CNF
mapping; a clausal proof alone does not certify an unchecked theory reduction.
Reuse existing CNF and lift artifacts wherever possible.

First delivery is a Python example exporting current certificates to files and
rechecking them without the binding's solver. Register one positive LRAT case
and one guaranteed DRAT-only case; optional LRAT must remain honest `None`.
Missing RAT elaboration belongs to EVD-4; any event-stream API needs its own
bounded contract, not a claim that a debug log is a proof.

**Exit:** route census cites fresh commands/results; exported LRAT is accepted
by a pinned independent checker (for example the
[DRAT-trim LRAT checker](https://github.com/marijnheule/drat-trim/blob/master/lrat-check.c));
tampered clauses/hints/source binding fail;
no absent or inconclusive check returns success. SAT witnesses replay against
the original terms. Document supported routes and remaining gaps precisely.

## EVD-6: Boolean and arithmetic proof composition

### A0 — regress the three reports on fresh HEAD

Use the [audit reproducers](user-feedback-audit-2026-10-10.md#reproducers).
Add paired SAT controls, plus unary `(- x)`, product `(* (- 1.0) x)` and
commuted product `(* x (- 1.0))`. Keep assertion syntax and order in the recorded
source. Compare parser IR, arithmetic linearization, selected emitter and final
proof checker to find the first loss. Existing emitter availability is not a
coverage claim; a test that accepts either a proof or `None` cannot close this gap.

**Exit:** a table gives exact per-route declines and a pinned mandatory proof
expectation for the first repaired cases. Distinguish parse, solve, production,
in-tree check, external check and kernel reconstruction.

### A1 — pure Boolean refutations

Reuse native CNF proof production and the existing Alethe resolution tail.
Verify whether the BV entry already accepts Bool-only assertions before adding a
new emitter. Preserve source assertions through simplification, Tseitin
introductions and clause mapping; certify rewrites explicitly. Exercise `not`,
`and`, `or`, implication, equivalence, `xor` and Boolean `ite` with source-bound
small formulas and constants.

**Exit:** `p` plus `not p` and a nontrivial resolution example emit proofs that
pass the in-tree checker and pinned Carcara, with no holes. Deleting a premise,
changing a pivot or substituting a different query rejects. A SAT control cannot
emit an accepted refutation. Bound proof work and return a production decline
on exhaustion.

### A2 — negative real multiplication

If `(* (- 1.0) x)` is linearized for solving but not proofs, share a specified
linearization contract and emit a checked rewrite bridge, rather than assuming
the two terms are syntactically interchangeable. Include zero, positive and
negative coefficients, operand order, nested negation and mixed Int/Real numeral
coercion. Do not turn variable-times-variable multiplication into an LRA rule.

**Exit:** the contradictory positive-product example emits a source-bound
arithmetic proof; the negative/zero SAT controls remain satisfiable. A changed
coefficient or omitted normalization bridge is rejected by targeted controls.

### A3 — Boolean+LIA composition

Build a Boolean resolution spine carrying checked arithmetic theory lemmas.
Start with the audit's disjunction case and one truly integer-only contradiction
(e.g. `2*x = 1`); Farkas infeasibility alone cannot justify the latter.
Inventory existing cuts, branch certificates and `lia_generic` checking before
selecting the export mechanism. Local `lia_generic` is not automatically a
portable Alethe rule. Elaborate integer lemmas into supported rules or retain an
explicit internal-only artifact class until portability is demonstrated.

[cvc5's current Alethe documentation](https://cvc5.github.io/docs/latest/proofs/output_alethe.html)
names linear arithmetic support and [Carcara](https://github.com/ufmg-smite/carcara)
provides checking/elaboration, but neither substitutes for testing Axeyum's exact
rules. Pin producer/checker commits and fail on holes or unsupported rules; do
not infer portability from the `.alethe` suffix.

**Exit:** Boolean+linear and integer-only examples have checked theory lemmas
and a closed refutation; wrong cuts, omitted branches and weakened integer
premises reject. Publish internal, external and kernel results separately.

## CON-5: explicit OMT semantics and trustworthy answers

### O0 — stop objectives disappearing

Freshly reproduce bounded maximize/minimize through Python solve, model/value
queries, session commands, CLI and explicit Rust optimizer APIs. Verify parser
objective retention across push/pop/reset and multiple `check-sat` commands.
Decide in an ADR whether generic satisfiability APIs reject OMT scripts or dispatch
to an explicitly typed optimization result. Plain `sat` and a feasible value
must not be presented as an optimum. Unsupported Real objectives, soft constraints
and objective modes must fail explicitly until implemented.

**Exit:** maximizing `x` over `[0,10]` yields a declared optimal result at 10
through the supported route, or an explicit unsupported-optimization result;
no route silently produces 0 as the answer to that optimization request.

### O1 — thread budgets and repair unboundedness classification

Both text optimization entry points currently discard `SolverConfig` and use
unconfigured engines. Pass one shared deadline through parsing, bound search,
all objectives and evidence checking. Audit `MAX_DOUBLINGS`, arithmetic overflow
and limit exits in `maximize_lia_with_config`: reaching a resource/representation
ceiling must return unknown, never prove unboundedness. Genuine unboundedness
requires a checked ray or another explicit mathematical witness.

**Exit:** bounded wide objectives do not become unbounded because of overflow;
expired budgets become resource-limited; finite, infeasible, unbounded and unknown
cases each have positive and negative controls. Budget propagation tests measure
actual work or deliberate exhaustion, not fragile elapsed-time thresholds.

### O2 — Python OMT result and gold-answer criteria

Expose selected Int/BV optimization functionality with exact values and a model,
objective direction and sort, chosen box/lexicographic semantics, completion,
and evidence status. The existing Rust API's default independent/box behavior
must not silently replace a consumer's lexicographic expectation.
[Z3's optimization guide](https://microsoft.github.io/z3guide/docs/optimization/intro/)
is the primary comparison reference; pin versions for differential fixtures.

For an integer maximum `v`, gold credit requires a replayed feasible model at
`v` and checked UNSAT for a strictly better value (`objective > v`); minimize
uses `< v`. Bind both to the same original constraints and prior fixed objectives
for lexicographic results. Use analogous unsigned/signed BV order consistently.
A future Real optimizer must separately handle strict suprema and unattained
bounds. Do not reuse integer attained-optimum semantics for that future API.

**Exit:** bounded optimum, tie, minimize, conflicting objectives, infeasible,
unsupported sort and resource-limited cases round-trip through Python; independent
checks reject altered values, models or objective order. Gold-answer generation
is enabled only for the audited evidence-bearing slice.

## CON-6: parser convenience and corrected capability notes

Bare `-1` is compatibility syntax, while canonical SMT-LIB integer values use
unary subtraction ([Ints specification](https://smt-lib.org/theories-Ints.shtml)).
Document that distinction and decide how unquoted signed atoms interact with
symbols and quoted identifiers before adding a convenience path. Reuse the
unbounded numeral constructor; never limit negative inputs to `i128` when
positive numerals already use `WideInt`. Specify decimal and Int-to-Real coercion
separately. Emit canonical `(- n)` in SMT serialization.

Test `-1`, `(- 1)`, zero, `i128` boundaries, wider negative numerals, quoted
`|-1|`, declared-symbol precedence, mixed Int/Real contexts, let/macro terms and
writer/parser round trips. Pair each acceptance with a malformed-input control.
`abs` and `distinct` already parse; document their actual sort/coercion and arity
coverage and test results, rather than listing them as absent.

**Exit:** fresh public parser/Python/CLI tests show the specified convenience
behavior and canonical syntax remains stable. Resolve the exact `notes/80` path
before correcting that historical note; the audit holds the correction meanwhile.

## CON-7: typed dates and one statute-backed template

### R0 — Date domain and Python rules facade

Propose a distinct Python symbolic Date type lowered to existing Int day ordinals,
with a checked Gregorian conversion and retained source-sort/lift metadata.
A native IR Date sort is a separate ADR decision, not a prerequisite for the
first API. Specify representable range, leap years, order, date ± integer days,
and date difference in days. Python's
[`date.toordinal` contract](https://docs.python.org/3/library/datetime.html#datetime.date.toordinal)
is a reference for the facade's conversion/round-trip tests; decide explicitly
whether the symbolic range matches Python dates. Keep durations distinct from dates; month/year
arithmetic needs an explicit convention. Reject invalid dates and mixed date,
number or datetime/timezone operations. Preserve Date identity in model lifting.

Expose pack loading, typed input binding, evaluation, obligation checking and
source-linked outcomes using the existing metadata, query generation and proof
routes. Missing facts remain explicit; complete evaluation cannot assume absent
facts are false. Reuse the seven packs before creating a new framework.

**Exit:** at least one existing temporal pack works from Python; models lift
back to dates; leap day, invalid date, year boundary and effective-interval
endpoints have concrete discriminating tests. Checked/replayed/inconclusive
statuses retain their meaning through the API.

### R1 — sourced computation-of-time pack

Recommended bounded template: [Minnesota Statutes §645.15](https://www.revisor.mn.gov/statutes/cite/645.15)
(the official page researched here identifies the 2025 edition). It excludes
the first day, includes the last, and omits a last day falling on Saturday,
Sunday or a legal holiday. Its explicit references to
[§645.13](https://www.revisor.mn.gov/statutes/cite/645.13) and
[§645.14](https://www.revisor.mn.gov/statutes/cite/645.14) must be reviewed before
choosing the modeled subdomain. This is a proposed template selection, not a
legal applicability finding or an implemented pack.

Pin source edition/text identity and retrieval date; record jurisdiction,
exceptions, holiday-calendar authority, applicability assumptions and effective
interval evidence. Do not infer historical effective dates from retrieval time.
Carry cross-reference exclusions explicitly; model holiday facts as sourced input
until a complete calendar is supplied. A bounded holiday search that exhausts its
range must decline, not return an arbitrary deadline.

Pack contents: source citations/paraphrase; clause-to-predicate crosswalk;
temporal semantics; executable reference evaluator; typed Python example;
SMT obligations; expected witnesses and proof routes; limitations. Include a
minimal metadata template that future statute packs can copy.

**Exit:** weekday/weekend/holiday, leap-day/year-crossing and applicability
boundary examples replay; solver checks consistency, deterministic deadline,
minimal admissible endpoint and agreement with an independently written reference
evaluator over a stated bounded domain. Every generalized UNSAT claim names and
checks its proof route. Existing validator/dashboard integration stays intact;
only explicitly modeled clauses receive coverage credit.

## Validation obligations

For implementation: workspace library tests plus full-feature solver library
tests; SMT front-door changes also require the corpus and four string suites
listed in AGENTS.md. Linear arithmetic changes require all five z3 differential
fuzzes, and dispatch changes require `progress_frontier`. Use the serialized
cargo wrapper and confirm nonzero counts. Run fresh Python suites, applicable
external proof checks, rules validator and documentation generators. Mutate
checker guards only in snapshots, requiring the targeted one-test failure.
These are planned gates, not claims that this documentation session ran them.

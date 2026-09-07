# ADR-1704: A CDCL(T) `unsat` is TWO streams — a Boolean refutation over CNF **plus the enumerated theory lemmas**, counted

Status: accepted
Index-summary: A theory lemma is not RUP, so a CDCL(T) refutation is checked as a Boolean DRAT/LRAT stream over the CNF **extended by the enumerated theory lemmas as input clauses**, plus a per-lemma theory discharge. The lemma count is a printed metric, never zero-by-omission; a refutation modulo N lemmas is never reported at `SatRefutation`'s assurance level. New `TrustId::SatRefutationModuloTheory`. Boundary pinned by `crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs` (11 tests; three mutations killed 2, 1 and 3 tests respectively).
Index-status: accepted
Date: 2026-09-06

## Context

[ADR-1703](adr-1703-the-native-core-is-the-sat-engine-batsat-is-demoted-to-a-differential-oracle.md)
made the native CDCL core the SAT engine on every path. Its identity, stated in
[ADR-0012](adr-0012-proof-producing-sat-core.md) and restated in
[`docs/internals/cnf-and-sat.md`](../../internals/cnf-and-sat.md) under "What
that changed about UNSAT assurance", is that **every learned clause is RUP
against the CNF**, so the learned sequence *is* a DRAT proof and `check_drat` —
or, with hints, the linear `check_lrat`
([ADR-0613](adr-0613-unsat-is-certified-by-following-hints-not-by-searching-for-them.md))
— makes `unsat` sound regardless of search bugs. "Proofless UNSAT" stopped being
a category the crate can produce.

Slice **S7** of the
[SMT parity plan](../../plan/smt-parity-plan-2026-09-05.md) moves every theory
route off `CdclT` and onto that core. The
[slice-2 design memo §6.1](../../plan/adr-1701-slice-2-design-2026-09-05.md)
names the obstacle and declines to resolve it:

> The native core's identity is that every learned clause is RUP by
> construction… **A theory lemma is not RUP against the CNF.** Putting one into
> the learned database silently converts the emitted proof from a refutation
> into a refutation-modulo-theory, with nothing in the artifact saying so.

That is not a stylistic complaint. It is the exact failure this repository's
evidence discipline exists to prevent: a checker that returns `Ok(true)` over an
artifact whose real claim is weaker than the label on it. `check_drat` accepting
`CNF ∪ {lemma} ⊢ ⊥` while the artifact is named "DRAT refutation of CNF" is a
checker that cannot fail on the axis that matters.

Two further facts constrain the answer, both read from the tree:

1. **`CdclT` emits no proof at all today.** `crates/axeyum-solver/src/cdclt.rs`
   contains no DRAT, `UnsatProof` or proof-emission code; `solve` returns a
   three-valued `Outcome` with no proof out-parameter, and the three `Unsat`
   returns (`cdclt.rs:1413`, `:1438`, `:1460`) are bare. Every consumer
   collapses to `CheckResult::Unsat` (`lra_theory.rs:283`, `euf_egraph.rs:800`,
   `dl_online.rs:2079`, `string_theory.rs:1063`), reaching the front door as
   `Evidence::Unsat(None)` with empty `trusted_steps`. So there is no proof to
   regress — only one to gain.
2. **The two-stream shape already exists in this tree, one level up.**
   `ArithDpllRefutation` (`crates/axeyum-solver/src/dpll_lia.rs:161`) and
   `LraDpllRefutation` (`crates/axeyum-solver/src/dpll_t.rs:349`) each carry a
   `skeleton` plus an explicit `lemmas: Vec<Vec<…LemmaLiteral>>`, and their
   `verify` (`dpll_lia.rs:322`, `dpll_t.rs:565`) discharges the two halves
   separately. The trust ledger already grades that shape: `lra-dpll` is
   "lazy-SMT skeleton + Farkas-certified theory lemmas", pedantic 9, certified.
   This ADR is that contract, moved down to the CNF/DRAT level where S7 needs
   it, and given a counted assumption list.

## Decision

**A CDCL(T) `unsat` artifact is two streams, and the checker composition is
`check_lrat` over `CNF ∪ lemmas` followed by a per-lemma theory discharge. The
number of lemmas is carried in the artifact, printed beside the check outcome,
and derived from the artifact rather than asserted by the producer. A refutation
modulo N ≥ 1 theory lemmas is never reported at the assurance level of a pure
propositional refutation.**

### 1. What the artifact contains

| Field | Content |
|---|---|
| `cnf` | the Boolean CNF exactly as encoded, unchanged |
| `lemmas` | the enumerated theory lemmas, in emission order; each a clause over the *same* CNF variables, plus the theory that produced it and its theory-level explanation |
| `boolean_stream` | a DRAT (or LRAT) proof whose input formula is `cnf` **extended by `lemmas` appended as additional input clauses**, in that order |

The extended formula is `cnf` followed by `lemmas`; nothing is interleaved and
nothing is reordered. That makes the assumption count a subtraction on the
artifact — `lemmas.len() == extended.len() - cnf.len()` — rather than a number
a producer can under-report. The
[boundary suite](../../../crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs)
asserts exactly this in
`the_theory_lemma_count_is_read_off_the_artifact_not_asserted`.

Per lemma, the recorded theory-level explanation is:

| Theory | Explanation object |
|---|---|
| LRA / mixed linear | a Farkas combination: nonnegative multipliers over the asserted atoms whose positive combination is a false constant relation |
| DL (IDL/RDL) | a negative cycle, recorded as the unit-multiplier Farkas combination over the cycle's edge relations |
| EUF | a congruence chain: the `Input`/`Congruence` steps relating the two sides |
| any other | *absent* — the lemma is carried with its theory label and no explanation, and is counted as undischarged |

An absent explanation is a legal artifact. What is illegal is an absent
*lemma*: a clause that entered the search from a theory and does not appear in
`lemmas`.

### 2. What a checker accepts, and what it declines

```
check(artifact):
  extended  := artifact.cnf ++ artifact.lemmas          # order is part of the contract
  boolean   := check_lrat(extended, artifact.boolean_stream)   # or check_drat
  discharged, unchecked := for each lemma: theory_checker(lemma) or "no checker"
```

- **Accepts as `Verified`** iff `boolean == Ok(true)` **and** `unchecked == 0`
  **and** every discharged lemma verified. This is the only outcome that
  licenses trusting the `unsat` on the evidence alone
  ([ADR-0384](adr-0384-honest-evidence-front-door.md)'s rule).
- **Accepts the Boolean half only**, and reports
  `checked modulo <N> unchecked lemmas`, when `boolean == Ok(true)` and
  `N = unchecked > 0`. The `EvidenceCheck` value is **not** `Verified`; it is
  `NothingToCheck(NoCheckReason::UndischargedTheoryLemmas)` — a new
  `NoCheckReason` — because a partial check is not a pass. `N` is printed
  regardless.
- **Declines** (`EvidenceCheck::Failed`, a soundness alarm) on any of the
  failure modes in §4.

`check_drat` and `check_lrat` are **unchanged** by this ADR. Neither gains a
theory arm, neither learns a new step kind, and the trusted base does not grow
by a line. The whole contract is a statement about which formula the existing
checkers are handed.

### 3. How the assurance level is named

**A new trust id, `TrustId::SatRefutationModuloTheory`**, with
`is_certified == false` until the per-lemma discharge is complete for the query.

Reusing the existing `TrustId::SatRefutation` ("CNF UNSAT from the CDCL core",
pedantic 9, certified) is exactly the relabelling this ADR forbids: that id's
meaning is a refutation of the CNF, and a refutation of `CNF ∪ lemmas` is a
strictly weaker statement. One id cannot carry both without the ledger becoming
unreadable at the only place it is load-bearing.

The lemma discharges reuse the ids the theories already have — `TrustId::Farkas`
for LRA and DL, and (when it lands) the EUF congruence id — so a fully
discharged CDCL(T) refutation appears in the ledger as
`SatRefutationModuloTheory (certified) + Farkas (certified)` and not as one
opaque row.

**The metric.** Beside the existing `certified` / `checked` columns the evidence
report carries `theory_lemmas = <total>` and `theory_lemmas_unchecked = <N>`,
both computed from the artifact. A route that reports `unsat` with
`theory_lemmas = 0` is producing a pure propositional refutation and is graded
at `SatRefutation` as before; the field is therefore never absent and never
zero-by-omission. This is the "trusted base, not output volume" rule applied to
theory reasoning: the number that must go **down** as S7 lands more per-theory
checkers is `theory_lemmas_unchecked`, and nothing a producer writes can move
it.

### 4. Failure modes, and what each prints

| # | Condition | Outcome | Printed |
|---|---|---|---|
| 1 | the Boolean stream does not check over the extended formula | `Failed` | `theory-lemma-contract: boolean stream rejected (<DratError/LratError>)` |
| 2 | the Boolean stream checks but derives no empty clause (`Ok(false)`) | `Failed` | `theory-lemma-contract: boolean stream verified but derived no empty clause` |
| 3 | a lemma's theory certificate fails to verify | `Failed` | `theory-lemma-contract: lemma <i> (<theory>) failed <checker>` |
| 4 | `extended` is not `cnf` followed by `lemmas` (a lemma hidden among the input clauses, or a listed lemma absent from the extended formula) | `Failed` | `theory-lemma-contract: lemma list does not match the extended CNF (<n> listed, <m> extra clauses)` |
| 5 | a lemma carries no explanation, or its theory has no checker | `NothingToCheck(UndischargedTheoryLemmas)` | `theory-lemma-contract: checked modulo <N> unchecked lemmas (<theory>: <k>, …)` |
| 6 | `lemmas` is empty | as today | graded at `SatRefutation`; `theory_lemmas = 0` |

Mode 4 is the one that carries the contract. Without it a producer could append
its lemmas to `cnf` and report `theory_lemmas = 0`, which is mode 6's label over
mode 5's artifact — the precise dishonesty this ADR exists to make impossible.

### 5. What S7 may NOT do

Two prohibitions, stated as outcomes so that a violation is a test failure and
not a matter of taste:

1. **S7 may not learn a theory lemma into the RUP stream unlabelled.** Any
   clause that enters the clause database from a theory rather than from
   1-UIP resolution over input clauses must appear in `lemmas`. Enforcement is
   mode 4: a lemma inside the CNF is a mismatch between the two halves of the
   artifact, and it is checked, not trusted.
2. **S7 may not report a refutation-modulo-theory at the assurance level of a
   pure DRAT refutation.** `theory_lemmas > 0` and `TrustId::SatRefutation`
   must never co-occur, and `theory_lemmas_unchecked > 0` must never produce
   `EvidenceCheck::Verified`.

## Evidence

The contract's boundary is pinned by
[`crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs`](../../../crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs)
(11 tests, no production change). The fixture is three Boolean variables
abstracting a difference-logic negative cycle:

```text
x1 == (a - b <= 0)   x2 == (b - c <= 0)   x3 == (c - a <= -1)
CNF:    (x1) & (x2) & (x3)              -- SATISFIABLE; only the theory refutes it
lemma:  (~x1 | ~x2 | ~x3)               -- the negative cycle, as DlTheory would emit it
```

Measured, not asserted:

- `check_drat(CNF, [Add(lemma)])` = `Err(StepNotVerified { step: 0 })`. The
  lemma is neither RUP nor RAT against the CNF — the RAT check fails on every
  pivot because each resolvent is the lemma itself, which is not RUP.
- `check_drat(CNF, [Add(lemma), Add([])])` = the same error at step 0: the
  whole refutation-modulo-theory does not check as a plain DRAT refutation.
- `check_lrat(CNF, [Add{id:4, lemma, hints:[]}, …])` =
  `Err(StepNotVerified { id: 4 })`. No antecedent chain over the CNF justifies
  it, because none exists.
- `check_drat(CNF ++ [lemma], [Add([])])` = `Ok(true)`, and
  `check_lrat(CNF ++ [lemma], [Add{id:5, [], hints:[1,2,3,4]}])` = `Ok(true)`.
  The same refutation is accepted the moment the lemma is an **input** clause.

Both directions are shown to have teeth. Mutations were applied to a
`lane-snapshot.sh` copy (never the shared tree), each restored and the baseline
re-confirmed at 11/11 afterwards; every run collected 11 tests, matching the
baseline, so none is a "did not build" or "did not run":

| Mutation | Killed |
|---|---|
| `drat.rs` `is_rat` stops requiring its resolvents to be RUP (the checker now accepts the lemma as derived) | **2**: `drat_rejects_the_theory_lemma_as_a_derived_addition`, `drat_rejects_a_refutation_that_learns_the_theory_lemma_unlabelled` |
| `lrat.rs` `verify_addition` accepts an addition whose hint chain never reaches a conflict | **1**: `lrat_rejects_the_theory_lemma_as_a_derived_addition` |
| the fixture deletes the lemma from the extended input CNF | **3**: both `*_accepts_the_refutation_when_the_lemma_is_an_input_clause`, and `the_theory_lemma_count_is_read_off_the_artifact_not_asserted` |

The suite also carries its own vacuity controls: a genuinely RUP addition
(`(x1 | ~x2)`) and a genuinely hinted LRAT addition over the *same* skeleton are
accepted, so the rejections above are about the theory lemma and not about the
checker refusing everything.

### Which theories already have a checkable lemma form

Read from the code, with references:

**Have one.**

- **LRA.** `FarkasCertificate` (`crates/axeyum-solver/src/lra.rs:474`:
  `atoms`, `multipliers`, `origins`, `vars`) with
  `FarkasCertificate::verify` (`lra.rs:498`) — pure exact-rational, no arena, no
  search, every operation `checked_*` so an overflow returns `false`. This is
  the best-shaped per-lemma discharge object in the tree and needs no new work
  beyond a slot to carry it.
- **Difference logic (IDL/RDL).** Already re-expresses each negative cycle as a
  unit-multiplier `FarkasCertificate`: `cycle_certificate`
  (`crates/axeyum-solver/src/dl_online.rs:1159`), and `DlTheory::verified`
  (`dl_online.rs:1516`) is literally
  `cycle_certificate(steps, &[]).is_some_and(|c| c.verify())`, called before any
  conflict is reported. **The certificate is built, verified, and then
  dropped**, because `TheoryExplanation` has nowhere to put it. Retaining it is
  plumbing, not new proof theory. The query-level export already exists for the
  conjunctive case (`dl_online.rs:1347`, `evidence.rs:2554`); the
  Boolean-structured case is the bare `Evidence::Unsat(None)` at
  `evidence.rs:2615` that this ADR is designed to replace.
- **EUF.** A structured congruence chain exists — `ProofStep`
  (`crates/axeyum-egraph/src/lib.rs:206`: `Input { a, b, reason }` /
  `Congruence { a, b, args }`) from `EGraph::explain_steps` (`:1154`) — together
  with an **independent** re-checker `check_congruence` (`:1311`) that re-runs
  congruence closure from scratch over the premises. Today `check_congruence` is
  called only on the offline route (`euf_egraph.rs:1352`, `:2398`); the online
  CDCL(T) path never invokes it. So EUF has the object *and* the checker and is
  missing only the wiring.

**Do not have one.**

- **Strings.** `string_theory.rs:1063` returns a bare `CheckResult::Unsat`; there
  is no per-lemma certificate and no checker. Its lemmas land in the
  `theory_lemmas_unchecked` count, which is the honest report.
- **NIA/NRA.** The self-checking certificates that exist
  (`SosCertificate`, `nra_real_root.rs:6470`;
  `HandelmanRefutationCertificate`, `nra_handelman_cert.rs:208`; and five more
  with arms at `evidence.rs:1183-1232`) are **whole-query** refutations, not
  per-lemma objects. They are not a discharge route for a CDCL(T) lemma.
- **The offline LIA/LRA lazy-SMT routes** (`ArithDpllRefutation`,
  `LraDpllRefutation`) enumerate their lemmas but discharge each by
  **re-solving** it with the theory's exact procedure, not by checking a carried
  certificate. That is sound and it is the prototype for this contract's shape,
  but at CDCL(T) scale re-solving every lemma is the inverted cost ADR-0613 was
  written about. Per-lemma certificates are the reason this ADR carries the
  explanation rather than only the clause.

### The one structural change the theories need

`TheorySolver`'s conflict channel is a bare `Vec<TheoryLit>` — "`¬⋀lits` is a
valid lemma" — with no certificate slot anywhere:
`assert` returns `Result<(), Vec<TheoryLit>>`
(`crates/axeyum-solver/src/euf_egraph.rs:80`), `final_check` returns
`FinalCheckOutcome { Sat | Conflict(TheoryExplanation) | Unknown }` (`:181`),
and `TheoryExplanation` (`:164`) has exactly two arms, both resolving to
materialized literals. Carrying a discharge object needs a third arm or a
widened return. DL already computes and discards exactly such an object for
every conflict; that is the measurement that says the slot, not the certificate,
is what is missing.

## Prior art

*Added 2026-09-06 as an addendum. It changes no part of the decision above; it
records the published work this design coincides with, and the one place where
the comparison puts a new constraint on future work.*

The design decided above — a propositional refutation below, enumerated theory
lemmas above, discharged separately — is the published **eDRAT** approach:

> S Hitarth, Cayden Codel, Hanna Lachnitt, Bruno Dutertre. **Extending DRAT to
> SMT.** In *Formal Methods in Computer-Aided Design (FMCAD) 2024*, pages
> 18–28. TU Wien Academic Press. ISBN 978-3-85448-065-5.
> DOI [10.34727/2024/isbn.978-3-85448-065-5_8](https://doi.org/10.34727/2024/isbn.978-3-85448-065-5_8)
> (open access, CC BY 4.0).

This ADR was written without it. The shape here was derived one level up in
this tree, from `ArithDpllRefutation` / `LraDpllRefutation` (§Context item 2),
not from the paper. So the agreements below are **convergence, not adoption**,
and the disagreements are choices, not oversights.

### What they do

eDRAT is a *format*: DRAT plus SMT-LIB-shaped `(declare-sort …)` /
`(declare-fun …)` term declarations, two new commands (`define-let` naming a
term, `define-literal` mapping a DIMACS variable to an atom), and three clause
prefixes — `a` for an input clause, `t` for a theory lemma, bare for a Boolean
reasoning clause, `d` for a deletion. Their toolchain, VALIDO, checks it in two
steps (their Algorithm 1):

1. Build one CNF from the `a` clauses **and** the `t` clauses — "we treat all
   the theory lemmas as axioms and add them to the input clauses" — and run a
   restricted DRAT-trim over the Boolean stream, which also returns an unsat
   core.
2. Discharge the theory lemmas **that appear in that core**, via an *untrusted
   elaborator* (Rust) that rediscovers a certificate per lemma, plus a
   *validator* (Lean 4, proved sound) that checks the certificate. QF_LRA
   elaborates to a Farkas combination found by simplex; QF_UF to a congruence
   certificate checked by a union-find in Lean.

Their measurements: eDRAT proof generation costs under 10% over proofless cvc5,
against 2x–17x for cvc5's ALF and LFSC; checking is 3x/15x faster than
LFSC/ALF on QF_LRA and 80x/120x on QF_UF.

### Where this contract agrees with them, independently

- **The two streams themselves**, and the fact that they are checked by
  different machinery.
- **Hoisting the lemmas into the input formula rather than teaching the
  propositional checker about theories.** Their step 1 sentence above is this
  ADR's §1 `extended := cnf ++ lemmas`, arrived at separately. Both designs
  therefore reject a theory-aware DRAT dialect for the same reason: it would put
  a decision procedure inside the trusted checker (this ADR's alternative (1)).
- **The per-lemma discharge objects.** Farkas for LRA, a congruence chain for
  EUF — the same two theories, the same two objects, and in both cases the
  cheap ones to have first.
- **Coarse granularity on purpose.** Their motivation is production overhead;
  ours is that ADR-0613 chose a smaller checker over a faster one. Same
  artifact, two different arguments for it.
- **The trusted base is the validator, not the producer.** Their elaborator is
  explicitly untrusted; here the search is untrusted by identity.

### Where it differs, and why

1. **We add no format and no checker arm; they added both.** eDRAT needs a
   portable on-disk artifact a third party can consume, so it pays for new
   syntax *and* a modified DRAT-trim. This ADR's §2 hands `check_drat` /
   `check_lrat` an ordinary formula and changes neither by a line. The cost of
   our choice is exactly what theirs buys: no external referee can read our
   artifact. That is already named here as the Alethe route (alternative (1)),
   and it stays a portability project rather than a soundness one.

2. **Who computes the certificate.** eDRAT emits the lemma bare and has an
   elaborator *rediscover* the Farkas coefficients afterwards by solving an LP.
   This ADR requires the **producer** to carry the explanation. We chose that
   because DL already builds and verifies a Farkas object per conflict and
   throws it away (`dl_online.rs:1159`, `:1516`), so retaining it is plumbing,
   while rediscovery is the inverted cost ADR-0613 was written against. Their
   own results are evidence for our side of this: VALIDO is *slower* than the
   ALF checker on the QF_LRA families whose lemmas run to several hundred atoms,
   and they attribute it to their simplex recomputing the coefficients. The bill
   for our choice lands on the producer instead, which is the axis eDRAT
   optimized — mitigated here by making emission a per-call choice
   (`prove_unsat`, §Consequences).

3. **Which lemmas must be discharged.** eDRAT discharges only the lemmas in
   DRAT-trim's unsat core. This ADR discharges **every listed lemma** or counts
   it in `theory_lemmas_unchecked`; there is no core-pruning step. We are
   strictly more conservative and strictly more expensive. See item 5.

4. **A distinction our certificate carries and theirs cannot.** VALIDO returns
   success, "DRAT Proof Check Failed", or "Theory Lemma Validation Failed"; it
   has no way to say *checked modulo N undischarged lemmas*, because it is only
   instantiated for theories it can fully discharge. This ADR's
   `SatRefutationModuloTheory`, `NoCheckReason::UndischargedTheoryLemmas`, and
   the counted `theory_lemmas_unchecked` exist precisely so a partial check
   cannot present as a pass — which is what we need and they do not, because our
   strings and nonlinear routes have lemmas with no checker at all.

5. **RAT — the one place the comparison changes something.** eDRAT *restricts*
   its propositional checker to RUP additions and rejects RAT, on the stated
   ground (their §III-B, Example III.2) that adding a RAT clause can eliminate
   Boolean models, so a formula satisfiable in `T` can become `T`-unsatisfiable
   after a RAT addition. This contract hands the **unchanged** `check_drat`,
   which accepts RUP *or* RAT (`crates/axeyum-cnf/src/drat.rs`, and the boundary
   suite's mutation of `is_rat` kills two tests), the extended formula.

   Read against the contract as decided, the hazard does not reach us: the
   extended formula is **fixed before the stream is checked** (§1: `cnf`
   followed by `lemmas`, nothing interleaved, mode 4 enforcing it), every listed
   lemma is separately discharged or counted (§2), and the only propositional
   claim inherited is "`cnf ∪ lemmas` is unsatisfiable" — which DRAT establishes
   soundly with RAT included. eDRAT's hazard bites where a clause's status is
   judged against a formula that is not the one whose unsatisfiability is
   finally claimed, and core-pruning is exactly that situation.

   **So the constraint this comparison adds, recorded here rather than
   discovered later:** *if this route ever adopts eDRAT's core-pruning
   optimization — discharging only the lemmas in the unsat core — then the
   RUP-only restriction becomes load-bearing and `check_drat`'s RAT arm must be
   disabled on that route.* The two are a package; taking the cheap half alone
   is the unsound combination. Note that the LRAT arm of §2's composition is
   **already** RUP-only and would be unaffected: `check_lrat` rejects a RAT
   addition outright (`LratError::RatNotSupported`, `crates/axeyum-cnf/src/lrat.rs`,
   ADR-0382). The agreement there is accidental and worth keeping deliberate.

### Their limitation is our open hole

The paper states it in its own §I and §VII: eDRAT starts from CNF, and "the
preprocessing, simplification, and rewriting steps that SMT solvers perform to
convert formulas to CNF are not expressible in eDRAT." They name three
candidate bridges and commit to none — (a) emit a *separate* proof of the
preprocessing steps only, in ALF, noting that some useful preprocessing must
then be disabled (in cvc5, symmetry breaking is incompatible with LFSC/ALF
proof production); (b) translation validation, seeing preprocessing as a
compilation whose satisfiability preservation is validated per run, which they
note may need the solver to emit hints; (c) a provably correct preprocessor,
most effort and most benefit, with maintenance as the standing objection.

That is our hole too, one layer earlier: `axeyum-rewrite` is preprocessing and
produces no evidence. The published two-stream contract therefore covers
CNF-to-refutation and stops. One measurement of theirs is worth carrying into
that work: ALF and LFSC proofs *do* include preprocessing steps, and the paper
reports the resulting size difference is "significant mostly on easy problems"
— on hard problems resolution and theory lemmas dominate. Preprocessing
evidence is a correctness gap, not a scale problem.

## Alternatives

### (1) One proof format with labelled theory steps — rejected for now

Define a DRAT/LRAT dialect whose additions may be tagged as theory steps, and
have the checker either trust the tag or discharge it against the theory.

Rejected because it puts the theory *inside* the trusted checker.
`check_drat` is a few dozen readable lines and `check_lrat` is smaller still;
that readability is the entire basis of the trust story, and ADR-0613 chose a
*smaller* checker over a faster one for exactly this reason. A dialect with
theory steps either (a) trusts the tag, which is option (3)'s silence wearing a
proof format's clothes, or (b) links every theory decision procedure into the
checker, growing the trusted base by the size of the simplex and the e-graph.
Neither is a trade this repository makes. It also gains nothing option (2) does
not: the same lemmas, the same discharges, one artifact instead of two, and no
extra checking power.

**If a portable single-artifact form is ever wanted, the route is Alethe, not a
DRAT dialect.** `crates/axeyum-cnf/src/alethe.rs` already checks a resolution
core plus `eq_reflexive`/`eq_symmetric`/`eq_transitive`/`eq_congruent`, and its
resolution steps are discharged by the proof-producing SAT core with the
resulting DRAT re-checked by `check_drat` — so the composition this ADR
describes is already the way that checker works internally. Alethe is the format
veriT and cvc5 emit and Carcara checks, so it is the form an external referee
can consume. That is a portability project with an external cross-check as its
payoff, not a prerequisite for S7, and it does not change what must be recorded:
the lemmas and their explanations, which is what this ADR fixes.

### (3) Suppress proof emission whenever a theory is attached — rejected

This is what `CdclT` does today (no proof code at all, §Context item 1), so
adopting it is not a regression. It is rejected because it makes S7 a *loss*:
today's theory routes are proofless and stay proofless, while the Boolean half
of every CDCL(T) refutation — which the native core produces for free, by
construction — is thrown away. It also forecloses proof-producing SMT, which is
the "Lean parity" half of this project's stated target ("every unsat/valid
carries a machine-checkable proof"). Option (2) costs nothing that (3) saves:
the Boolean stream is emitted by machinery that already exists, and the lemma
list is a `Vec` the search already has in hand.

## Consequences

**Easier.**

- S7 can move CDCL(T) onto the native core without a silent assurance
  regression, because the artifact says what it is.
- Every CDCL(T) `unsat` gains a checked Boolean half immediately, from
  proofless (`Evidence::Unsat(None)`, empty `trusted_steps`) to
  `checked modulo N`. That is a strict improvement on day one, before any
  per-theory checker is wired.
- LRA and DL reach full discharge with plumbing only: DL already builds and
  verifies the Farkas object per conflict and throws it away.
- The remaining trust hole becomes a **number that goes down**
  (`theory_lemmas_unchecked`), visible per query, which is the shape this
  repository's metrics take.

**Harder.**

- `TheoryExplanation` must grow a way to carry a discharge object, touching the
  trait every in-tree theory implements. That is a real cost and it is the
  reason this ADR precedes S7 rather than following it.
- Retaining the lemma list costs memory proportional to the theory conflicts,
  which on a long CDCL(T) run is not negligible. The mitigation is the same one
  the proof stream already uses: emission is a per-call choice
  (`prove_unsat`), off by default on the warm path.
- A theory that emits many small lemmas now reports a large `theory_lemmas`.
  That is the honest number and it will look worse than today's silence. It is
  supposed to.

**Revisited when.**

- A per-lemma checker lands for strings, or the EUF wiring lands: the ledger row
  for `SatRefutationModuloTheory` moves toward `certified` and the revision is a
  ledger regeneration, not a new ADR.
- An external cross-check (Carcara) is wanted: that is the Alethe project noted
  under alternative (1), and it supersedes the artifact's *serialization*
  without changing what this ADR says must be recorded.

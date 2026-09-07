# Mathematical operating system: applicability and evidence roadmap

Date: 2026-09-07
Status: proposed extension within the accepted L0–L4 programme; no new dispatch authority
Evidence baseline: `a103b3db37ca976e0cc68acbe28031033ce0c4b2`

## Outcome and scope

Make the mathematical conditions under which a result can be used govern
selection, execution, checking, and reuse. An agent requesting a root should
receive a justified choice of theorem or computation, its remaining obligations,
and its evidence requirements. It should not receive an exact-root promise when
the selected result only bounds the residual.

“Operating system for mathematics” is an architectural aim, not a uniqueness
claim or a new foundation. Earlier systems already integrate mathematical
knowledge, heterogeneous services, proof planning, and reusable theory contexts.
This programme tests whether Axeyum can connect these responsibilities through
its existing admission boundary. It does not create a competing priority list:
L0 safety comes first, L1 binds identities, L2 uses those identities for selection,
L3 measures useful reuse, and L4 adds a checked external adapter.

The parent authorities remain [ADR-0717](../research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md),
the [graph roadmap](graph-directed-library-roadmap-2026-08-30.md), the
[safety roadmap](trusted-library-safety-roadmap-2026-08-30.md), the
[artifact roadmap](library-artifact-compatibility-roadmap-2026-08-30.md), and the
[discovery roadmap](definition-discovery-efficiency-roadmap-2026-08-30.md).
This document specifies an analysis destination pilot within that programme.

## Lessons from prior systems

These are design lessons, not comparative performance measurements. The cited
publications establish the precedent; they do not prove that every described
feature remains maintained or that Axeyum improves on it.

| Prior work | Existing contribution | Consequence for this programme |
|---|---|---|
| [MMT/OMDoc](https://arxiv.org/abs/1105.0548) and MathHub | Foundation-independent theory organization and theory morphisms; services over structured mathematical content | Name the theory context and its bindings. A common serialization or theorem title does not establish semantic identity. |
| [OpenDreamKit / Math-in-the-Middle](https://arxiv.org/abs/1603.06424) | Shared mathematical meaning across heterogeneous computational systems | Specify representation maps and their obligations before connecting CAS objects to `CReal`. |
| [Ωmega](https://user.informatik.uni-bremen.de/autexier/pub/JAL05.pdf) | Knowledge-based proof planning with heterogeneous reasoners | Make methods carry applicability conditions and justify their refinement into checked steps. Integration and planning are established precedents. |
| [Theorema](https://jfr.unibo.it/article/view/4568) | Proving, solving, and computing inside mathematical theory development | Evaluate a connected mathematical task, including explanation and reuse, rather than unrelated backend demos. |
| [IMPS](https://imps.mcmaster.ca/doc/cade-11-sys-desc.pdf) | Little theories and interpretations for contextual theorem reuse | A theorem's assumptions and an interpretation's obligations belong in the actual application check. |
| [LeanAgent](https://arxiv.org/abs/2410.06209) | An evolving database, curriculum, retrieval, and proof generation | Separate the effects of library growth, retrieval, and learned behavior with frozen populations and ablations. |

MathHub is the service environment around this knowledge-management lineage,
not evidence that MMT itself supplies Axeyum's intended producer/credit policy.
Likewise, these publications are not interchangeable implementations to score
on one theorem benchmark. The site research dossiers provide longer treatments;
the durable engine requirement is to evaluate the specific lesson above.

## What the current tree establishes

- [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)
  puts native proof construction, CAS reconstruction, and import behind a
  common mathematical admission boundary. Historical counts in that ADR are
  not fresh measurements.
- [ADR-0602](../research/09-decisions/adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md)
  separates prospective capability contracts from retrospective proof receipts.
  `scripts/validate-producer-contracts.py::shape_matches` currently ANDs formal
  language, fragment, and optional title prefix, statement substring, and ID
  prefix. This is useful candidate filtering; it is not elaborated-type
  unification or a proof that a requested conclusion follows.
- [ADR-0603](../research/09-decisions/adr-0603-classical-theorems-land-as-graded-statement-families.md)
  establishes distinct statement families. Its early boundary/refutation claims
  were corrected in subsequent audits. A checked reduction to a sign principle
  must not be reported as an internal proof of that principle's independence.
- The [current graph dispatcher scope](status/l2-g5-graph-dispatcher.md) is
  authoritative only for the measured `mathlib-group-defs-v1` population and
  language-infrastructure/proof-producers queues. Analysis remains a new,
  advisory population until its own measured authorization.
- Existing integration points include `scripts/lib/graph_dispatcher.py`,
  `scripts/fact-frontier.py`, `scripts/credit-transaction.py`,
  `scripts/check-credit-transaction.py`, and `artifacts/safety-matrix/`.
  Extend these authorities rather than introducing a second admission ledger.
- `crates/axeyum-lean-kernel/src/creal.rs` retains Bishop-style sequence
  representatives and defined equivalence. The IVT implementation, exact-root
  boundary, and strengthened forms live under `creal/`. Consult the
  [IVT/EVT audit](../formalized-math-2026-08/08-ivt-and-evt-measured-against-mathlib.md)
  together with exact declarations, not its historical headline claims.

This is a source inspection baseline. It does not re-run theorem production,
independent Lean replay, or existing performance measurements.

## Ordered work packages

### MOS-0 / L0: freeze a usable statement contract

Owner: theorem-credit lane. Prerequisite: existing safety contract and exact
statement binding. Start with the IVT family, one identity per distinct
statement. Do not place an informal claim such as “exact polynomial IVT” over a
certificate whose checked conclusion is only a sign computation.

Proposed files (not implemented by this roadmap):

- `artifacts/statement-families/ivt-v1.json`;
- `artifacts/ontology/statement-family.schema.json`;
- `scripts/check-statement-families.py`;
- fixtures under `scripts/tests/fixtures/statement-families/`.

Each row binds an existing fact ID, kernel declaration, elaborated type digest,
carrier/context digest, equality relation, quantified inputs, explicit data
inputs such as a modulus, conclusion, and the existing credit receipt. Human
labels such as `approximate` aid discovery but cannot authorize application.
Record the measured source-kernel footprint separately from translation/import
assumptions. Preserve both in the combined acceptance policy.

**Exit:** every selected row resolves to the intended declaration and receipt;
none depends on a title match. A changed binder, weakened endpoint hypothesis,
missing modulus, equality switched from `CReal.Equiv` to identity, or substituted
proof type must fail a targeted negative control. Deleting a row must fail
coverage derived from the frozen population. No changes to `proved` status are
made by this inventory step.

### MOS-1 / L1: represent checked applications and bridges

Owner: artifact/graph lane. Depends on MOS-0. Add a request representation that
binds the desired proposition and supplied hypotheses in an explicit context.
Store statement/dependency/type edges separately from proof/value edges.

Proposed request/application record:

```text
request: context_digest, goal_type_digest, supplied_term_bindings,
         accepted_trust_policy, resource_budget
candidate: fact_id, declaration_digest, producer_contract_digest
application: substitution, prerequisite_goal_digests,
             optional_bridge_declaration_digests
check: instantiated_result_type_digest, checker_identity, decision, reason
```

An elaborated goal and actual terms are authoritative; digests bind the payloads,
not replace them. Unification can propose a substitution. Only checking the
instantiated application and its obligations establishes that it meets the goal.
For rational-polynomial/algebraic-real/CReal crossings, require an explicit map
and checked preservation theorem for the property used. A shared word “real”
never creates a bridge.

**Exit:** positive applications preserve exact type and context; wrong-carrier,
missing-order-law, wrong-polynomial, and unproved-bridge controls decline.
Definitions are tested at discriminating inputs under the existing safety
programme. Proof-derived graph data remain unavailable to isolated producers.
Unknown, unsupported, and missing-hypothesis decisions remain distinct.

### MOS-2 / L2: select legal applications before ranking cost

Owner: infrastructure-frontier lane. Depends on MOS-1. Existing string/fragment
matching can generate candidates, but add the checked application stage before
any candidate can claim to satisfy the request. Preserve `fact-frontier.py`
legality, nursery isolation, capability retirement, and existing receipts.

Emit a decision trace under a proposed
`artifacts/applicability-pilots/ivt-v1/` directory: every considered candidate,
failed obligation, trust-policy decision, estimated cost, selected route, and
producer version. Contract selection does not constitute proof completion.
Choose among legal candidates by a published policy; never exchange stronger
assumptions for a shorter runtime silently. Execution produces a candidate,
which enters the existing credit transaction only after checking.

**Exit:** an approximate theorem cannot satisfy an exact request; a classical
import cannot pass a no-added-axioms policy; a CAS-internal result cannot pass a
kernel-reconstruction requirement. A timeout cannot settle a fact. A successful
producer returning the wrong goal is rejected. Concurrent duplicate credit and
stale-environment receipts fail through the existing transaction authority.

Keep this pilot advisory. Promotion to dispatcher authority requires a measured
ADR, as the current dispatcher scope requires.

### MOS-3 / L3: run the bounded IVT composition pilot

Owner: discovery/evaluation lane. Depends on MOS-0–2. Freeze the pilot before
execution. Existing IVT proofs are known examples for application/composition;
reusing them earns no new-theorem or autonomous-discovery credit.

Use four request families, with at least two valid and two adversarial instances
per family (16 instances minimum, generated from the manifest rather than a
hard-coded test count):

1. A residual bound suffices: instantiate `CReal.ivt_approx` at a requested
   accuracy, retaining interval membership and `abs(F x) ≤ 1/(n+1)`.
2. An exact root is required and stronger quantitative hypotheses are supplied:
   instantiate the checked exact theorem only after binding its actual inputs.
3. A rational polynomial exact-root request: use the CAS route only to the
   extent its present checked representation bridge establishes that exact
   conclusion. Missing bridge produces a typed decline, a valid pilot result.
4. A general classical existence request: select the named imported theorem
   only under an explicit compatible trust policy and proved hypothesis mapping.

For each accepted application, include a downstream consumer whose goal forces
use of the advertised guarantee. Negative consumers ask for root-distance error
from residual error alone, or for an exact witness from mere existence without
an extraction route. The acceptance check must reject those substitutions.

Baseline policies on identical inputs and resource limits:

- manual expert route assignment with recorded effort;
- current legal frontier plus current metadata filters;
- checked applicability without cost ranking;
- full proposed selection.

Ablate family labels, assumption policy, representation bridges, and dependency
reuse separately. The acceptance gate always stays on: unsafe ablations should
increase rejected proposals, never permit unsafe admission. Freeze model,
retriever, prompts, environment, seeds, CPU/memory budget, and cache conditions.
Do not train or tune on the held-out evaluation population. A second run with a
larger library is a distinct condition, not evidence of model learning.

Report valid downstream completions, incorrect proposals caught, wrong accepted
applications (required zero), typed declines by cause, hypothesis discharge
cost, selection and checking time, producer calls, tokens, and reused results.
Compare paired tasks rather than aggregate backend wins. Record unsuccessful
runs and exact denominators. No improvement claim follows from a single success.

**Exit:** all adversarial requests are rejected or routed to explicit unmet
obligations, all accepted applications replay, and the downstream-consumer
checks cover each accepted guarantee. Preregister which efficiency or completion
metric must improve over the strongest baseline before extending authority.
Zero gain retains the data and revises the policy; it does not justify expansion.

### MOS-4 / L3–L4: grow by demonstrated reuse

Only after the IVT pilot, add EVT and FTC with their actual statement families.
Do not force an obstruction row onto FTC by analogy with IVT. Add a second
mathematical context and a checked interpretation/bridge to test whether the
contract is reusable rather than an IVT dispatch table. Connect the elaborated
request/result to the existing L4 Lean adapter and require Lean to check the
returned proof where representable. Unsupported representation stays explicit.

The next research experiment asks whether one new lemma or method improves a
frozen downstream task population. Compare old library/new library under the
same selector and model, then change the selector separately. Learned policies
remain untrusted. This is the measurable recursive-improvement claim; growth of
an artifact directory alone is not improvement.

## Software verification follow-on: preserve the executable contract

After the bounded applicability pilot, extend the same contract discipline to a
Rust program already within `axeyum-verify`'s supported source subset. The
current frontend lowers syntax into solver terms; sharing Rust does not eliminate
semantic translation. Preserve source and contract digests, machine-integer
semantics, unwind bounds, lowering identity, and certificate coverage. A bounded
successful verdict is not automatically a general kernel theorem.

[Verus](https://verus-lang.github.io/verus/guide/modes.html) already lets developers
work with executable Rust, specifications, and proofs together. Its
[spec-to-exec machinery](https://verus-lang.github.io/verus/guide/exec_spec.html)
explicitly separates checked and unchecked translations. [SAW](https://galoisinc.github.io/saw-script/master/rust-verification-with-saw/introduction.html)
coordinates verification of existing code, and [Why3](https://why3.org/doc/manpages.html)
retains and replays proof sessions. [AutoVerus](https://arxiv.org/abs/2409.13082v3)
already explores LLM-generated Rust proofs. These are required comparisons for
this follow-on, not displaced by an all-Rust implementation claim.

Freeze a scalar executable contract; let an agent propose a repair or lemma;
check the unchanged obligation; then test a downstream caller. Mutations to
integer width, overflow behavior, source version, precondition, or bound must
invalidate stale evidence. Contract weakening is a separate reviewed change,
never an automatic way to make a repair pass. Measure duplicated models,
handwritten adapters, edit propagation, checked downstream completions, and
resource cost against matched supported examples. The desired benefit is that
the system owns reusable semantic bridges instead of each caller recreating them.

This does not authorize a general Rust verifier or a cybersecurity claim.
Security experiments must name the property and attacker model: bounds safety,
authorization, and secret-independent execution require different arguments.
Rust memory safety and kernel logical soundness are also separate properties.

## Integration and completion boundaries

No new engine feature, schema, capability, or dispatcher authority is landed by
this research document. Follow the repository ADR process before implementing
new public artifacts or extending measured authority. Keep L0–L4 order in
`PLAN.md`; the first execution task is MOS-0, not a broad autonomous agent.

The lane status file links this roadmap into the generated plan. The coordinator
must stage the new status file before running `python3 scripts/gen-plan.py`,
then run `python3 scripts/gen-plan.py --check` and the documentation link gate.
A generator pass that skips the untracked file does not validate integration.
No source counts or timing results in earlier journals are refreshed by this
planning change.

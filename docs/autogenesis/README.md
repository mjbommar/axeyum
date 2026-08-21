# Axeyum Autogenesis

## Purpose

This programme turns Axeyum from a collection of increasingly capable,
evidence-aware reasoning components into a system whose **verified reasoning
capability compounds automatically**.

The target is not merely a better solver, a larger theorem library, or an agent
that emits plausible proofs. It is:

> **A self-extending verified reasoning system: untrusted search may propose
> goals, decompositions, representations, tactics, algorithms, and even changes
> to its own search policy; only independently checkable evidence becomes
> durable knowledge.**

The trusted core stays small and stable while the untrusted intelligence around
it becomes broader, more adaptive, and more ambitious.

## Authority and scope

This directory is a durable long-horizon programme, not a second live task
tracker. Root [`PLAN.md`](../../PLAN.md) remains the sole authority for current
status and the next authorized increment. Each implementation phase in this
programme must enter the live queue through an owned file in
[`docs/plan/status/`](../plan/status/README.md), and consequential public or
trust-boundary decisions still require an ADR.

The existing [research roadmap](../research/08-planning/roadmap.md),
[foundational DAG](../research/08-planning/foundational-dag.md), and hard rules
remain in force. Autogenesis changes the criterion by which work is selected;
it does not waive foundation gates or authorize speculative implementation.

## Redefined goal

Axeyum succeeds when it can repeatedly perform this cycle:

```text
domain and checked knowledge
          |
          v
select or formulate a valuable claim
          |
          v
propose proof plans and representations       untrusted
          |
          v
search across solver / CAS / rewriting / library / induction
          |
          v
produce explicit evidence and a kernel term
          |
          v
independently replay, check, and admit         trusted boundary
          |
          v
record dependencies, assumptions, and provenance
          |
          v
measure what this result unlocked
          |
          +------> improve selection and search, then repeat
```

The unit of progress is a **verified capability gain**: a result that makes a
new useful class of problems reachable, cheaper, more assured, or more
automatic. A theorem counts when it unlocks descendants or teaches a reusable
method; a certified procedure may count more than a hundred isolated theorems.

The programme's primary objective is:

```text
verified capability gain
------------------------
human intervention * compute * trusted-base growth
```

No single scalar can carry the assurance claim. The operational dashboard must
also show the full conversion funnel from eligible goal to independently
replayed ledger transition.

## Programme outcome

The first decisive result is **Autogenesis-1**:

> From a fixed kernel, initial library, fact DAG, configuration, and resource
> budget, Axeyum autonomously selects and proves a reusable fact, admits it with
> checked evidence, observes that it unlocks another fact, then selects and
> proves that descendant. A clean-room replay reproduces the two-step acquisition
> sequence with no human-written or repaired proof and no unaccounted assumption.

This is deliberately stronger than “one automatic theorem.” It demonstrates
compounding, not automation theatre.

## Programme map

| Document | Question answered |
|---|---|
| [Current state and gaps](00-current-state-and-gaps.md) | What exists now, and what is genuinely absent? |
| [Target architecture](01-target-architecture.md) | What objects, boundaries, and feedback loops must exist? |
| [Phased roadmap](02-phased-roadmap.md) | What phases and concrete tasks get from here to the horizon? |
| [Workstreams and sequencing](03-workstreams-and-sequencing.md) | How do bottom-up and top-down work compose without starving each other? |
| [Metrics and evaluation](04-metrics-and-evaluation.md) | How is real capability gain distinguished from activity and self-report? |
| [Trust, safety, and governance](05-trust-safety-and-governance.md) | What remains immutable as autonomy increases? |
| [Research horizon](06-research-horizon.md) | What do current external systems teach, and what lies beyond them? |
| [First 90 days](07-first-90-days.md) | What is the first bounded execution programme? |
| [Backward foundation](08-backward-foundation.md) | What must be true immediately before Autogenesis-1, and which assumptions already fail? |
| [Authoritative B result](09-authoritative-b-admission-result.md) | Did a real B admission durably unlock A, and what remains uncredited? |
| [Autogenesis-1 result](10-autogenesis-1-result.md) | Did two clean authoritative B-then-A runs satisfy the fixed-budget, assurance, and reproducibility gates? |
| [Nursery foundation result](11-nursery-foundation-result.md) | Can the next evaluation population be split without dependency, family, proof-shape, mutation, or longitudinal leakage? |
| [Mathlib statement-source result](12-mathlib-statement-source-result.md) | How can Mathlib supply versioned statement families without vendoring bulk exports or leaking proof answers? |
| [Mathlib dependency-component result](13-mathlib-dependency-components-result.md) | Which statement candidates must remain together so direct proof dependencies cannot leak across evaluation splits? |
| [Mathlib outcome-blind review result](14-mathlib-outcome-blind-review-result.md) | Which candidates survive statement review, and how are mutation controls grouped before any outcome or split exists? |
| [Mathlib open-fact catalog result](15-mathlib-open-fact-catalog-result.md) | Can the reviewed statements become honest Axeyum ledger propositions without importing proofs or claiming construction? |
| [Mathlib frozen nursery split](16-mathlib-frozen-nursery-split-result.md) | Can all reviewed propositions be preregistered into useful evaluation partitions without dependency, source-group, family, proof-template, mutation, or longitudinal leakage? |
| [Nursery dispatch baseline](17-mathlib-nursery-dispatch-baseline.md) | What prevents the frozen train/development population from entering a current authoritative operation? |
| [First statement adapter](18-first-proof-isolated-statement-adapter.md) | Can an official Mathlib surface proposition become an independently checked goal without importing its proof or installing it as an assumption? |
| [First checked reflexivity candidate](19-first-checked-reflexivity-candidate.md) | Can a bounded generic producer construct a fresh proof from that goal and survive independent kernel and dependency checks without receiving ledger credit? |
| [Authoritative reflexivity registration](20-authoritative-reflexivity-operation.md) | Can that candidate route become one exact machine-selectable operation without yet changing the ledger? |
| [First nursery fact admission](21-first-mathlib-nursery-admission.md) | Did the registered operation durably establish its frozen train fact through the ordinary crash-safe ledger protocol? |
| [Reflexivity coverage census](22-mathlib-reflexivity-coverage.md) | Where do all train/development rows stop under the current proof-isolated adapter and bounded reflexivity grammar? |
| [Factorial-zero family registration](23-factorial-zero-family-registration.md) | Can one checked operation family cover a second frozen fact without broadening admission authority beyond exact source-bound rows? |
| [Factorial-zero family admission](24-factorial-zero-family-admission.md) | Did the second exact family member survive ordinary selection, crash recovery, settled replay, and clean-room reproduction? |
| [Type-slice feasibility](25-type-slice-feasibility.md) | Are trusted dependencies in the statement-facing type boundary or only in implementation closure? |
| [Fresh-kernel transport](26-root-selected-fresh-kernel-foundation.md) | Can one atomic root closure be exported and independently admitted without unrelated declarations? |
| [Checked typed generalization](27-checked-typed-generalization.md) | Can exact constant instances become a dependent proposition telescope that specializes back to the source? |
| [Type-slice receipt foundation](28-type-slice-receipt-foundation.md) | Which identities and checks must one durable proof-free slice receipt bind? |
| [Checked Mathlib type-slice replay](29-checked-type-slice-replay.md) | How many frozen train/development statements survive the complete semantic slice boundary, and why do the rest decline? |
| [Checked `autoParam` binder replay](30-auto-param-binder-replay.md) | Can the ten metadata-contaminated closures be normalized under a narrow kernel-checked contract? |
| [First complete producer census](31-first-type-slice-producer-census.md) | What does one preregistered proof grammar establish across all checked slices, and which gap should drive the next turn? |
| [Semantic abstraction debt census](32-semantic-abstraction-census.md) | Which exact definition identities and checked contract shapes separate type-safe generalization from fair proof search? |
| [First discharged function contract](33-discharged-function-contract-control.md) | Can a local behavior premise be proved generically, discharged by the exact source definition, and remain axiom-free under circularity controls? |
| [Source-bound function-contract receipt](34-semantic-function-contract-receipt.md) | Can both kernels, the exact source, local contract, witness, specialized proof, and dependency closures become one replayable fail-closed object? |
| [Real contract target census](35-real-contract-target-census.md) | Is any pointwise Mathlib binding ready for a direct equation contract, and what representation capability must come first? |
| [First exact contract-body residualization](36-int-gcd-contract-residualization.md) | Can the omitted `Nat.gcd` dependency become a checked local binder, and what trust evidence still blocks a real receipt? |
| [First bounded source-delta trace](37-int-gcd-source-delta.md) | Can the exact source body be exposed by one recorded definition unfold while residual functions remain opaque? |
| [First real trace-backed source-contract receipt](38-int-gcd-trace-contract-receipt.md) | Can exact residualization, specialization, delta evidence, and assumption freedom become one replayable real-source receipt without a witness theorem? |
| [Preregistered contract-to-theorem bridge](39-int-gcd-contract-theorem-control-selection.md) | Which bounded theorem control should consume the receipt before real evaluation, and which dependency chain lies beyond it? |
| [First contract-backed theorem receipt](40-int-gcd-contract-theorem-control-result.md) | Did the frozen bridge close the source-contract-to-theorem seam, and what remains before evaluation credit? |
| [Fibonacci/GCD premise sequence](41-nat-fib-gcd-premise-selection.md) | Which strategic premise and bottom-up foothold maximize compounding without skipping the first missing capability? |
| [First bounded Fibonacci recurrence result](42-nat-fib-iterate-recurrence-result.md) | Did the one-shot iterator-recurrence plan establish `Nat.fib_add_two`, and which exact capability boundary failed? |
| [Equality-elimination composition control](43-eqrec-composition-control.md) | Does the corrected motive-first `Eq.rec` universe contract close the measured constructor gap without another target execution? |
| [Corrected Fibonacci recurrence v2 selection](44-nat-fib-recurrence-v2-selection.md) | Which exact repair evidence and unchanged budget authorize one second `Nat.fib_add_two` execution? |
| [Corrected Fibonacci recurrence v2 result](45-nat-fib-recurrence-v2-result.md) | Did the corrected one-shot plan establish `Nat.fib_add_two`, and which target-specific stage must be localized next? |
| [Fibonacci recurrence stage control](46-nat-fib-recurrence-stage-control.md) | Which explicit equality bridge closes the v2 mismatch, and do all closed stages match without target submission? |
| [Fibonacci recurrence v3 selection](47-nat-fib-recurrence-v3-selection.md) | Which exact stage evidence and unchanged ceiling authorize one complete repaired target execution? |
| [Fibonacci recurrence v3 result](48-nat-fib-recurrence-v3-result.md) | Did the complete repaired operation construct the first real Fibonacci-path candidate, and what authority still remains? |
| [Fibonacci checked-theorem receipt selection](49-nat-fib-checked-theorem-receipt-selection.md) | How can the non-reflexive candidate receive an exact two-kernel receipt without rerunning search or granting ledger credit? |
| [Fibonacci checked-theorem receipt result](50-nat-fib-checked-theorem-receipt-result.md) | Did two fresh kernels reissue one exact receipt, and which admission boundary still keeps the fact open? |
| [Fibonacci recurrence admission](51-nat-fib-add-two-admission.md) | Did crash-safe admission make the checked recurrence durable and reproduce its real child-readiness delta? |
| [Fibonacci child qualification](52-nat-fib-child-qualification.md) | Which newly ready child aligns strategic leverage with the measured term boundary? |
| [Fibonacci coprimality premise plan](53-nat-fib-coprime-premise-plan.md) | Which bounded proof shape applies, and what exact composition seam blocks its execution? |
| [Alpha-stable prelude compatibility](54-alpha-stable-prelude-compatibility.md) | Which imported/native overlaps are exact, alpha-type compatible, or still unresolved before checked reuse? |
| [Kernel-type-shape prelude compatibility](55-kernel-type-shape-prelude-compatibility.md) | Which remaining overlaps differ only in kernel-irrelevant binder metadata, and which eight need explicit translation? |
| [Required Nat closure census](56-required-nat-theorem-closure-census.md) | Which representation mismatches actually block the seven-lemma target surface, and what is the first safe composition slice? |
| [First checked native-library composition](57-first-native-nat-composition.md) | Can native axiom-free proofs be transactionally admitted over compatible imported Mathlib declarations? |
| [Public checked theorem composition](58-public-checked-theorem-composition.md) | Does the first composition survive a reviewed reusable API, exact receipt, and fail-closed control matrix? |
| [Translated definitional reuse](59-translated-definitional-reuse.md) | Are the first structural mismatches real blockers, and which checked package becomes the next demand after target-kernel reduction? |
| [Atomic singleton-inductive composition](60-atomic-singleton-inductive-composition.md) | Can a demanded family, constructor, and generated recursor enter the imported target as one checked package, and what blocks the original root next? |
| [Checked definition composition](61-checked-definition-composition.md) | Can demanded computational helpers enter only through target-kernel admission, and which representation seam appears next? |
| [Official Bool order](62-official-bool-order.md) | Does aligning native Bool with Lean preserve every branch-sensitive consumer and advance the unchanged Mathlib composition control? |
| [General Nat.mod_lt compatibility](63-general-nat-mod-lt-compatibility.md) | Can the native theorem adopt Lean's general contract and cross wrapper differences through checked definitional equality? |
| [Canonical Acc composition](64-canonical-acc-composition.md) | Can one demanded recursive package be regenerated exactly without authorizing a generic transport class, and what target check appears next? |
| [Nat division composition mismatch](65-nat-division-composition-mismatch.md) | Which semantic representation mismatch blocks `Nat.div_mod_exec`, which direct consumer is the real next repair, and can official support remain axiom-free? |
| [Axiom-free Nat.mod equation pack](66-axiom-free-nat-mod-equation-pack.md) | Which official computation equations can compose with empty footprints and support a constructive target-side remainder proof? |
| [Constructive Nat.mod invariant specialization](67-constructive-nat-mod-invariant-specialization.md) | Can an authored fuel induction become an independently checked target `Nat.dvd_mod_iff`, and which closure boundary remains before `Nat.dvd_gcd`? |
| [Target-owned theorem leaves and the Nat.gcd frontier](68-target-owned-theorem-leaves-and-nat-gcd-frontier.md) | Can a compatible axiom-free target theorem cut only its source proof, and which foundation appears after both division branches are cut? |
| [Native Fibonacci composition](69-native-fibonacci-composition.md) | Can the exact imported Fibonacci definition and its established recurrence move into the axiom-free native gcd environment, avoiding the assumption-bearing official gcd route? |
| [Native Fibonacci coprimality](70-native-fibonacci-coprimality.md) | Does the bounded induction close with exactly the planned axiom-free dependencies, and why does the official r082 statement still require a semantic gcd bridge? |
| [Axiom-free official `Nat.gcd_succ`](71-axiom-free-official-nat-gcd-succ.md) | Can a pointwise fuel proof remove the quotient-bearing generic recursion equation and advance the official target through `Nat.dvd_gcd`? |
| [Official Fibonacci coprimality support surface](72-official-fibonacci-support-surface.md) | Do all seven preregistered native dependencies compose together over the checked official gcd leaves, leaving only the exact target theorem? |
| [Exact official Fibonacci coprimality](73-exact-official-fibonacci-coprimality.md) | Does the exact frozen r082 theorem pass ordinary kernel admission twice per run with an empty footprint, and what authority still precedes ledger credit? |
| [Fibonacci receipt authority](74-fibonacci-receipt-authority.md) | Which exact library-premise identities may the semantic receipt authorize, and how are they frozen before issuance? |
| [Exact Fibonacci semantic receipt](75-exact-fibonacci-semantic-receipt.md) | Did two fresh complete official reconstructions issue one identical dependency-bound receipt, and which transaction boundary still keeps the fact open? |
| [Exact Fibonacci coprimality admission](76-exact-fibonacci-coprimality-admission.md) | Did the dependency-bound receipt survive crash-safe ledger admission and clean replay, and which descendant became ready? |
| [`Nat.gcd_fib_add_self` qualification](77-nat-gcd-fib-add-self-qualification.md) | What exact relation and reusable support obligations lie between the newly ready child and its first honest bounded target submission? |
| [`Nat.gcd_fib_add_self` support-first plan](78-nat-gcd-fib-add-self-support-plan.md) | Which fixed reusable support sequence and bounded authority may attempt the newly ready Fibonacci gcd-shift theorem? |
| [Native Fibonacci successor addition](79-nat-fib-successor-addition.md) | Did the first preregistered support reconstruct twice, remain axiom-free, compose into r091, and preserve the zero-target-credit boundary? |
| [Coprime-factor cancellation and the Euclidean seam](80-coprime-factor-cancellation-and-euclidean-seam.md) | Did the second support reconstruct independently, and what exact official/native boundary prevents target composition? |
| [Constructive official Euclidean bridge plan](81-constructive-euclidean-bridge-plan.md) | Which bounded bottom-up route repairs the official division/Bézout foundation without importing an assumption-bearing proof or spending target credit? |
| [Official division equation root audit](82-official-division-equation-root-audit.md) | Are the three generated quotient/remainder computation roots independently checkable with empty footprints before authored bridge work begins? |
| [Proof-isolated Euclidean construction capsule](83-proof-isolated-euclidean-construction-capsule.md) | Can a fresh construction context receive every allowed statement and audited identity without being exposed to upstream proof material? |
| [Current-stable Mathlib statement comparison plan](84-current-stable-mathlib-statement-comparison-plan.md) | Which exact stable release and bounded proof-free process should measure whether the selected v4.30 statement surface survives upstream evolution? |

The first executable counterfactual primitive is
[`create-autogenesis-snapshot.py`](../../scripts/create-autogenesis-snapshot.py).
It derives a content-addressed B -> A overlay without editing committed facts;
[`theorem_knowledge_audit`](../../crates/axeyum-lean-kernel/examples/theorem_knowledge_audit.rs)
then rejects required/forbidden dependency violations over the full transitive
kernel closure.
[`create-autogenesis-proposer-catalog.py`](../../scripts/create-autogenesis-proposer-catalog.py)
projects that snapshot to names and canonical types only, and the Python
proposer runner supplies the verified catalog through an OS sandbox with no
checkout, retained proof bodies, inherited environment, or network.
[`check-autogenesis-apply-search.sh`](../../scripts/check-autogenesis-apply-search.sh)
then composes two catalog-only searches: a target-independent structural-plan
grammar produces fresh B, and the identical A target receives no proof before B
but a fresh, B-dependent proof afterward under the same budget. The chain is
now bound to an internal typed B evidence handoff and a replay-derived,
zero-ledger-write episode transition. A checked accepted-transition event is
now required to construct the post-B catalog, so the snapshot alone cannot
unlock A. The exact-commit retained bundle at `42dad8ffa` also reproduces
through the separate read-only replay command.
The next boundary now has a typed, read-only fact-transaction proposal: its
positive test is explicitly counterfactual, while mismatched evidence for a
real open fact rejects. No authoritative ledger write is claimed; its durable
admission event is fixture-scoped.
ADR-0468's applicant now commits that proposal only in a temporary fact root,
with compare-and-swap and roll-forward recovery tested at all three durable
boundaries. Production write authority rejects this fixture path.
The durable fixture event now derives a content-addressed readiness delta, and
that delta is mandatory input to the post-B catalog. It authorizes exactly A
from the ledger's B-to-A edge. The authoritative fact frontier now has a
content-addressed JSON form with deterministic rationale. At exact pushed
checkpoint `5c38bf95d`, it selects exactly
`F:no-integer-square-is-minus-one`: the only open fact matching an
authoritative typed operation. Every unregistered candidate remains refused,
so broad fragment reachability cannot silently become dispatch authority.

The reviewed [`operations.json`](../../artifacts/autogenesis/operations.json)
names both the fixture-only Nat producer/checker and the first authoritative
QF_NIA certificate operation. The latter is source-bound, narrow, and carries
a non-empty SMT trust footprint rather than impersonating a kernel theorem.
Selection, typed execution, admission, and recovery are therefore real. The
executor binds a clean commit, frontier, registry, fact, source bytes, budget,
and independently rechecked result; the transaction adapter derives the
complete fact delta and replay checker without caller-authored metadata. The
first production compare-and-swap intentionally stopped after durable intent,
left the fact unchanged, then recovered to a durable event. Its event-triggered
frontier delta honestly records `newly_ready: []`.

At exact pushed commit `f8651ec98`, a second isolated clean worktree reconstructed
the historical open row and freshly repeated selection, certified execution,
transaction preparation, the same intent fault, recovery, settled-fact replay,
and readiness derivation. The complete external bundle at
`/nas3/data/axeyum/autogenesis/replays/f8651ec98/` has replay digest
`7dc1ad8dc336ac0ea295a3a0b912f89f415787c0b78c61c54624a791f1800e4b`.
This closes clean authoritative **leaf** reproduction. The selected fact unlocks
no descendant, so it still receives no Autogenesis-1 compounding credit.

Chain authority is now narrower and stronger. The kernel subgraph contains 52
authored `depends_on` edges, but only 23 are confirmed as direct dependencies by
the checked proof terms; the content-addressed catalog refuses to equate those
sets. The existing `F:nat-zero-add -> F:nat-mul-one` two-search experiment
replayed at exact commit `a90255a92` and qualifies the primary chain: same A
target, pre-B budget exhausted with no proof, B produced axiom-free, durable
fixture event, then A proved using the episode-local B. Qualified catalog
`95e8c8d401441b98793259d79f95cda485493b81c996c08f0d1df998285c925b`
selects it for engineering while explicitly granting no authoritative-write
authority. The next bridge is therefore operation authority for B and A, not
more chain prose.

B's first production-capable route is deliberately exact rather than
generic: `authoritative-kernel-nat-zero-add-induction-v1` reconstructs the
selected statement in a fresh kernel, accepts plan 2 of 2, and requires both an
empty axiom footprint and no retained-answer dependencies. The retained
[authoritative B admission](09-authoritative-b-admission-result.md) then
crash-recovered one real write and derived A as newly ready. The live ledger was
untouched. A's exact episode-local apply operation is now implemented: it
verifies B's execution-to-readiness trigger chain, reconstructs
an episode-local B candidate, and applies only that candidate. It also creates a
deterministic detached post-B state commit without touching the branch or index.

**Autogenesis-1 passed at exact source commit `cf998788b`.** Two isolated runs
used the same fixed budgets (`B=2`, pre-B `A=1`, post-B `A=1`). Before B, A
exhausted that budget without a proof. The authoritative frontier then selected,
proved, crash-recovered, and recorded B; B's durable event made exactly A newly
ready; and the frontier selected, proved through the episode-local B,
crash-recovered, and recorded A. Both kernel footprints and retained-answer
dependency lists were empty. The two runs had identical semantic identities and
all 56 retained artifact bytes matched. The small committed
[result index](../../artifacts/autogenesis/autogenesis-1-result.json) binds the
external receipts; the detailed audit is in the
[Autogenesis-1 result](10-autogenesis-1-result.md).

The first post-result increment was a deliberately red nursery baseline. ADR-0478
reserves the successful chain as a longitudinal regression, separates authored
split dependencies from proof-derived admission authority, and prohibits
dependency components, theorem families, proof shapes, or mutations from
crossing evaluation partitions. The executable
[`nursery-v1.json`](../../artifacts/autogenesis/nursery-v1.json) now freezes 214
proof-free Mathlib propositions: 78 train, 60 development, and 76 held-out. The
checker reports ready with zero blockers and zero leakage. The earlier red
finding remains important: the original ledger could not be relabelled into a
credible held-out population. See the [nursery foundation
result](11-nursery-foundation-result.md) and [frozen split
result](16-mathlib-frozen-nursery-split-result.md).

The first [type-slice feasibility result](25-type-slice-feasibility.md) then
measured the 138 unsealed statement streams bottom-up. All 114 strict-adapter
rejections have a syntactically clean proposition-facing type closure: their
trusted declarations appear only through implementation bodies. The boundary
shrinks 67,099 implementation-closure declaration occurrences to 1,806 type
occurrences, but remains diagnostic. The next semantic gate must construct the
generalized proposition in a fresh kernel, reject proposition-valued
abstractions, bind universe-instantiated type identities, and check an exact
specialization back to the source proposition before any fact receives credit.

The first implementation increment now supplies that future route's
[fresh-kernel transport](26-root-selected-fresh-kernel-foundation.md). The
canonical kernel writer emits an atomic root dependency closure, and the
ordinary importer re-admits it into a fresh environment with unrelated
declarations absent. This is intentionally not yet a type slicer: selected
definition bodies still retain their full dependencies until ADR-0484's typed
parameter abstraction is implemented.

The next two increments add [checked dependent generalization](27-checked-typed-generalization.md)
and a [content-addressed slice receipt](28-type-slice-receipt-foundation.md).
The resulting [checked Mathlib replay](29-checked-type-slice-replay.md) first
admitted proof-free producer boundaries for 128 of the 138 unsealed statements.
A type-only normalization control left the same ten declines, locating the
remaining contamination in recursor-rule binder annotations. The separately
versioned [checked `autoParam` binder replay](30-auto-param-binder-replay.md)
now admits all 138 after the source kernel validates the exact elaborator
metadata definition and checks every normalized declaration and rule by
definitional equality. This closes the goal boundary, not the proofs: the next
increment measures bounded producer yield and structured declines over
train/development while held-out remains sealed.

That [first complete producer census](31-first-type-slice-producer-census.md)
now admits two of 138 goals under the fixed reflexivity grammar. More
importantly, it separates 24 exact slices from 114 slices whose 152 definition
abstractions preserve types but intentionally omit behavior. The next flywheel
turn therefore has two controlled lanes: develop proof plans against the 22
unsolved exact goals, and add kernel-discharged semantic contracts before
treating the 114 abstracted goals as a fair proof-search curriculum.

The [semantic abstraction census](32-semantic-abstraction-census.md) now
resolves those 152 bindings into 32 exact definition identities and three
checked-type contract shapes. Printed names are insufficient keys, and the
large transitive theorem closure is mostly indirect. ADR-0488 therefore makes
contracts exact-identity-bound local obligations with independently checked
source-specialization witnesses. The next bottom-up increment prototypes one
pointwise function contract; proof planning on the exact 24 remains an
independent top-down lane.

That [first function-contract control](33-discharged-function-contract-control.md)
now passes end to end on a synthetic transparent identity function. The generic
proof and exact source witness are separately axiom-free; same-typed definition
substitution fails, and circular answer use remains visible in the footprint.
The next boundary is a durable exact-identity receipt before any real Mathlib
slice or ledger row can consume the mechanism.

The [source-bound contract receipt](34-semantic-function-contract-receipt.md)
now makes that boundary durable. It reissues from both kernels, requires the
literal generic-proof/source/witness application, binds complete dependency
closures, and rejects identity, binder, proof, and circularity mutations. The
next turn selects and preregisters one real train/development target by joining
bottom-up definition cost with top-down proof demand.

The [real-target census](35-real-contract-target-census.md) declines that
selection: 0/50 pointwise bindings can state their direct transparent equation
in the current proof-free slice because every body names an omitted constant.
ADR-0489 therefore inserts checked contract-body residualization before target
selection. The axiom-free `Int.gcd`/omitted-`Nat.gcd` row is the first mechanism
control, not an authorized theorem attempt.

That [first exact residualization](36-int-gcd-contract-residualization.md) now
passes: the `Int.gcd` equation becomes a two-function local contract and
specializes exactly. Its source witness is axiom-free but reaches 52 theorems
transitively despite reporting zero direct theorem dependencies. ADR-0490
strengthens receipt independence to the complete closure. The next turn must
produce a bounded one-step source-delta trace rather than whitelist that closure.

That [bounded source trace](37-int-gcd-source-delta.md) now passes against the
same exact `Int.gcd` declaration. It consults `Int.gcd` only, leaves `Nat.gcd`
opaque, and binds a proof-free template containing neither function constant.
ADR-0491 accepts the structural trace mechanism without weakening ADR-0490.
The next turn must replace the receipt's theorem-valued source witness with
this independently replayed trace; the current result grants no contract or
ledger credit.

The [trace-backed receipt](38-int-gcd-trace-contract-receipt.md) now closes that
source-side boundary for the exact pinned `Int.gcd`: one receipt issues and
replays with residual `Nat.gcd`, retained `Int`/`Int.natAbs`, one selected delta,
zero source axioms, and no witness theorem. ADR-0492 keeps this source-contract
receipt distinct from downstream theorem evidence. The next turn returns
top-down: select one frozen proposition that actually needs the contract before
running a producer.

The [preregistered bridge](39-int-gcd-contract-theorem-control-selection.md)
has now run exactly once. Its [result](40-int-gcd-contract-theorem-control-result.md)
is one replayable, axiom-free semantic theorem receipt for `Int.gcd_def`, built
with the frozen two-binder, five-node grammar. This closes the mechanism seam
but carries zero evaluation or ledger credit. `Int.gcd_fib` remains the real
horizon target; its explicit upstream facts `Int.fib_neg` and `Nat.fib_gcd` are
both still open.

The [next sequence](41-nat-fib-gcd-premise-selection.md) selects
`Nat.fib_gcd` over `Int.fib_neg`: it has the smaller checked boundary and
unlocks both `Int.gcd_fib` and `Nat.fib_dvd`. Execution starts lower in the
chain at zero-dependency `Nat.fib_add_two`, under a frozen two-plan iterator
recurrence budget. No proof attempt has run under that policy.

## Phase summary

| Phase | Future state | Decisive exit |
|---|---|---|
| 0. Bind reality | Current claims and interfaces are machine-readable and non-contradictory | One generated baseline names every existing seam and refuses stale plan/fact state |
| 1. Close one loop | A deterministic orchestrator performs one evidence-backed fact transition | Clean replay of one autonomous closure; no learning or conjecturing |
| 2. Demonstrate compounding | A counterfactual knowledge snapshot and scheduler produce a two-fact unlock chain; a dense nursery follows for sustained evaluation | Autogenesis-1 passes from a clean checkout |
| 3. Plan proofs | A typed proof-plan IR composes heterogeneous checked substeps | One goal solved by a multi-route plan that no monolithic route can solve |
| 4. Acquire capabilities | Structured declines drive reusable lemma, route, and representation work | Measured capability acquisition raises held-out autonomous yield |
| 5. Learn search, not truth | Search policy improves from replayable reasoning episodes | Learned policy beats deterministic baselines without changing acceptance |
| 6. Discover | The system proposes and filters useful new conjectures and algorithms | Novel candidates survive independent proof/refutation and novelty review |
| 7. Become domain-general | Domain adapters produce typed, epistemically classified knowledge | Two non-mathematical domains complete the same checked loop |
| 8. Govern recursive improvement | The system proposes bounded improvements to its own untrusted machinery | Improvements pass immutable evaluation, regression, and trust-budget gates |

Phases are capability gates, not dates. Work may begin on a later phase's
research or fixtures early, but no later phase may receive product credit before
its prerequisites pass.

## Strategic rules

1. **Composition before breadth.** Prefer closing an existing seam over adding
   another isolated capability.
2. **Demand pulls mechanisms.** Solver and reconstruction work should normally
   be selected by structured declines from valuable, dependency-ready goals.
3. **Learning proposes; formal machinery disposes.** Learned systems never
   decide truth, evidence validity, axiom freedom, or publication.
4. **Failures are products.** A typed decline with a minimal blocker and replay
   is valuable training and planning data; a timeout string is not.
5. **The ledger records knowledge, episodes record attempts.** Do not overload
   the fact schema with search traces or treat every attempted conjecture as a
   fact.
6. **Novelty is a separate judgment.** Kernel acceptance establishes formal
   consequence, not importance, originality, correct formalization, or truth of
   empirical premises.
7. **Scale follows demonstrated pull.** Sharding, caching, distributed search,
   and learned policies are justified by observed bottlenecks in the closed
   loop, not projected theorem counts.
8. **Over-the-horizon pressure is explicit.** Every phase must preserve typed
   binders, extensible evidence, deterministic replay, domain separation, and a
   path to richer proof calculi.

## Relationship to existing programmes

Autogenesis does not replace the A1-A11 solver programme or the existing proof,
Lean, CAS, verified-systems, and frontend tracks. It supplies their selection
function:

```text
autonomous attempt
      |
      v
structured blocker --+--> solver/theory task
                     +--> reconstruction/checker task
                     +--> library lemma task
                     +--> representation task
                     +--> resource/observability task
                     +--> domain/formalization task
      |
      v
repair the smallest reusable blocker
      |
      v
retry the original attempt and measure unlocked descendants
```

The complete-solver and Lean horizons remain valuable. They become capability
reservoirs serving a measurable knowledge-growth loop rather than independent
feature-count races.

## Definition of done

The programme is not complete because a model generates a proof, because a
solver returns `unsat`, because Lean reads a generated module, or because a
dashboard reports growth. It is complete only when Axeyum can sustain bounded,
reproducible capability acquisition across domains while:

- every durable formal result is independently checkable;
- every assumption and trust step is explicit;
- every policy improvement is evaluated against immutable held-out populations;
- regressions and failed experiments remain visible;
- the trusted base grows only through deliberate, reviewed decisions; and
- human intervention per verified capability gain declines over time.

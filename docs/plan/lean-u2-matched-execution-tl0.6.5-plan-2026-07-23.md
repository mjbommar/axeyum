# Lean U2 TL0.6.5 plan — matched official/Axeyum execution and comparison

Status: **preregistered contract and evidence-schema correction only; no
TL0.6.5 input authority, execution authorization, official or Axeyum process,
outcome, comparison row, performance row, U2 promotion, axis completion,
terminal gate, or parity credit exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Required parents:

- a future complete and accepted
  [TL0.6.3 official-execution authority](lean-system-implementation-plan-2026-07-21.md#lean-system-task-table)
  covering every selected official case/provider cell; and
- a future accepted TL0.6.4 M3 result under the
  [complete-row review plan](lean-u2-native-surface-classification-tl0.6.4-m3-review-plan-2026-07-23.md),
  covering all 3,723 case rows and all 408,374 applicable case/variant cells.

## 1. Decision boundary

TL0.6.5 is the first phase that may execute the native Axeyum route against
the same registered U2 obligations already executed by official Lean. It owns
the immutable Axeyum run records, semantic comparison records, exact overlap
projection, and bounded U2 paired-execution authority. It does not implement a
missing Lean surface, repair TL0.6.3 official evidence, revise TL0.6.4
classification, or promote U2 to terminal status.

The singular rule is:

> A comparison is a third evidence object over two separately identified
> executions. It may not replace either execution identity with one shared
> command, environment, resource, attempt, completion, diagnostic, or artifact
> field, and it may not infer a missing comparison row from the rows that did
> run.

This is a correction of the existing parity registry, not a new solver or
evidence policy. Accepted
[ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)
already requires every result to own its exact run, attempt, environment,
resource, and output identities. Proposed
[ADR-0343](../research/09-decisions/adr-0343-preregister-cross-regime-measurement-provenance.md)
already separates raw occurrence, normalized path, exact content, population,
selection, scoring, and oracle identities. The current flat paired-cell shape
violates those constraints by sharing execution-local fields across official
Lean and Axeyum. Because the registry has zero paired cells, correcting that
shape now migrates no credited observation.

## 2. Current-state audit and hard block

The current U2 authorities establish useful but non-executable prerequisites:

| Boundary | Current fact | TL0.6.5 consequence |
|---|---|---|
| U2 case authority | 3,723 full-Lake cases | exact case denominator exists |
| official variants | 111 provider variants in eight selection sets | variant identities exist, but complete accepted official outcomes do not |
| classification expansion | 408,374 applicable `(case_id, variant_id)` cells | candidate execution-slot denominator exists |
| TL0.6.4 M2 | all 111 providers unbound; no accepted M2.1-M2.7 closure | native dispatch and dependency closure are unavailable |
| TL0.6.4 M3 | no accepted parent, assignments, dispositions, or acceptance | no classified TL0.6.5 input authority exists |
| official execution | 66 accepted outcomes over 65 unique cases; one of 289 release-Linux child shards complete | TL0.6.3 is incomplete |
| native execution | zero Axeyum outcomes | no native observation exists |
| comparison | zero paired cells | no functional, assurance, or performance credit exists |

Therefore this plan authorizes no process. In particular, it does not authorize
Lean, Lake, compiler, server, official-test, network, tracing, or Axeyum
execution. A future attempt needs a separate post-parent authority that binds
the exact input revision, executable, commands, environment, resources,
attempt IDs, output root, and stop conditions before launch.

## 3. Denominators and comparison obligations

Three denominators remain distinct:

1. **case rows:** 3,723 stable U2 case identities;
2. **execution slots:** 408,374 applicable `(case_id, variant_id)` cells from
   the accepted TL0.6.4 authority; and
3. **comparison obligations:** the complete expansion of each execution slot
   into every applicable `(axis, layer, normalization)` observation.

The third count is not assumed to equal 408,374. A compile test can create
separate elaboration, kernel-assurance, generated-artifact, interpreter,
native-runtime, and output obligations; a server test can create lifecycle,
diagnostic, request/response, cancellation, and stale-publication obligations.
Conversely, an accepted TL0.6.4 decline can establish that a particular layer
is inapplicable, but only through an explicit reviewed obligation or exclusion
row. TL0.6.5 M0 must derive and content-bind the complete comparison-obligation
list before any native execution.

Content equality never removes membership. Equal source bytes, commands, or
normalized outputs may deduplicate storage, but every case, variant, axis, and
layer retains its own authority membership and terminal classification.

## 4. Paired authority: no vacuous agreement

The terminal registry must carry one paired-population authority row for each
`U0` through `U9`. Each row has an explicit state:

- `not_registered` — no authoritative comparison population exists;
- `bounded_profile` — an exact scoped comparison population exists but cannot
  satisfy terminal G3; or
- `complete_authority` — the complete terminal obligation list and ordered-ID
  digest are registered with retained evidence.

A row records the expected comparison-cell count and the domain-separated
digest of its sorted IDs. `complete_authority` is valid only when the registered
cells for that population match both values exactly. G3 derives satisfied only
when all ten paired-population authorities are complete and every expected cell
is classified `agree-success` or `agree-reject`.

This closes two vacuity paths in the current generator:

- one successful pair cannot stand in for an unknown terminal denominator;
- omitted `not-run` or `invalid-run` obligations cannot disappear from the
  disagreement counts.

TL0.6.5 may finish with U2's paired-population authority complete even when it
contains disagreements. TL0.6.6 separately reviews those results and promotes
U2 only if its complete matrix has no unexplained mismatch or missing evidence.
Other U0-U9 rows remain independent and keep G3 open.

## 5. Terminal paired-cell schema v2

Each cell has common subject identity plus two structurally separate execution
records and one comparison record.

### 5.1 Common identity

| Field | Meaning |
|---|---|
| `id` | stable unique comparison-obligation ID |
| `population` | `U0` through `U9` |
| `population_member_id` | exact raw member identity; U2 uses `case_id` |
| `profile_id` | exact configuration/provider identity; U2 uses `variant_id` |
| `axis` | `A0` through `A11` |
| `layer` | compared semantic or workflow layer |
| `source_sha256` | exact input-content digest |
| `dependency_sha256` | accepted transitive dependency-closure digest |
| `source_family` | non-authoritative family label retained for stratification |
| `official` | official-Lean execution record in section 5.2 |
| `axeyum` | native Axeyum execution record in section 5.2 |
| `comparison` | normalization, classification, and evidence in section 5.3 |

`population_member_id` is deliberately separate from `source_sha256`: two
official test occurrences with equal bytes remain two members. `profile_id` is
separate from executable/configuration hashes because one provider may serve
multiple named variants and one variant can change implementation only through
an explicit new authority.

### 5.2 Per-system execution record

The `official` and `axeyum` objects have identical exact fields but independent
values:

| Field | Meaning |
|---|---|
| `record_state` | `complete`, `not-run`, or `invalid` |
| `executable_sha256` | exact executable/provider identity |
| `configuration_sha256` | effective system configuration identity |
| `command_sha256` | exact argv/cwd/input/redirection contract identity |
| `environment_sha256` | allowlisted effective environment identity |
| `platform_id` | declared hardware/OS/toolchain platform identity |
| `resource_envelope_sha256` | requested and enforced limits identity |
| `attempt_id` | immutable owning attempt identity |
| `completion_sha256` | completion-last record identity |
| `outcome_sha256` | typed observed/admitted outcome identity |
| `assurance_sha256` | independent-checking/trust vector identity |
| `diagnostics_sha256` | raw and normalized diagnostic-set identity |
| `duration_ms` | non-negative wall duration, not a parity verdict |
| `peak_rss_kib` | non-negative peak RSS, not a parity verdict |
| `artifact_bytes` | non-negative retained artifact bytes |
| `evidence` | nonempty repository-relative evidence links |

For `complete`, every scalar identity and metric is present and validates.
For `not-run` and `invalid`, unavailable execution-derived values are JSON
`null`, not magic all-zero digests or invented attempts. Any values that are
present must still validate, and retained evidence must explain absence or
invalidity. `invalid` never becomes `complete` by later patching; a new valid
attempt creates a new immutable execution record while history stays visible.

### 5.3 Comparison record

| Field | Meaning |
|---|---|
| `outcome` | one class from the existing eight-class taxonomy |
| `normalization_id` | stable named normalization and version |
| `normalization_sha256` | exact normalization implementation/rule-set identity |
| `contract_sha256` | exact selected-observable, ignored-field, equivalence, and taxonomy contract |
| `result_sha256` | canonical comparison-result identity |
| `completed` | comparison record was installed last over the two cited side records |
| `evidence` | nonempty raw/normalized diff and independent-check links |

The comparison record does not own command, environment, attempt, or resource
fields. It binds the two side records and records how their declared
observables were compared. `completed = true` means the comparison projection
is complete for the evidence available; it does not imply both systems ran or
that they agree.

Outcome/state coherence is exact:

| Comparison outcome | Required side states |
|---|---|
| `agree-success`, `agree-reject`, `official-only`, `axeyum-only`, `semantic-mismatch`, `unadjudicated` | both `complete` |
| `not-run` | at least one side `not-run`, neither side `invalid` |
| `invalid-run` | at least one side `invalid` |

An Axeyum timeout, resource exhaustion, or supported decline is a completed
typed Axeyum execution and can therefore produce `official-only`. Total absence
of launch/completion is `not-run`. Inconsistent pins, artifacts, or attempt
evidence are `invalid-run`, even when a process returned exit zero.

## 6. Matching and selection rules

The official and Axeyum commands need not be byte-identical; they implement
different systems. They must be selected before execution from the same common
subject, profile, dependency closure, declared observables, platform class,
and resource policy. Each side retains its own concrete argv, environment, and
enforced envelope.

The official side is joined only to the exact accepted TL0.6.3 record named by
the comparison authority. It is never selected as “latest,” “fastest,” “first
pass,” or “best of retries.” A fresh official rerun cannot silently replace a
consumed record. Axeyum receives one preregistered attempt per execution
authority; diagnostic retries retain new attempt IDs and do not overwrite the
selected result.

Functional and performance matching are distinct:

- functional comparison permits declared non-semantic platform details to
  differ only when the comparison contract explicitly normalizes them;
- performance comparison requires the same registered hardware class,
  effective resource limits, concurrency regime, warm/cold state, and
  measurement method; otherwise performance is `unadjudicated` even if
  functional behavior agrees; and
- timing, RSS, and artifact size never change a functional outcome class.

## 7. Observable and normalization contract

Every obligation names exactly what is observed, what is ignored, and why the
ignored fields are non-semantic for that layer. Normalization is allowlist
based: an unregistered field is compared, not silently dropped.

| Layer | Required normalized observables |
|---|---|
| process/harness | typed termination, expected exit policy, stdout/stderr, declared files/effects, cleanup, and completion |
| parser/macro | syntax kind/payload, source spans, scopes/hygiene, recovery nodes, and macro expansion |
| elaboration | declaration/core term, inferred types, environment extensions, messages/ranges/severity, and info trees where declared |
| kernel/assurance | admission/rejection, type, definitional equality, normal form, declaration/dependency identity, axiom/trust closure, and independent replay |
| module/cache | raw/effective import closure, public/private/meta visibility, environment parts, initialization, artifact identity, and invalidation |
| tactic | initial/final goals, metavariable state, emitted theorem term, diagnostics, and independent kernel admission |
| compiler/runtime | frontend result, interpreter/native route, exit, values, exceptions, stdout/stderr, files/effects, FFI/ABI/load/init evidence |
| server/RPC | ordered lifecycle and request/response transcript at exact document versions, cancellation, diagnostics, snapshots, worker/watchdog state, restart, widgets, and stale-result suppression |
| Lake/project | workspace graph, revisions, manifests, targets/facets/jobs, materialization, cache state, network policy, command exits, artifacts, incremental/offline behavior |

The official Lean reference documents why these layers cannot be collapsed:
source elaboration produces environments and info trees; kernel checking is a
separate boundary; compiler input can differ from kernel terms; `.olean`,
`.ilean`, initialization, interpreter, and native compilation carry different
state. Lean's pinned test README likewise distinguishes test directories from
test piles and separately names elaboration-success, expected-failure,
compile/execute/interpreter, server, Lake, package, and benchmark families.

Every normalization receives controls that mutate one semantic observable at
a time and must change the comparison result. Each ignored-field rule receives
a paired non-semantic mutation that must not change the result. Required
classes include source bytes, dependency closure, declaration/core term,
diagnostic class/range, environment visibility, output bytes, artifact/effect
sets, request ordering/document version, cancellation/staleness, platform,
resource, attempt, completion, and assurance/trust evidence.

## 8. Incremental publication and review

TL0.6.5 may publish deterministic bounded prefixes after each valid Axeyum
attempt. A prefix must include:

- one immutable attempt authority and completion-valid side records;
- the exact comparison obligations covered and their ordered-ID digest;
- every outcome class, including `not-run` and `invalid-run` rows in scope;
- exact overlap and direction counts rather than equal total counts;
- functional, assurance, and performance projections kept separate; and
- an explicit residual against the full U2 comparison authority.

A bounded prefix remains `bounded_profile`. It cannot increase U2's terminal
denominator, A0/A3-A8 completion, G3, or the public parity claim. Resume skips
only validating immutable side and comparison records. Conflicting duplicates,
changed parents, changed normalization, missing outputs, mixed revisions, or
post-completion mutation invalidate the attempt instead of being repaired in
place.

Independent review is required before accepting the final TL0.6.5 authority.
The reviewer verifies exact obligation coverage, both side identities,
normalization controls, outcome coherence, comparison recomputation, evidence
reachability, aggregate projections, and non-credit fields. Any unexplained
semantic mismatch, unadjudicated row, absent obligation, or invalid evidence
is retained for TL0.6.6 and blocks U2 promotion.

## 9. Milestones

| Milestone | Work | Exit | Non-credit boundary |
|---|---|---|---|
| M0 — obligation authority | after both parents, expand every accepted execution slot into exact comparison obligations | count, ordered IDs/digest, layer/normalization ownership, exclusions, and zero executions validate | no process or outcome |
| M1 — comparison implementation | implement side/comparison records, normalizers, joiner, store, projector, and independent validator | all schema, mutation, determinism, and copied-root controls pass | synthetic controls only |
| M2 — attempt authority | bind exact native executable, commands, environment, platform/resources, shard mapping, output root, and stop rules | explicit authorization digest validates | no launch before authorization |
| M3 — bounded native execution | execute one preregistered bounded shard and install completion last | every selected side record and absence/invalid row validates | bounded profile only |
| M4 — incremental campaign | resume over disjoint exact obligations with immutable attempts | every U2 execution slot has a selected native record or explicit terminal absence | no U2 promotion |
| M5 — comparison closure | normalize and compare every expected obligation | paired authority count/digest exact; every row classified and reproducible | disagreements remain blockers |
| M6 — independent acceptance | review full authority, aggregate projections, controls, and residual | TL0.6.5 result accepted or rejected with complete action ledger | TL0.6.6 owns U2 promotion |

This plan is M0-prior documentation only in the roadmap sense; its own status
does not mean the future post-parent M0 obligation authority exists.

## 10. Acceptance gates for this preregistration checkpoint

Before this plan can be registered as the TL0.6.5 contract:

1. the generated terminal schema uses separate `official`, `axeyum`, and
   `comparison` objects with exact field sets;
2. complete side records require every digest, ID, metric, and retained
   evidence field;
3. absent/invalid sides use typed states and JSON `null`, never a fabricated
   zero digest or borrowed attempt;
4. outcome/state coherence rejects agreement without two complete sides,
   `not-run` without an absent side, and `invalid-run` without an invalid side;
5. paired-population authorities bind expected count and sorted-ID digest;
6. G3 rejects a nonempty proper subset even if every registered row agrees;
7. source/path/content/member/profile identities remain distinct;
8. generator output is byte-identical under `--check` from a detached copied
   repository root;
9. focused parity tests, the full parity documentation gate, and link checks
   pass; and
10. all counters remain at current truth: zero native outcomes, zero paired
    cells, zero complete paired-population authorities, and zero parity credit.

## 11. Primary sources and design references

- Lean v4.30.0's pinned
  [test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
  distinguishes directory and pile execution and the observable behavior of
  elaboration, expected-failure, compile/interpreter, server, Lake, package,
  and benchmark families.
- Lean's
  [elaboration and compilation reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
  separates elaborator output, kernel checking, environment serialization,
  `.ilean` data, compiler IR/native output, and initialization.
- Lean's
  [source-file and module reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
  specifies modifier-sensitive import visibility and multi-part module
  environments, supporting layer-specific rather than byte-only comparison.
- [BenchExec's execution documentation](https://github.com/sosy-lab/benchexec/blob/main/doc/benchexec.md)
  keeps commands/configurations, task sets, limits, per-execution results,
  resource measurements, and raw logs explicit. It is a methodology reference;
  TL0.6.5 does not adopt BenchExec or authorize a process.
- Axeyum's accepted
  [resumable execution ADR](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md),
  [execution-evidence contract](lean-execution-evidence-tl0.7.1-2026-07-22.md),
  and [complete parity contract](lean4-complete-parity-contract-2026-07-22.md)
  remain authoritative for immutable attempt/completion handling and terminal
  claims.

## 12. Non-claims

This plan does not claim that:

- TL0.6.3 or TL0.6.4 is complete;
- 408,374 execution slots are already runnable or equal the final comparison-
  obligation count;
- one official command can be translated mechanically into a native command;
- equal process exits imply equal elaboration, kernel, module, runtime, or
  editor behavior;
- normalization may erase unregistered fields or substitute byte equality for
  semantic equality;
- a bounded prefix, equal total count, or all-agree registered subset proves
  U2 coverage;
- official acceptance grants Axeyum independent-kernel assurance;
- functional agreement implies performance parity; or
- any complete Lean 4.30, maintained Lean 4, or 100% parity claim is currently
  permitted.

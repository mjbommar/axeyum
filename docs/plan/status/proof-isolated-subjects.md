# Lane: proof-isolated-subjects — a subject in an ephemeral kernel is still a subject

<!-- plan-section: lane-status -->

**Done (`proof-isolated-subjects`, 2026-08-31).** `scripts/check-trust-closure.py`'s
`unresolved` moved **62 -> 20**, `subjects` **2121 -> 2123**, with a **fifth
guard** now examining the 40 facts three of the four guards structurally could
not reach. No floor was raised to make room; `resolved` is untouched, so
`min_ratio` still sits at 0.9579 with the headroom it had. Decision recorded in
[ADR-1285](../../research/09-decisions/adr-1285-a-proof-isolated-subject-is-a-subject-and-the-registry-names-it.md).

## The live count and the mechanism, read from code

62 unresolved, measured against a freshly-built projection. The split is clean
and it is not the one the brief assumed:

| bucket | count |
| --- | --- |
| rides an `axeyum-lean-import/*` executor driver (proof-isolated) | **40** |
| no registered autogenesis operation at all | **22** |

All 40 are `ml430-*`. Six distinct drivers: `sealed-kernel-capsule-v1` (16),
`conclusion-directed-family-multi-target-v1` (10),
`modeq-family-multi-target-v1` (8), `imported-candidate-family-multi-target-v1`
(3), `bounded-induction-multi-target-v1` (2),
`dependency-theorem-receipt-v1` (1).

The mechanism, read from the code path rather than a doc: the checker script
(e.g. `scripts/check-autogenesis-modeq-family.py`) shells out to
`cargo run --release -p axeyum-lean-import --example modeq_family_operation`,
which calls `axeyum_lean_import::import_statement_ndjson` to build a **fresh
`Kernel`**, admits the candidate with `Kernel::add_declaration` under a
content-addressed name, runs `modeq_family::audit_circularity` over
`Kernel::declaration_dependency_closure`, prints a receipt, and exits. The
kernel is dropped. Nothing is merged into the persistent preludes: verified by
looking up all 40 registry-named subjects in `kernel_declaration_projection` —
**zero present**.

## Isolation is by design, and the reason is soundness

- **ADR-0480** decides it: a proposition enters as `def target : Prop := P`, and
  the boundary rejects the whole stream on any axiom, theorem, opaque or
  quotient, because exporting `axiom target : P` "gives the imported environment
  an inhabitant of `P`" and a producer could then close the goal by citing the
  adapter axiom. Merging these declarations into the shared environment is what
  that design exists to prevent.
- The registry says it in a field: `producer.input_kind:
  "axeyum-proof-isolated-kernel-goal"`.
- **ADR-0601 §3** forbids it separately: import scaffolding must not enter the
  inventories or the axiom-free counts.

So the gap was in the DESCRIPTION, not the isolation.

## Which option, and why over the others

Chosen: **teach the model to say it** — a derived `isolated` bucket plus a
fifth guard.

- **`kernel_theorem: null`** — refused, as the brief required. That field means
  "not about exactly one kernel theorem" and these are about exactly one.
- **Resolve against the isolated environment** — rejected. It would run an
  `axeyum-lean-import` example per fact inside an L0 gate that reads one TSV
  today, and the environment is discarded by construction, so there is nothing
  stable to compare between runs. The registry's `goal_sha256` /
  `declaration_sha256` already pin what it contained.
- **Demote to `imported-kernel-lean`** — the brief said this deserved real
  weight, and it got it. **Refuted on the evidence, and no count shrinks.**
  `validate-facts.py` gives that route two reasons: authorship, and a trust base
  that additionally assumes the exporter rendered the source *proof* faithfully;
  it says `[]` is unavailable there. For these facts the proof was constructed
  here — provenance records "statement-only extraction … no proof value was
  exposed" and "the proof term and tactic trace were not consulted", and the
  audit computed from `declaration_dependency_closure` reports `axioms=0`,
  `theorem_dependencies=0`, `target_dependency=false`. Their empty
  `axiom_footprint` was measured, not assumed. What IS imported is the
  STATEMENT, and that is already disclosed per fact in `provenance.prior_art`
  naming the pinned Mathlib commit.
- **A hand-authored `formal.isolated_kernel_theorem`** — rejected for the reason
  the identity map in the same script is derived: an authored field can encode a
  wish. The registry entry is what the executor actually runs.

## What the counts change to

| | before | after |
| --- | --- | --- |
| `subjects` (resolved) | 2121 | **2123** |
| `unresolved` | 62 | **20** |
| `isolated` (newly guarded) | — | **40** |
| `dual` (persistent + isolated) | — | **4** |
| `declarations` | 2729 | **2779** |
| `identity_classes` / `disclosed_equivalent_pairs` | 15 / 14 | 15 / 14 |
| `validate-facts.py` | 0 errors | **0 errors**, 2511 facts |

**No headline number shrinks.** Nothing was relabelled off `kernel-lean`, no
axiom-free count moves, and the ratio floor stayed at 0.9579.

`dual` is the one genuinely new observation: 4 facts
(`F:ml430-nat-ascfactorial-zero-fd183202`,
`F:ml430-nat-descfactorial-one-d4856d4a`,
`F:ml430-nat-descfactorial-zero-966b01df`, `F:ml430-nat-fib-add-two-b86e0c82`)
resolve to a NATIVE persistent theorem while their registered operation checked
an isolated `Axeyum.Autogenesis.Statement.*` import. Both are true. The guards
walk the native closure; the fact's evidence is the import's receipt. Reported
rather than absorbed.

## The 2 umbrella facts: they do not exist, and finding that out found a bigger hole

ADR-1265 recorded 2 facts as "several distinct `evidence[].kernel_declaration`
(umbrella facts)". Reproduced the query exactly: today the two that are
unresolved AND lack a `formal.kernel_theorem` key are
`F:excluded-middle-not-intuitionistic` (4 declarations) and
`F:heyting-3-chain-refutes-excluded-middle` (3). So the count was right.

**The classification was not.** Each is about exactly ONE theorem — the others
are supporting lemmas — and each was verified by comparing the fact's
`formal.statement` **byte-for-byte** against the declaration's rendered
canonical type, never by name:

    F:excluded-middle-not-intuitionistic       -> ipc_excluded_middle_not_provable
    F:heyting-3-chain-refutes-excluded-middle  -> ipc_heyting_join_not_ne_top

Nobody could check that, because **none of the three tools that build the
constructed preludes built the IPC package**: `kernel_declaration_projection`,
`prelude_theorem_inventory` and `cross_prelude_collision_tests.rs` all stopped
at 10 groups. An empty answer from a tool never pointed at the subject is
indistinguishable from the declarations not existing — and it produced a wrong
census entry that stood in an accepted ADR.

`scripts/check-theorem-inventory-completeness.py` exists to catch exactly this
(a group in two of the three tools and missing from the third). It could not:
its label regex reads `Group { label: "…" }` and the collision test had been
refactored to `Group::of("…", &k)`, so it matched **zero** occurrences and
refused to compare against an empty set. Correct, fail-closed — and invisible,
because it is registered in **no `check.sh`, no `local-ci.sh`, no `justfile`**.
Widened to accept both shapes (two new controls pin the constructor half) and
registered in `check.sh`. With `ipc` built in all three: **2255 distinct theorem
names agree, 11 group labels agree**, and
`every_declaration_a_prelude_introduces_is_checked_and_axiom_free` covers the
IPC declarations for the first time (8 collision tests green).

## Proof the check fires

Against the **real ledger**, not a fixture — `--facts`/`--operations`/
`--projection` point at scratch copies, so no tracked file is touched. Baseline
green, each mutation fires its own tag with a nonzero exit, restored, green
again:

| mutation | tag |
| --- | --- |
| append a projection row declaring `Nat.gcd_greatest` (ADR-0480 quarantine broken) | `ISOLATED-SUBJECT-LEAKED` |
| drop `executor.target_theorem` from the gcd-greatest capsule operation | `ISOLATED-SUBJECT-UNNAMED` |
| set the fib-dvd capsule's `axiom_footprint_policy` to `"any"` | `ISOLATED-FOOTPRINT-UNPOLICED` |
| give `F:ml430-nat-fib-gcd-d1d98407` a non-empty `axiom_footprint` | `ISOLATED-FOOTPRINT-DISAGREES` |
| empty every import driver's `applicability.fact_ids` | `ISOLATED-POPULATION-BELOW-FLOOR` |

`scripts/tests/test-trust-closure.sh`: **22 cases, 20 mutations, each killing
exactly one.** The fixture carries TWO proof-isolated facts deliberately — with
one, deleting it makes the guard scan nothing, the generic zero-executed-cases
meta-guard rejects instead of the floor, and the floor's mutation would kill no
case at all.

## `annotate-trust-closure-kernel-theorem.py`: leave it unwired, and here is why

Not a deferral. It reports **0 unapplied candidates against 20 unresolved**, so
as a standing gate it ratchets nothing the trust-closure population floor does
not already ratchet, and it runs a full `--release` projection build to say so.
Its value is as a RECOVERY tool when a batch lands under-annotated — run it
then. If it is ever wired, it should be `--check` beside `trust-closure`,
sharing that step's projection rather than building a second one. Its own
controls pass (11 cases, 1 mutation killing exactly one).

## What the brief got wrong, and what I got wrong

- **"~36 `ml430-*` facts"** — it is **40**, and the discriminator is not
  `producer.input_kind`. Only 16 of the 40 carry
  `"axeyum-proof-isolated-kernel-goal"`; the rest declare
  `axeyum-sealed-kernel-theorem-capsule`, `axeyum-checked-theorem-slices` or
  `axeyum-imported-candidate-family-goal`, which are the OUTPUTS of an earlier
  isolated stage fed back in. The `executor.driver` namespace is the one that
  partitions cleanly: 40 / 0 / 22, no ambiguity.
- **"the ~19 non-`ml430` residue"** — it is **22**, and every one of them has no
  registered operation at all, which is a cleaner statement than the prior
  lane's mixed bucket.
- **My own first pass reported `F:ml430-nat-fib-coprime-fib-succ-162fc738` as
  having no registry-named subject.** It has one — `executor.target_definition`,
  singular, at executor level, a third shape my extractor did not read. The
  finding was an artifact of my query, not of the registry, and it would have
  become a false `ISOLATED-SUBJECT-UNNAMED` in the shipped gate.
- **The prebuilt `kernel_declaration_projection` in the shared checkout was
  stale by 9 declarations** and produced 9 spurious `SUBJECT-ABSENT` rows for
  `Int.sumRange*` theorems that had landed hours earlier. The documented
  stale-binary hazard, demonstrating itself in the first ten minutes. Every
  absence claim in this lane is against a freshly-built binary.

## Two `check.sh` steps are RED on `main`, and it is not this lane

Verified by rebuilding the projection example at its parent content and
re-running both, so this is a measurement rather than an inference:

- `autogenesis-kernel-projection-fresh`
  (`gen-autogenesis-kernel-dependency-projection.py --check`) — stale before
  this change and after. Not regenerated here: doing so would sweep a sibling
  lane's `Int.sumRange` landing into this lane's commit.
- `curriculum-bucket-cohesion` — 3 findings, naming `Int.sum*`, `Nat.count*`
  and `Nat.primrec*`. None IPC, none this lane's.

<!-- plan-section: landed-changes -->

| 2026-08-31 | | `scripts/check-trust-closure.py` — `isolated`/`dual` subject buckets derived from the operation registry, plus `guard_isolated_subject` (5 rejections). `unresolved` 62 -> 20, `subjects` 2121 -> 2123, no floor raised |
| 2026-08-31 | | `scripts/check-trust-closure.py --update` — no longer raises `min_ratio` without `--update-ratio` (a routine update left ZERO headroom), and no longer DELETES `ratio_floor_note` |
| 2026-08-31 | | `scripts/tests/test-trust-closure.sh` — 22 cases, 20 mutations, each killing exactly one; fixture gains a two-member proof-isolated population |
| 2026-08-31 | | `kernel_declaration_projection` / `prelude_theorem_inventory` / `cross_prelude_collision_tests.rs` — all three build the `ipc` group; 2255 theorem names and 11 labels agree |
| 2026-08-31 | | `scripts/check-theorem-inventory-completeness.py` — label regex accepts `Group::of("…")` (it had matched zero since the constructor refactor); registered in `check.sh`; +2 controls |
| 2026-08-31 | | `F:excluded-middle-not-intuitionistic`, `F:heyting-3-chain-refutes-excluded-middle` — `formal.kernel_theorem` set, each verified byte-for-byte against the rendered canonical type; the "2 umbrella facts" were never umbrellas |
| 2026-08-31 | | [ADR-1285](../../research/09-decisions/adr-1285-a-proof-isolated-subject-is-a-subject-and-the-registry-names-it.md) — a proof-isolated subject is a subject, and the operation registry names it |

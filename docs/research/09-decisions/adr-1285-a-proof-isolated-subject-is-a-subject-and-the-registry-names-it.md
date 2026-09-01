# ADR-1285: A proof-isolated subject is a subject, and the operation registry names it

Status: accepted
Date: 2026-08-31
Index-summary: 40 settled kernel-lean facts are checked in an ephemeral kernel, so no persistent declaration is their subject; `check-trust-closure.py` gains a derived `isolated` bucket and a fifth guard rather than a `kernel_theorem: null` that would misdescribe them.
Index-status: accepted

## Context

`scripts/check-trust-closure.py` (S2, ADR-0717 risk 4) classifies a settled
`kernel-lean` fact by resolving its SUBJECT — the one declaration it is about —
and then walks that declaration's transitive closure. A fact whose subject it
cannot resolve still counts toward `kernel_facts`, but is not a subject, so
`guard_self_occurrence`, `guard_alias_occurrence` and `guard_forbidden_trust`
never examine it.

The `resolve-kernel-subjects` lane took `unresolved` from 90 to 62 by annotating
28 genuinely under-annotated facts, and reported that the residue is not one
thing. Measured here on 2026-08-31, against a freshly-built
`kernel_declaration_projection` (the stale prebuilt binary in the shared
checkout reported 9 spurious `SUBJECT-ABSENT` rows for declarations that had
landed hours earlier — the documented stale-binary hazard, and it demonstrated
itself before anything else in this lane):

| bucket | count |
| --- | --- |
| rides an `axeyum-lean-import/*` executor driver | **40** |
| no registered autogenesis operation at all (bundles, meta-facts, per-query reconstructions) | **22** |

Every one of the 40 is an `ml430-*` mirror. Their check runs
`axeyum_lean_import::import_statement_ndjson`, which builds a **fresh
`Kernel`**, admits the candidate proof into it with `Kernel::add_declaration`,
audits it, and discards the environment. Nothing is merged into the persistent
preludes, so the Mathlib-style name is absent from the projection — verified by
lookup, all 40, zero present.

### The isolation is deliberate, and the reason is soundness

ADR-0480 decides it explicitly. A nursery proposition `P` enters as the value of
a transparent definition `def target : Prop := P`, and the import boundary
**rejects the whole stream** if it contains any axiom, theorem, opaque
declaration or quotient primitive. The ADR states the hazard in one line:
exporting `axiom target : P` "gives the imported environment an inhabitant of
`P`", so a producer could close the goal by citing the adapter axiom and "the
infrastructure would have converted a source statement into its own answer."

The registry says the same thing in a field: those operations declare
`producer.input_kind: "axeyum-proof-isolated-kernel-goal"`.

Merging the imported statement declarations into the shared environment is
precisely what that design exists to prevent. It would also put Mathlib-spelled
names into every inventory and every axiom-freedom sweep at once, which
ADR-0601 §3 forbids for import scaffolding independently.

**So the gap is in how the ledger and the gate DESCRIBE these facts, not in the
isolation.**

### Why the two obvious repairs are wrong

- **`formal.kernel_theorem: null`.** That field's documented meaning is "not
  about exactly one kernel theorem". These facts are about exactly one — the
  registry names it, `goal_sha256` and `declaration_sha256` pin it. Writing
  `null` would misrepresent a single-subject fact as a bundle, which is a worse
  statement than saying nothing.
- **Demote them to `imported-kernel-lean`.** Refuted on the evidence.
  `validate-facts.py`'s own comment gives that route two reasons — authorship
  ("a `kernel-lean` fact is one this project constructed a proof of") and trust
  base (an import additionally assumes the exporter rendered the source
  environment faithfully) — and says `[]` is unavailable there. For these facts
  the **proof was constructed here**: the provenance records "statement-only
  extraction … no proof value was exposed" and "the proof term and tactic trace
  were not consulted", and the circularity audit computed from
  `Kernel::declaration_dependency_closure` reports `axioms=0`,
  `theorem_dependencies=0`, `target_dependency=false`. An imported fact carries
  Lean's axioms and the export pipeline's trust assumptions in a NON-empty
  `axiom_footprint`; these carry an empty one because an empty one was measured.
  Their `kernel-lean` route is correct and **no headline count shrinks.**

  What IS imported is the STATEMENT, and that is already disclosed, per fact, in
  `provenance.prior_art` naming the pinned Mathlib commit.

## Decision

1. **`subject_of` keeps three tiers; `Subjects` gains two buckets.** A fact
   whose own fields name a declaration is that declaration's, whatever else
   checks it — the registry answers only the question the fact left open, and
   never overrides an answer it gave.

   - `isolated` (40) — unresolved by tiers 1-3 AND claimed by an
     `axeyum-lean-import/*` executor driver.
   - `dual` (4) — resolves to a persistent declaration AND rides such a driver.
     Counted as ordinary subjects, because their persistent declaration is real
     and its closure is worth auditing, and reported separately, because the
     declaration the guards walk is a NATIVE proof of the proposition while the
     fact's evidence is the isolated import's. Both are true; only saying both
     is honest.

2. **The subject name is DERIVED from `artifacts/autogenesis/operations.json`,
   never authored.** A fact cannot declare itself proof-isolated; the operation
   that runs the check decides. Read in this order, and the order matters — a
   multi-target driver's `executor.targets[]` is keyed BY FACT, while
   `executor.target_theorem` is the operation's single target, so reading the
   operation-level field first would give every member of a family the same
   name:

       executor.targets[] entry whose fact_id == this fact  ->  target_definition
       executor.target_theorem
       executor.target_definition

   All 40 resolve. Two claiming operations that disagree on the name yield no
   name, which the guard rejects rather than picking arbitrarily.

3. **`guard_isolated_subject` is a fifth guard**, rejecting five ways, each
   looking at a different thing: no per-fact subject named; the named subject
   PRESENT in this environment (the ADR-0480 quarantine broken, or a fact that
   should stop being isolated); a claiming operation that does not require an
   empty footprint; a fact contradicting that policy; and a pinned
   `min_isolated` population floor, so deleting the facts or the operations
   cannot make the guard green by leaving it nothing to examine.

4. **No floor moved to make room.** `resolved` is untouched, so `min_subjects`
   and `min_ratio` mean exactly what they meant. Separately, `--update` no
   longer raises `min_ratio` unless `--update-ratio` is passed: that ratio's
   denominator is every kernel-route settled fact, so a routine `--update`
   ratchets it to the observed value and leaves ZERO headroom, and the next
   fact landing without naming its declaration then reds an L0 gate with a
   message about a population floor. `--update` was also silently DELETING
   `ratio_floor_note`, the recorded argument for where the ratio sits; it is
   carried forward now.

5. **The "2 umbrella facts" do not exist.** ADR-1265 counted 2 facts as about
   several theorems at once. Each is about exactly one:
   `F:excluded-middle-not-intuitionistic` about
   `ipc_excluded_middle_not_provable`, and
   `F:heyting-3-chain-refutes-excluded-middle` about
   `ipc_heyting_join_not_ne_top` — verified by comparing each fact's
   `formal.statement` BYTE-FOR-BYTE against the declaration's rendered canonical
   type, not by name. Their other evidence rows name supporting theorems, which
   is why the "unambiguous single `kernel_declaration`" tier fell through.

   Nobody could check that, because **none of the three tools that build the
   constructed preludes built the IPC package.** All three now build it as the
   `ipc` group; see Consequences.

## Evidence

Baseline, real ledger, freshly-built projection:

    TRUST_CLOSURE|declarations=2779|identity_classes=15|kernel_facts=2183|
      subjects=2123|unresolved=20|isolated=40|dual=4|absent=0|
      disclosed_equivalent_pairs=14|failures=0
      guard isolated_subject   scanned=44 rejected=0

**The guard fires, proved against the REAL ledger rather than a fixture**
(`--facts`/`--operations`/`--projection` point at scratch copies; no tracked
file is touched). Each mutation, then restored, with the baseline green before
and after:

| mutation | tag |
| --- | --- |
| append a projection row declaring `Nat.gcd_greatest` (quarantine broken) | `ISOLATED-SUBJECT-LEAKED` |
| drop `executor.target_theorem` from the gcd-greatest capsule operation | `ISOLATED-SUBJECT-UNNAMED` |
| set the fib-dvd capsule's `axiom_footprint_policy` to `"any"` | `ISOLATED-FOOTPRINT-UNPOLICED` |
| give `F:ml430-nat-fib-gcd-d1d98407` a non-empty `axiom_footprint` | `ISOLATED-FOOTPRINT-DISAGREES` |
| empty every import driver's `applicability.fact_ids` | `ISOLATED-POPULATION-BELOW-FLOOR` |

`scripts/tests/test-trust-closure.sh`: **22 cases, 20 mutations, each killing
exactly one.** The fixture carries TWO proof-isolated facts on purpose — with
one, deleting it makes the guard scan nothing and the generic
zero-executed-cases meta-guard rejects instead of the floor, so the floor's own
mutation would kill no case at all.

## Consequences

- **A whole prelude group was invisible to every tool, and one checker that
  should have caught it was broken and unregistered.**
  `kernel_declaration_projection`, `prelude_theorem_inventory` and
  `cross_prelude_collision_tests.rs` all stopped at 10 groups and never built
  the IPC package. `check-theorem-inventory-completeness.py` exists precisely to
  catch a group present in two of the three and missing from the third — and its
  label regex reads `Group { label: "…" }` while the collision test had been
  refactored to `Group::of("…", &k)`, so it matched zero occurrences and refused
  to compare against an empty set. Correct, fail-closed, and invisible, because
  it is named in no `check.sh`, no `local-ci.sh` and no `justfile`. Widened to
  accept both shapes (two new controls pin the constructor half) and registered
  in `check.sh`. With `ipc` built in all three: 2255 distinct theorem names
  agree, 11 group labels agree, and
  `every_declaration_a_prelude_introduces_is_checked_and_axiom_free` covers the
  IPC declarations for the first time.
- Counts that move, all in the direction of more checking:
  `subjects` 2121 → 2123, `unresolved` 62 → 20, `declarations` 2729 → 2779,
  `isolated` 40 and `dual` 4 newly guarded. `identity_classes` (15) and
  `disclosed_equivalent_pairs` (14) unchanged. `validate-facts.py`: 2511 facts,
  0 errors. **No headline number shrinks**; nothing was relabelled off
  `kernel-lean`, and no axiom-free count changes.
- The 22 facts with no registered operation are a separate, unfinished
  question. They are genuine bundles (`F:int-categoricity` names four
  `Int.Characterization.*` declarations), meta-facts about module size or
  interface structure, and per-query ad hoc reconstructions with no stable
  declaration name. Marking them needs a per-fact reading, not a rule.
- `scripts/annotate-trust-closure-kernel-theorem.py` stays **unwired**, and that
  is now a positive decision rather than a deferral. It reports 0 unapplied
  candidates and 20 unresolved, so as a standing gate it would ratchet nothing
  the trust-closure population floor does not already ratchet, and it runs a
  full `--release` projection build to say so. Its value is as a recovery tool
  when a batch of facts lands under-annotated; run it then. If it were wired, it
  should be as `--check` beside `trust-closure`, sharing that step's projection
  rather than building its own.

## Alternatives considered

- **Teach `subject_of` to resolve against the isolated environment the check
  builds.** Rejected: it would mean running an `axeyum-lean-import` example per
  fact inside an L0 gate that today reads one TSV, and the isolated environment
  is discarded by construction — there is nothing stable to compare against
  between runs. The registry's content-addressed `goal_sha256` /
  `declaration_sha256` already pin what that environment contained, and the
  fact's own `checker_command` re-derives it.
- **A hand-authored `formal.isolated_kernel_theorem` field.** Rejected for the
  reason the identity map in this same script is derived rather than authored:
  an authored field can encode a wish. The registry entry is what the executor
  actually runs.

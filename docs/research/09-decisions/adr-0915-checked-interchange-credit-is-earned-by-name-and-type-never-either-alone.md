# ADR-0915: Checked-interchange credit for a root is earned by pinned Lean's own name admission AND independent type identity, never either alone

Status: accepted
Date: 2026-08-30
Index-summary: L4 phase C2 builds the universal checked-interchange pipeline
(export the exact reachable Axeyum closure, fresh-reimport it through an
independent reader, submit it to pinned Lean's kernel, grade acceptance) over
the "credited roots" -- the 9 declarations in ADR-0835's graph join whose
`trust_footprints` dimension resolved, out of 446 in `mathlib-group-defs-v1`
-- and requires every accepted grade to be evidenced by BOTH pinned Lean's own
`env.constants` membership by name AND independently-rendered type identity
across two separately-constructed `Kernel` instances, never a name match
alone.

## Context

`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C2
asks, for every headline theorem representable in the pinned Lean slice: (1)
export the exact reachable Axeyum closure; (2) fresh-import or replay it
through an independent path; (3) submit it to pinned Lean's kernel; (4) bind
the result to the fact receipt. Its exit criterion: the generated credit
census reports expected, attempted, accepted, declined-by-typed-reason,
missing, and extra counts, with `missing=0` mandatory and declines never
silently inheriting Lean-accepted credit.

Two prior measured facts bound how this must be built:

- **ADR-0716** measured `Nat.multichoose`: an identical NAME naming a
  DIFFERENT proposition across two systems. A credit mechanism that grades by
  name alone can silently manufacture a false identity.
- CLAUDE.md's own account of the `nra_monomial_bound_cert.rs` incident: a
  certificate that could not express a distinction its producer made (`<`
  versus `<=`) accepted a forged refutation of a satisfiable query, and
  mutation testing could not find the gap because the missing guard was never
  written.

`crates/axeyum-lean-kernel/src/lean_export.rs` (the root-selected `lean4export`
NDJSON writer), `crates/axeyum-lean-import` (the fail-closed independent
reader), and `crates/axeyum-lean-kernel/tests/real_lean_replay_census.rs`
(S4, ADR-0717's independent-replay-graded-by-name suite for the whole `creal`
carrier) already exist and are reused, not reimplemented, per the task's
explicit instruction and per this repository's standing rule that a second
mechanism for one question is how two answers start disagreeing.

## Decision

1. **The credited-root population is the join's own `trust_footprints`
   dimension, never a hand-picked list.** ADR-0835's graph join resolves,
   over the bounded 446-declaration `mathlib-group-defs-v1` population: 9
   declarations with an exact-title Mathlib mirror fact (`fact_ids`), all 9
   of whose kernel theorems exist in this environment (`kernel_declarations`),
   all 9 of whose kernel-reported `axiom_footprint` is empty
   (`trust_footprints`). That 9-of-446 set -- `Nat.add_comm`,
   `Nat.add_pos_right`, `Nat.ble_eq_true_of_le`, `Nat.ble_self_eq_true`,
   `Nat.ble_succ_eq_true`, `Nat.le_of_ble_eq_true`, `Nat.le_of_lt_succ`,
   `Nat.le_of_succ_le_succ`, `Nat.le_refl` -- is "credited": it carries ledger
   credit, which is exactly the roadmap's scoping word for C2.
   `artifacts/checked-interchange/populations/credited-roots-v1.json` is a
   committed snapshot of that set; `scripts/check-checked-interchange.py`'s
   `STALE_POPULATION` guard re-derives the same set from a FRESH read of the
   live `artifacts/graph-join/*.join.json` file, never from the snapshot's
   own fields, so a name silently dropped from the join is caught as
   staleness rather than papered over -- the same "external authority the
   pack does not control" pattern ADR-0800's `MISSING` guard uses against its
   own population file.

2. **Export reuses `render_lean4export_ndjson_roots`/`root_declaration_closure`
   verbatim.** No second closure-computation or digest mechanism is built.
   The credited roots' combined closure is exported once, submitted to both
   independent paths, and graded per-name.

3. **Two independent paths, matching the roadmap's picture exactly.**
   - Fresh reimport: `axeyum_lean_import::import_ndjson`, a completely
     independently-coded reader, into a BRAND NEW empty `Kernel` built from
     nothing but the wire bytes.
   - Pinned Lean kernel replay: `scripts/lean/replay-lean4export.lean`, the
     same script S4 uses, bypassing Lean's elaborator entirely and handing
     declarations straight to `Lean.Environment.addDeclCore`.

4. **A credited root is graded ACCEPTED only when BOTH conditions hold**,
   checked in the test suite and re-verified by two dedicated checker guards:
   - **By name**: pinned Lean's own `env.constants` (read back via
     `replay-lean4export.lean --emit-names`, never the transmitted stream)
     contains a constant of exactly that name. `BARE_NAME_ACCEPT` fails a
     census that marks a root `accepted` without this.
   - **By type**: the type this kernel checked and the type the fresh
     reimport rebuilt from the wire bytes render to BYTE-IDENTICAL text via
     `Kernel::render_lean`, compared across two SEPARATELY-CONSTRUCTED
     `Kernel` instances (the source kernel, and the one `import_ndjson`
     built from scratch). `BARE_TYPE_ACCEPT` fails a census that marks a root
     `accepted` without this.

   Neither guard is redundant with the other: `BARE_NAME_ACCEPT` is exactly
   the guard `Nat.multichoose` needs (a name match with no type check behind
   it would have accepted a differently-defined declaration); `BARE_TYPE_ACCEPT`
   is the guard a forged census entry needs (a fabricated "accepted" status
   with the type-identity field simply not populated).

5. **Four adversarial fixtures, one per distinction the exporter/importer
   make**, run against the real committed 9-root closure and real pinned
   Lean:
   - **Wrong proof** (same goal, substituted proof) and **wrong goal** (same
     proof, substituted goal) must be rejected by BOTH the fresh reimport
     (`import_ndjson` returns `Err`) and pinned Lean (`REAL LEAN KERNEL
     REJECTED`).
   - **No inheritance**: exporting one credited root's closure alone must not
     confer a grade on an uncredited sibling declared in the same source
     module (`Nat.le_succ`, which shares `nat_prelude`'s order-lemma cluster
     with `Nat.le_refl` but has no mirror fact).
   - **Declined by typed reason**: a synthetic `Theorem` whose type is `Nat`
     itself (this kernel's `Theorem` variant carries no `Prop` requirement;
     Lean's kernel refuses a `theorem` whose type is not a proposition)
     proves the decline path is real. It is reported SEPARATELY
     (`decline_mechanism_probe`, `synthetic: true`) and never contributes to
     the 9 real roots' accepted count; `DECLINE_PROBE_VACUOUS` fails a census
     where this probe reads as accepted.

   All four run live against pinned Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`)
   in `crates/axeyum-lean-import/tests/checked_interchange_credited_roots.rs`;
   none is asserted without running it.

6. **What this format cannot express is a finding, not a gap, and it is not
   re-derived.** `lean_export.rs`'s own module documentation already records
   that `letE.nondep`, `isReflexive`, and non-mutual `all` are wire metadata
   this kernel does not model at all, emitted in a fixed conservative form
   regardless of the source construct. A round trip through this interchange
   cannot preserve a distinction along those three axes because the SOURCE
   kernel never tracked one to begin with.

7. **The gen/check split matches C1's own posture.** `scripts/
   gen-checked-interchange.py` is a thin wrapper that runs the real pipeline
   (needs pinned Lean, a cargo build, `AXEYUM_REQUIRE_LEAN=1` forced so it
   cannot produce a silently-vacuous census by skipping); `scripts/
   check-checked-interchange.py` validates the committed census with no
   Lean toolchain and no cargo run, and is the only one of the two registered
   in `just check`/`scripts/check.sh` -- identical to how `check-declaration-
   graph.py`/`check-graph-join.py` are gated while their `gen-*` counterparts
   are not.

8. **Seven guards, seven distinct mutation classes, mutation-verified 1:1**
   (`scripts/tests/test-checked-interchange-mutations.sh`):

   | Mutation | Guard | What only that guard checks |
   |---|---|---|
   | dropped root | `MISSING` | every population-named root present in the census |
   | drifted population | `STALE_POPULATION` | the population snapshot matches the LIVE graph-join, not its own frozen copy |
   | miscounted totals | `ACCOUNTING` | `accepted+declined_typed+missing == expected`, `len(roots)==expected` |
   | nonzero missing | `MANDATORY_MISSING_ZERO` | C2's exit clause is mandatory, not merely reported |
   | name-only accept | `BARE_NAME_ACCEPT` | an accepted root's Lean-by-name evidence |
   | type-only-missing accept | `BARE_TYPE_ACCEPT` | an accepted root's type-identity evidence |
   | vacuous decline probe | `DECLINE_PROBE_VACUOUS` | the decline path was actually exercised |

## Alternatives

**Grade acceptance by Lean's stream-acceptance exit status alone (`lean_accepted_stream`), without a per-name membership check.** Rejected: a
combined-closure stream accepting overall says nothing about which INDIVIDUAL
names Lean actually holds afterward -- exactly the aggregate-vs-individual gap
S4's own module documentation identifies ("a strong statement about the
carrier and a weak one about any particular theorem in it").

**Recompute content digests for identity instead of comparing rendered
type text across two Kernel instances.** Rejected: this would be a second
identity mechanism alongside `Kernel::render_lean`, which every other
identity claim in this repository already reads from (`nat_theorem_inventory`,
the `ml430` mirror-flip criterion). Two independently-constructed kernels
agreeing on rendered text is the same "different implementation, same
conclusion" evidence ADR-0800 requires of its two readers.

**Skip the synthetic decline probe and rely on the classifier's own
documentation that Lean refuses a non-Prop theorem.** Rejected per this
repository's standing rule that an assertion about what a tool refuses must
be earned by running it, not assumed -- `real_lean_replay_census.rs`'s own
`lean_really_does_refuse_a_theorem_whose_type_is_not_a_proposition` test
already established this pattern for the `creal` carrier; C2 needed its own
instance because the credited-root population is a different (and
Prop-only) slice with no naturally-occurring non-Prop declaration to sample.

## Consequences

C3 (the thin Lean adapter) can treat a `status: "accepted"` census row as
carrying both name and type evidence without re-deriving either. Extending
the credited-root population beyond these 9 (as more `ml430` mirrors resolve
in ADR-0835's join) needs no new identity mechanism, only a wider population
snapshot re-checked by `STALE_POPULATION` against the live join. The census
covers 9 of 446 declarations in the underlying population -- the 437
uncredited declarations have no ledger fact at all and are out of C2's scope
by the roadmap's own "credited roots" phrasing; this is stated rather than
hidden, matching ADR-0820's and ADR-0835's own "what this does not capture"
sections.

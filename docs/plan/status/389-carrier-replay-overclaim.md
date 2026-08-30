# Carrier replay overclaim — correcting the whole-carrier Lean replay claim

<!-- plan-section: lane-status -->

Lane: `carrier-replay-overclaim`. Decision:
[ADR-0775](../../research/09-decisions/adr-0775-the-non-prop-residue-is-a-recorded-boundary-not-a-silent-exclusion.md).
Follows L0/S4's census ([386](386-l0-s4-independent-replay.md), ADR-0760),
which found this.

## Status

Landed. `F:lean-kernel-accepts-the-whole-constructed-real-carrier` claimed
pinned Lean's kernel accepts EVERY declaration of the constructed-real carrier.
It does not. The statement is narrowed to what is measured, the superseded one
is preserved three ways including as a test that fails if it ever becomes true
again, and the 73 declarations it no longer covers are a typed, named, counted
boundary plus their own OPEN ledger row.

## The measurement

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier, all four tests
green in 146 s:

    AXEYUM-CREAL-CARRIER counts_agree population=2058 representable=1985
      lean_kernel_constants=1985 non_representable=73
    AXEYUM-CREAL-CARRIER superseded-claim-refuted
      rejected_by_lean=CReal.weierstrassMTest reason=theorem-type-not-prop
      theorem_type_not_prop=48
    AXEYUM-CREAL-CARRIER tampered-proof-rejected subject=CReal.Equiv.not_zero_one
    AXEYUM-CREAL-CARRIER residue-typed population=2058 representable=1985
      theorem_type_not_prop=48 blocked_by_dependency=25 untyped=0

S4 measured the same residue (48 + 25) at population 2,045 / representable
1,972; the carrier grew between the runs, the residue did not.

**Nothing was proved wrong.** `Lean.Environment.addDeclCore` refuses a
`theorem` whose type is not a `Prop`; this kernel has no such rule and uses the
freedom deliberately (`CReal.UniformConvergesOn` is `Type`-valued so a
convergence rate is data). Lean refused a KIND, never a proof. What it was is
73 declarations of the flagship carrier holding no independent-replay grade
with nothing in the ledger saying so.

## What changed, and how the old statement survives

| | |
|---|---|
| corrected statement | every declaration Lean's kernel accepts **as the kind this kernel declares it** — 1,985 of 2,058, no reachability filter — replays, with Lean's final constant count EQUAL to that population; the residue is 48 not-a-proposition theorems plus 25 blocked behind one; and the unfiltered export is REJECTED, naming one of the 48 |
| status | stays `proved`, on the corrected statement |
| previous statement | verbatim in the fact's `notes`; amendment row in `artifacts/ontology/settled-fact-statement-pins.json` with both SHA-256 digests and a reason (S1's rule); and EXECUTABLE as `the_superseded_whole_carrier_claim_is_refuted_by_the_same_binary` |
| the part no longer claimed | `F:lean-kernel-accepts-the-non-prop-residue-of-the-constructed-real-carrier`, **open** |

Keeping `proved` is not the number-maximising choice, it is the accurate one:
the narrowed claim is strictly weaker, is what the suite re-derives today, and
carries two negative controls. Demoting it would assert we have no carrier-wide
independent replay, which is false; leaving the old text `proved` would assert
one we do not have. The status question is decided by which statement is on the
row, and the amendment ledger is what makes that visible.

## How the 48 are discoverable without reading any of this

- The suite prints all 73 by name with a typed reason, and asserts `untyped=0`
  plus that every `blocked-by-dependency` blocker is itself a
  not-a-proposition theorem.
- Evidence row 4 of the fact is anchored on
  `residue reason=theorem-type-not-prop name=CReal.weierstrassMTest`, so the
  class has a named representative in the ledger.
- The open residue fact names `CReal.rolle_interiorExtremum` and
  `CReal.mvt_interiorExtremum` — the two flagship results behind the boundary.
- ADR-0775 states the rule, the counts and the follow-on cost.

## Checker discrimination, both directions

Every corrected `checker_command` run VERBATIM through cargo against one real
run: rows 1, 2, 3, 4, 5 all exit **0**. The same row 4 with a fabricated name
(`CReal.weierstrassMTestX`) exits **1** — 1 match on the real name, 0 on the
fabricated one. Mutated-output variants also give 0: unequal counts, a count
below the floor, a changed reason token, and `untyped=4`.

## Does a crash read as absence? Measured, by reproducing it

The suite SIGABRTed for twelve days before reaching Lean. Reproducing that (the
prelude built on a `#[test]` thread's 2 MiB) and running the fact's corrected
`checker_command` unchanged:

    CHECKER_COMMAND_STATUS=101
      stack-overflow lines: 1     SIGABRT lines: 1
      toolchain banners:    0     lean-checked markers: 0
      REQUIRE_LEAN panics:  0

So **`AXEYUM_REQUIRE_LEAN=1` would NOT have caught it** — it fires only when a
toolchain cannot be resolved, and the abort happens before the probe is
reached. Every other guard was already fail-closed and none was wrong: the
checker's `out=$(...) &&` exits 101, and `check-lean-gate.sh` fails the suite
three ways (nonzero cargo status, `unnamed-toolchain`, `0-lean-checks`). **The
gap was running, not guarding.** Adding a fourth guard to the same unrun gate
would not have helped.

## Mutation kill sets, as measured

| mutation | tests killed |
|---|---|
| `is_a_proposition` always `true` | 3 — count/acceptance, superseded-claim refutation, typed residue |
| no `blocked-by-dependency` exclusion | 1 — count/acceptance only |
| Lean's count compared against the whole population (the superseded relation) | 1 — count/acceptance only |
| the refutation aimed at the FILTERED stream | 1 — superseded-claim refutation only |
| `on_a_deep_stack` removed (the historical crash) | all 4, and the `checker_command` exits 101 |

**One survivor, recorded rather than hidden.** The tamper control survived the
first mutation: with everything classified representable, Lean still refuses the
tampered `CReal.Equiv.not_zero_one` before it reaches any of the 48, so the pass
is honest but says nothing about the classifier. An assertion was added stating
what that control assumes — a kind refusal must never be read as a proof
refusal — and it did **not** change the outcome. The two guards fail on disjoint
defects.

Each mutation perturbs the SUBJECT rather than deleting an assertion that
currently holds; deleting an always-true assertion kills nothing by
construction and reports a survivor for the wrong reason. All of it ran in this
lane's own worktree.

## Registration

- `scripts/check-lean-gate.sh` counted floor 229 → 230: this suite goes from
  two real-Lean invocations to three.
- The classification lives in
  `crates/axeyum-lean-kernel/tests/support/creal_representability.rs`, so
  `real_lean_replay_census`'s equivalent copy can adopt it with a one-line
  `#[path]` change. Not done here — that file belongs to L0/S4's lane.
- `formal.kernel_theorem` pinned to `null` on the corrected fact: it is about a
  population, not one theorem, and the derived-dependency extractor otherwise
  reads the residue name out of a checker command and demands 40 `Rat.*` edges.

## Holdout isolation

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1110|settled=0|references=0|verdict=PASS

## What the next increment costs

1. **Close the residue** — export the `Type`-valued carriers as `def`s so Lean
   checks all 73, recovering `rolle_interiorExtremum` and
   `mvt_interiorExtremum`. It changes what `theorem` means on the wire, so it
   needs its own ADR plus ~1 day. When it lands,
   `the_superseded_whole_carrier_claim_is_refuted_by_the_same_binary` FAILS by
   design, and the parent fact is widened again.
2. **Audit the other carriers the same way.** This measured `creal` only.
   `nat`, `int`, `rat`, `complex` and `string` each need one prelude build and
   one Lean invocation to learn whether they carry a residue at all.
3. **Run the gate.** The only countermeasure that would have caught this
   twelve days earlier is `scripts/check-lean-gate.sh` being run, and it is
   already wired into `scripts/check.sh` and the justfile.

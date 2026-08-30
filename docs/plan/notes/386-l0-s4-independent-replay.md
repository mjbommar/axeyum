# Notes: 386-l0-s4-independent-replay

Detail moved out of [`../status/386-l0-s4-independent-replay.md`](../status/386-l0-s4-independent-replay.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**So `F:lean-kernel-accepts-the-whole-constructed-real-carrier` claims an
independent replay that is not currently re-derivable.** This lane touched no
fact's `epistemic_status`, `proof_route`, `axiom_footprint` or
`formal.statement`; the finding is reported for that fact's owner.

## How a sibling is prevented from inheriting a grade

`grade` is an exact membership test on the subject's own name against the set
Lean's kernel ended holding, read from `env.constants` via the new
`replay-lean4export.lean --emit-names`. Attested end to end: replaying the
closure of `CReal.ivt_step` **alone** (359 constants) grades `ivt_step`
replayed and `ivt_approx` — its own descendant, same family, same module,
reachable in one step — not-replayed.

## Mutation kill sets, as measured

| mutation | tests killed |
|---|---|
| `grade` prefix-matches instead of exact | 1 — pure guard only |
| `grade` always returns `Replayed` | 2 — both inheritance guards |
| `is_a_proposition` always `true` | 2 — census + earned typed reason |
| Lean reports zero constant names | 3 — every Lean-dependent test |

The first **survived** the Lean-attested guard: `CReal.ivt_approx` is not a
prefix of anything in `ivt_step`'s closure, so prefix matching is invisible end
to end. Recorded rather than hidden; the two guards fail on disjoint defects.

## Registration

- `real_lean_replay_census` added to `scripts/check-lean-gate.sh`'s suite
  table; its counted floor 223 → 229 for six real-Lean invocations.
- `check-lean-gate.sh` was already wired into `scripts/check.sh` and the
  justfile, so no new aggregate entry was needed.
- Monotone replay floor 1,900, 72 below the measurement. It may only rise.

## Holdout isolation

    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS

## What the next increment costs

1. **Decide the `Type`-valued carriers** (the natural follow-on). Exporting
   `UniformConvergesOn`/`HasDerivativeOn` theorems as `def`s would let Lean
   check all 73, recovering `rolle_interiorExtremum` and
   `mvt_interiorExtremum`. Needs an ADR — it changes what "theorem" means on
   the wire — plus ~1 day to implement and re-measure.
2. **Reconcile the carrier fact and suite** with finding 1. Small, and owned by
   that fact's lane, not this one.
3. **Extend the census beyond `creal`.** `nat`, `int`, `rat`, `complex` and
   `string` are each one more prelude build plus one Lean invocation on the
   same machinery — roughly 4 min of runtime each and a few hours of work.
   That is what moves the ledger-wide `independent_replay` figure off 8/2117;
   the 2,117 facts are not 2,117 exports, since one carrier replay grades
   every declaration in it by name.

# SMT-COMP credited full-population F2 integration preview

Status: bounded synthetic merge preview green; topic not integrated, exact
main CI red, and live F2 still prohibited

Date: 2026-07-24

Implementation result:
[F2 live-capture implementation](smtcomp-credited-full-preparation-f2-live-capture-implementation-2026-07-24.md)

## Objective and boundary

Test the exact audited F2 topic against current `origin/main` without mutating
the integration checkout or merging either branch. This closes the mechanical
and scoped semantic integration question only. It is not a merge, a full
post-merge `just check`, a green-main result, or authority to probe hosts, run
sentinels, create a NAS preparation, accept F2, or launch F3.

## Inputs and merge result

- main input: `08af3665e553aa1266e45aa46b6467f1ebc5551b`;
- topic input: `9cec37e4c7f7b3ccb7cae54e825f1c835f458f64`;
- `git merge-tree --write-tree origin/main HEAD` result:
  `f0a08d42997a1cb49906d20da51f5b1d3758eeb0`;
- local synthetic two-parent audit commit:
  `1e00159cda8d18201e5beff066f232344e70370a`; and
- merge conflicts: zero.

The synthetic commit is a disposable local audit object, not a pushed
authority. The two pushed input commits and the merge-tree command are the
replay recipe. The scratch worktree was detached, clean before the gates, and
remained clean afterward.

## Combined-tree gates

The following ran from the synthetic combined tree and exited zero:

```text
just check-scope origin/main
  45 focused tests and 44 subtests passed
  158 portable resume tests passed; one expected live-host test skipped
  runner 6/6; scoring 30/30; pipeline 6/6; selection 5/5;
  provenance 2/2; generated resume and selection authorities passed

just parity-docs
  all emitted unit, generated-contract, parity, and evidence checks passed
  final PARITY_DOCS line retained DISAGREE=0 on its registered populations

./scripts/check-links.sh
  all links ok
```

This evidence strengthens integration readiness for the F2-owned stack. It
does not replace a complete `just check` on the actual integrated main commit.
The corrected topic code through `b02c486b` already passed that full gate on
its own branch; the integration owner must still run the complete combined
gate after the real merge.

## Remaining mainline blockers

The audited topic is not an ancestor of main and has no pull request. Exact
main CI run `30122366840` remains red for two independent non-SMT-owned
failures:

1. Rust 1.97 reports `manual_assert_eq` at
   `crates/axeyum-verify/tests/protocol_fsm_examples.rs:115` and `:157`;
   commit `a4a041d2` allowed the different `manual_assert` lint.
2. Stable test `one_level_fixed_mbqi_retry_closes_seed_111` returns
   `Unknown(ResourceLimit)` after exhausting its MBQI instantiation budget.

The green synthetic scoped gates show that current main and the F2 stack
compose without a conflict or an F2-scoped regression. They do not make those
main failures disappear and cannot satisfy the exact-main authority check.

## Read-only stale-run observation

The separately existing s4 discovery stream remained active on all eight
historical shards. Latest indices were 6,853, 6,849, 7,470, 6,868, 6,912,
6,905, 7,565, and 6,831 (sum 56,253); literal `<<< WRONG` remained 56, no
`raw_*.json` shard existed, and the maximum observed sensor input was 86 C.
This run predates the soundness repairs and E1--E3. It receives zero
correctness, coverage, or measurement credit and is unrelated to F2 launch
authority.

## Exact next actions

1. The integration owner repairs both exact-main failures and establishes a
   green main commit.
2. The integration owner merges the current clean remote F2 topic, including
   this result, without dropping the R2 correction.
3. Run complete `just check` on the real integrated commit and require clean
   equality of local `HEAD`, local `origin/main`, and live remote main.
4. Only then build the exact release binary and separately authorize the C5
   no-launch capture with R1's repaired-P0 argument.
5. Verify the resulting `launch_authorized=false` root in a second process and
   integrate its exact result before any F3 acceptance or allocation.

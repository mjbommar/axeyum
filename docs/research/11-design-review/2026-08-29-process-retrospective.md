# Process retrospective, 2026-08-29 — what to add, remove, change

Status: IN PROGRESS (first commit records measurements before analysis).

## Measurements taken in this worktree (re-measured, not inherited)

Window: `git log --since="2026-08-28 00:00"` in this worktree after
`git merge --no-edit main`.

| quantity | measured | brief said |
| --- | --- | --- |
| commits | 622 | 342 |
| merges | 112 | 63 |
| distinct `Agent:` trailers | 126 | 68 |

The window is wider than the brief's, so the counts are larger; the RATIOS are
what matter and they agree: ~1 merge per 5.5 commits, ~5 commits per lane.

### The two hot files

| file | commits touching it | size |
| --- | --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` | 100 | 15,835 lines |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` | 100 | 4,788 lines |
| `PLAN.md` | 98 | generated |
| `crates/axeyum-lean-kernel/src/int_prelude/int_prelude_tests.rs` | 22 | |
| `crates/axeyum-lean-kernel/src/creal.rs` | 20 | 16,253 lines |
| `crates/axeyum-lean-kernel/src/creal/creal_tests.rs` | 16 | 11,109 lines |

`nat_prelude.rs` is touched **as often as** `nat_prelude_tests.rs` and the brief
did not name it. It has **667 `NameId` fields and 395 `declare_*` calls** — the
same shape the 2026-08-27 architecture review diagnosed in `creal.rs` (441
fields, 364 calls) as the reason phase-order bugs and helper duplication recur.

### Correction to the brief: the nat pin counter is already gone

`nat_prelude_tests.rs` has **no pinned array length**. `theorem_names` returns a
`Vec` with 557 entries and no `[T; N]` and no `assert_eq!(len, N)`.
`every_nat_declaration_is_checked_and_axiom_free` already derives coverage from
`k.environment()` in both directions. So the specific artefact the brief
proposes deleting was deleted already; what remains is the **shared append
point**, which is a different and larger problem — `creal` fixed it by sharding
into `creal/inventory/*.rs`, and `nat_prelude` never received that transplant.

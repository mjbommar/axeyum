# Frontier campaign — 2026-08-13

Shared workspace for the multi-agent run that follows the Rado session. Every
agent writes here; nothing here is authoritative until it lands in the axeyum
repository's claim ledger.

## Layout

```
coordinator/            this session's own diary and aggregation
agent-a-offdiag-schur/  generalized off-diagonal Schur numbers S(3;s,t,u)
agent-b-rado741/        R_4(5(x-y)=4z) = 741, the open frontier claim
agent-c-rado-akb2/      R_k(a(x-y)=bz) = a^k for gcd(a,b)=1, a >= b+2
  <agent>/DIARY.md      append-only work log: what was tried, what broke
  <agent>/FEEDBACK.md   roadmap feedback for axeyum itself
  <agent>/RESULT.md     the standing summary of what is established
  <agent>/logs/         raw run output
  <agent>/artifacts/    CNF, witnesses, DRAT proofs, cover ledgers
```

## Host assignment (do not poach another agent's host)

| host | cores | RAM | owner |
|---|---:|---:|---|
| s0 (server0, local) | 24 | 123 GiB (~73 free, loaded) | coordinator |
| s4 | 16 | 123 GiB (121 free) | agent-b |
| s5 | 16 | 27 GiB | agent-a |
| s6 | 16 | 26 GiB | agent-a |
| s7 | 16 | 26 GiB | agent-b (second) / agent-c |
| s1 | 4 | 61 GiB | agent-c |

## Rules that are not negotiable

1. **No external solver or checker in the trusted path.** ADR-0002. kissat,
   cryptominisat, z3, drat-trim are corroboration only and must be labelled as
   such wherever they appear.
2. **Both sides or it is not a value.** `n = N-1` SAT with the witness replayed
   by an enumerator that shares no code with the encoder, and `n = N` UNSAT
   with a checked proof. A conjectured formula is a prediction, not an answer.
3. **Measure, do not trust a message.** Exit 0 with zero tests run is the
   house failure mode. Confirm nonzero counts, confirm nonzero proof steps.
4. **Multi-agent hygiene.** Pathspec-only commits (`git add <paths>` then
   `git commit -m ... -- <paths>`). Never `cargo fmt` (use
   `rustfmt --edition 2024 <file>`). Never `git stash`, `checkout`, `restore`
   on files you do not own. Never overwrite a script a long-running job is
   executing.
5. **File ownership.** agent-a owns `crates/axeyum-search/src/family.rs` and any
   new module it adds. agent-b owns `harness.rs`, `cover.rs`, `certify.rs` and
   new example binaries. agent-c owns no shared source file; it adds uniquely
   named examples and new `artifacts/claims/` directories only. Anything else
   goes through the coordinator.
6. **Diary as you go.** Append to `DIARY.md` when something happens, not at the
   end. The order of discoveries is the useful part.
7. **Ownership is not isolation — build from your own snapshot, on disk.** The
   file-ownership map stops agents clobbering each other; it does nothing about
   the shared checkout having a single shared *compile* state. agent-c, which
   owns no shared source file at all, still could not build `axeyum-search`
   because agent-b was mid-edit in `cover.rs`. Take a `git archive HEAD`
   snapshot into your own scratch directory, build and run there, and touch the
   live worktree only to commit. (No `git worktree` — this project works on the
   default branch.) **Put that snapshot on disk, not in `/tmp`**: `/tmp` is a
   62 GiB *tmpfs*, i.e. RAM, shared by every lane. Tonight it produced an
   `EDQUOT` that cargo reported as a compiler error, three link steps killed
   with `ld terminated with signal 7 [Bus error]`, and a silent reduction in the
   memory a lane had scheduled a proof check against. Use `~/.cache/<lane>`.
8. **Commit by diff, never by copy.** Rule 7 gives isolation for *building* and
   says nothing about committing. Copying a whole file back from a snapshot
   discards whatever landed in the meantime: it silently reverted another
   lane's refactor tonight (repaired in `c33553e72`). Diff your snapshot
   against the live file and apply your change; never overwrite.
9. **Shared append points are not protected by pathspecs.** Pathspec discipline
   stops you sweeping files you did not touch. It does nothing when two lanes
   legitimately edit the same file — and the session protocol *tells* every lane
   to edit `PLAN.md`. The ADR index README is the same shape. Expect
   collisions there, re-read before appending, and keep the edit to one line.
10. **Tag your commits with your lane.** Every commit in this checkout carries
    the same git author, so lane attribution from `git log` is **not
    recoverable** — two separate lanes misattributed a commit tonight, and I
    repeated one of the errors. Add an `Agent: <lane-id>` trailer so the next
    person can tell who did what.

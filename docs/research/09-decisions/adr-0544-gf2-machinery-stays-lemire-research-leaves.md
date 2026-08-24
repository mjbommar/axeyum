# ADR-0544: The GF(2) Machinery Stays; The Lemire Research Record Leaves

Status: accepted
Date: 2026-08-23
Index-summary: Reusable binary-field machinery lands on main; the Kaser--Lemire attack, its data, and its narrative move to a paper repo and a long-lived branch.
Index-status: accepted

## Context

Two lanes attacked Kaser--Lemire half-degree irreducibles over GF(2) and
produced, between them, four artifacts:

| Artifact | Size | Content |
|---|---|---|
| `main`, 57 commits unpushed, **694 behind** origin | 160 files, 46,253 lines | signed-trace notes 00-21, 28 Python scripts, 3 facts |
| `agent/gf2/lemire-proof`, 295 commits off `cbc2bd69e` | 647 files, 1,308,358 lines | the gf2 CAS lane |
| `origin/agent/noh-p2-axeyum-examples` | 627 files | 21 `acb_*` + 2 `noh_*` examples |
| 40 untracked files in the gf2 worktree | 30,607 lines | present on **no branch**, local or remote |

Merging either lane whole would have imported roughly 1.3 M lines of
problem-specific narrative, ADRs, witness data, and conditional-implication
ledgers into a general automated-reasoning stack. Three facts made the choice:

**The lanes never collided with each other.** Only `PLAN.md` is touched by both,
and it is generated.

**Sixty ADR numbers double-allocated, invisibly.** The branch allocated
`adr-0484`--`0592` while `origin/main` independently allocated `0484`--`0543`,
so sixty numbers name different decisions on each side. `git merge-tree` reports
**no conflict** on any of them, because the filenames differ: `adr-0486` is
`auto-param-normalization-includes-checked-recursor-binder-domains` upstream and
`hayes-research-stays-cas-local` on the branch. Both would have landed side by
side, and the index would have rendered them as one sequence.

**`gf2_hayes.rs` is a leaf, not a spine.** At 26,655 lines and 266 public items
it is the largest single module in the crate, and it imports nothing from the
rest of it -- only `std`, `num-bigint`, `num-traits`, `serde`. The reverse
direction is nearly as empty: `gf2.rs`, `gf2_artifact.rs`, and `gf2_shard.rs`
reference it zero times, and `gf2_extension.rs` six times, all of them doc
comments or `#[cfg(test)]`. Its size is therefore not evidence that it is
load-bearing.

## Decision

Split by reusability, not by lane.

**Stays on `main`.** Six modules -- `gf2` (bit-packed binary polynomial
arithmetic, composition, Hankel characteristic), `gf2_extension`
(extension-field traces), `gf2_artifact` and `gf2_shard` (sharded computation
with SHA-256-bound canonical-JSON evidence), `gf2_independent` (independent
certificate re-validation), `gf2_search` -- plus the seven binaries that do not
reach `gf2_hayes`, the `certificate-spec` fact language, and the pre-push
caller-safety assertion.

**Moves to `../lemire-half-degree-irreducibles`.** The narrative (22 signed-trace
notes, the AC-bridge, NoH-p2 and blocker-sweep packets), 109 ADRs, 41 facts,
28 MB of witness data across 408 files, the standalone Python, and the
problem-specific checkers.

**Stays on `agent/gf2/lemire-proof`, kept alive.** `gf2_hayes.rs` itself, its ten
binaries, and the tests that cross-check against it. The module still compiles
there.

Which facts stay was decided **mechanically, not editorially**: a fact stays if
and only if every `evidence.artifact` it cites resolves under a path that stays,
and no checker command reaches `gf2_hayes` or `artifacts/gf2`. Exactly four
qualify -- three `proved`, one `refuted` -- and their `depends_on` edges are
closed within that set. The other 41 cite data or checkers that left, so keeping
them would have left the ledger asserting evidence this repository can no longer
produce.

This reverses ADR-0486 (`hayes-research-stays-cas-local`), which is superseded
rather than withdrawn: its reasoning was sound while the attack was live work.

## Consequences

The `axeyum-cas` crate gains ~6,600 lines that no longer mention Lemire. All 694
`axeyum-cas` tests pass, clippy is clean under `-D warnings`, and each of the
four retained facts' declared checker commands runs a nonzero, passing test
count. `python3 scripts/validate-facts.py` reports 347 facts, 0 errors.

Three couplings had to be cut, and one of them was not visible to the obvious
search. Grepping for `gf2_hayes` finds the module-path references but **not**
`tests/gf2_artifact_cli.rs`, which reaches the module through a *binary name* --
`env!("CARGO_BIN_EXE_axeyum-gf2-hayes-conditional-variance")`. That test
compiled fine and failed only at link time, after the grep had already reported
the file clean. When cutting a module out of a crate, the coupling surface is
module paths **and** `CARGO_BIN_EXE_*` names **and** `Cargo.toml` target
declarations; a clean grep over the first is not evidence about the other two.

Two removed cross-checks are recoverable rather than lost, and are marked as such
in place: `gf2_extension`'s two Hayes-moment tests return if
`class_population_distribution` and the Sawin Euler report are lifted out, and
the `conditional_variance` CLI case returns with its binary.

The 109 exported ADRs keep their original filenames in the paper repo, so their
numbers remain ambiguous outside this repository. That is recorded in that
repo's `research/PROVENANCE.md`; the numbers are not authoritative there and the
sequence here is unaffected.

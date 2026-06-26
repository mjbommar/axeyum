# Phase-2 build goal — A / B / C

Paste the block below into `/goal` to drive the Phase-2 buildout of the three
consumer-track apps (`axeyum-evm`, `axeyum-property`, `axeyum-verify`) from their
landed Phase-1 MVPs toward clean, functional, state-of-the-art tools. It encodes
the worktree workflow, per-app next moves, the gates, and the coordination
guardrails so execution needs no re-derivation.

---

```markdown
Advance the three consumer-track apps from Phase-1 MVPs toward clean, functional,
state-of-the-art tools, working backwards from "a real user runs it on real input
and trusts the result." Be careful, comprehensive, consistent, patient.

## Apps (read docs/consumer-track/<app>/{PLAN,STATUS}.md first — STATUS lists the exact next actions)
- **B — axeyum-property** (SDK; build first, A/C reuse it): `#[derive(Symbolic)]` +
  `Bounded<T,LO,HI>`; the **counterexample → runnable `#[test]`** layer (shared with A/C);
  fixed arrays/slices; widen Lean-cert coverage; grow the scoreboard corpus.
- **A — axeyum-evm**: symbolic-offset memory + per-mapping storage decomposition;
  keccak-injectivity constraints; tie `SafeUpToBound` to the real reachability refutation;
  more opcodes; richer real-contract examples.
- **C — axeyum-verify**: parse array params/indexing; `usize`/`isize` widths; CFG/BMC for
  unbounded loops; surface Lean-cert coverage as the headline metric.

## How to work
- Worktree only: /home/mjbommar/projects/personal/axeyum-consumer (branch `consumer-track`,
  already on origin). Drive each app with **opus sub-agents + task lists**; **one build agent
  at a time** per worktree (git-index race). Regenerate the scoreboard each round.

## Discipline (hard)
- Gate every increment: `cargo fmt` + `clippy --all-targets -- -D warnings` (pedantic) + tests,
  via `CARGO_BUILD_JOBS=4 ./scripts/mem-run.sh … -j4`. `#![forbid(unsafe_code)]`.
- **DISAGREE = 0 is the soundness floor**: every bug revalidated (concrete re-run), every
  "proved/safe" certified, honest `Unknown` — never a wrong verdict. The scoreboard binary
  panics on DISAGREE ≠ 0.
- Commit sound increments on `consumer-track`; keep each STATUS.md current.

## Guardrails (do not step on the solver agent)
- **New crates + new files only**; consume axeyum-solver/ir as a black box; never edit the
  core crates or the main tree; root `Cargo.toml` additively only.
- Capability gaps → file as **notes** in the app's STATUS.md (never core reach-ins).
- Build caps (`-j4` + `mem-run`); if disk fills, reclaim only **inactive**-worktree `target/`
  caches (never the locked/active one or the main tree).
- **Do not merge to `main`** until main is clean/committed; the branch lives on origin.

## Optional (when tooling/network allows)
Install hevm/halmos (A) and Kani (C) to fill the install-gated vs-SOTA scoreboards; otherwise
keep them honestly deferred, not faked.
```

---

**Notes**
- **B first**: its `#[derive(Symbolic)]` and the shared **counterexample→`#[test]`** layer are
  reused by A and C, so building it first avoids rework. Reorder to lead with the EVM flagship
  if preferred.
- Phase-1 status / per-app next actions live in each `docs/consumer-track/<app>/STATUS.md`;
  the track charter + decision rationale are in `README.md` and `03-decision.md`.

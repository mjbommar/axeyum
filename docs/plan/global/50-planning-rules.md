## Planning rules

- **One mutable tracker.** `PLAN.md`, generated from `docs/plan/global/` and
  active lane files. `STATUS.md` is a pointer; no root `TODO.md`; no other
  document may claim project-wide priority.
- **Dated notes are evidence, not queue.** A note under `docs/plan/` (stock-takes,
  gap logs, "what to build", improvement lists, roadmaps) records what was
  measured and proposed on its date. Anything still open from it is either an
  item here or not scheduled.
- **Labels.** Items are `SOL-n`, `LIB-n`, `EVD-n`, `CON-n`, `ENG-n`. Older
  labels (A1–A13, L0–L4, S1–S12, C/D/G phases, MOS-, W-, chair "Next Ten") are
  historical; resolve them through [`docs/plan/CATALOG.md`](../CATALOG.md) and the archive.
- **Lane lifecycle.** A lane file exists only while its item is active. On
  `DONE` it moves to `docs/plan/archive/lanes/`; at most ~25 are active.
- **Evidence outranks prose.** Benchmark TSV/JSON, generated matrices, test
  output, Git objects and remote refs decide status; correct prose that disagrees.
- **Wrong verdicts preempt everything (P0):** a wrong sat/unsat, a crash, data
  loss, or a gate that cannot fail is reproduced, root-caused, regressed and
  repaired before any breadth or performance item.
- **No false green.** A focused pass is not a full gate; a running job is not a
  pass; a local commit is not integration; a pinned-list gain alone ships nothing
  (the ship criterion is 0 stable losses, 0 flips, ≥ 1 stable gain on pinned
  and held-out).
- **No journal growth.** Global sections carry state, order and exits; detail
  goes in a dated note or artifact. `scripts/check-plan-authority.py` caps
  `global/` at 32,000 bytes and each lane file at 3,000.
- **Decisions require ADRs** for public operators, rewrites, encodings,
  backends, evidence artifacts, logic fragments, and priority-changing
  architecture.
- **Determinism and replay are promises:** stable order, explicit seeds and
  limits, original-term SAT replay, independent UNSAT checking.
- **Graph rank is advisory.** Degree, centrality and cost estimates never bypass
  fact-frontier legality, held-out isolation, or the theorem-credit contract.
- **Proof data does not leak into autonomous discovery:** proof/value edges may
  sequence work but are excluded from producer inputs and autonomous credit.

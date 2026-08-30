## Planning rules

- **One mutable project tracker:** update this file only. Root `STATUS.md` is a
  pointer; do not create root `TODO.md`; subsidiary `STATUS.md` files may retain
  local historical evidence but may not claim project-wide priority.
- **Evidence outranks prose:** benchmark JSON/TSV, generated matrices, test
  output, Git objects, remote refs, and CI results determine status. Correct this
  file when they disagree.
- **Wrong verdicts preempt everything:** reproduce, root-cause, regress, and
  repair before breadth or performance work.
- **No false green:** a focused pass is not a full gate; a running job is not a
  pass; a process-free readiness artifact is not launch authorization; a
  local commit is not integration.
- **No journal growth:** result detail belongs in a dated note under
  `docs/plan/` or a committed benchmark artifact. Keep only the current state,
  ordered queue, and a short recent-change table here.
- **Decisions require ADRs:** public operators, rewrites, encodings, backends,
  evidence artifacts, logic fragments, or priority-changing architecture need
  the applicable research question and ADR resolved first.
- **Determinism and replay are product promises:** stable order, explicit seeds
  and limits, original-term SAT replay, and independent UNSAT checking remain
  mandatory.
- **Graph rank is advisory until its authority is complete:** module degree,
  declaration centrality, curriculum mapping, and cost estimates remain visible
  components. They never bypass fact-frontier legality, held-out isolation,
  representability, or the theorem-credit safety contract.
- **Proof data does not leak into autonomous discovery:** upstream proof/value
  dependency edges may measure and sequence work but are physically excluded
  from proof-isolated producer inputs and autonomous credit.
- **Three parallel library lanes have different jobs:** prefer one shared
  substrate/definition lane, one reusable producer lane, and one destination
  theorem/evaluation lane. Each owns disjoint status, script, artifact, and test
  paths; one generated writer owns every aggregate key.

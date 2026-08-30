# Engineering plan and evidence index

This directory contains detailed phase contracts, preregistrations, retained
results, handoffs, generated reports, and long-horizon plans. It is the durable
engineering record, not the live task tracker.

Start with these documents:

1. [Root `PLAN.md`](../../PLAN.md) — the only mutable session status, ordered
   queue, stop conditions, and resume protocol. It is **generated**: edit your
   lane's file in [`status/`](status/README.md) or a project-wide section in
   [`global/`](global/README.md), then run `python3 scripts/gen-plan.py`.
2. [Project State](../PROJECT-STATE.md) — the short public account of what is
   built, measured, partial, and not claimed.
3. [Research roadmap](../research/08-planning/roadmap.md) — phase definitions
   and exit criteria.
4. [Foundational dependency DAG](../research/08-planning/foundational-dag.md) —
   obligations that precede new public surface.

Do not infer current priority from a dated file in this directory. A plan or
preregistration records what was authorized at that time; a result records what
was observed; neither overrides root `PLAN.md`.

## Find the right record

| Need | Start here |
|---|---|
| Current status or next action | [Root `PLAN.md`](../../PLAN.md) |
| Solver capability and assurance | [Capability matrix](../research/08-planning/capability-matrix.md) |
| Parser, IR, solver, and proof support | [Support matrix](../research/08-planning/support-matrix.md) |
| Trusted and independently checked boundaries | [Trust ledger](../research/08-planning/trust-ledger.md) |
| Benchmark and parity results | [`bench-results/`](../../bench-results/README.md) |
| Accepted architecture decisions | [ADR index](../research/09-decisions/README.md) |
| Full-library SMT-COMP workflow | [SMT-COMP workstream](smtcomp-full-library-workstream/README.md) |
| Parallel lane briefs and ownership | [Agent program](agent-program-2026-07-28/README.md) |
| Lean implementation program | [Lean system implementation plan](lean-system-implementation-plan-2026-07-21.md) |
| Graph-directed library programme | [Graph roadmap](graph-directed-library-roadmap-2026-08-30.md) and [ADR-0717](../research/09-decisions/adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md) |
| Lean artifact compatibility | [Artifact compatibility roadmap](library-artifact-compatibility-roadmap-2026-08-30.md) |
| Universal theorem safety | [Trusted library safety roadmap](trusted-library-safety-roadmap-2026-08-30.md) |
| Definition and proof discovery | [Discovery efficiency roadmap](definition-discovery-efficiency-roadmap-2026-08-30.md) |
| Paused CAS work | [CAS parity handoff](cas-parity-handoff-2026-07-22.md) |
| Proposed strategy exploration | [Exploration track](exploration-track/README.md) |

## Structured plan sets

- [North star](00-north-star.md) and [cross-track dependency DAG](01-dependency-dag.md)
  define the long-horizon target and sequencing constraints.
- [Engine and performance](track-1-engine/README.md) covers the search core,
  incremental solving, and performance architecture.
- [Theories and breadth](track-2-theories/README.md) covers arithmetic, arrays,
  quantifiers, strings, floating point, and theory combination.
- [Proofs and Lean](track-3-proof-lean/README.md) covers certificates,
  reconstruction, kernel checking, and Lean compatibility.
- [Use cases and front ends](track-4-usecases-frontend/README.md) covers
  SMT-LIB, benchmarks, APIs, and consumer scenarios.
- [Verified systems](track-5-verified-systems/README.md) covers IR reflection
  and checked program-verification applications.
- [Reference implementations](references/README.md) records the external solver
  and checker designs used by those tracks.

The [exploration track](exploration-track/README.md) is a proposal and remains
ADR- and measurement-gated. Its local `STATUS.md` is a compatibility pointer;
root `PLAN.md` controls whether the track may run.

The accepted library-construction programme is deliberately split across four
documents because its lanes have different authorities: external artifact
extraction, graph selection, theorem-credit safety, and untrusted discovery.
Their ordering and current priority live only in generated root `PLAN.md`.

## Evidence families

Top-level dated files are intentionally append-only research records. Common
families include:

- arithmetic frontier work (`arithmetic-*`, `qf-nia-*`, `qf-uflia-*`,
  `qf-linear-*`);
- SMT-COMP selection, readiness, execution, and replay (`smtcomp-*`);
- Lean import, kernel, official-suite, and parity work (`lean-*`, `lean4-*`);
- floating-point and string measurements (`fp-*`, `strings-*`);
- measurement, provenance, proof-gap, and API contracts.

Use repository search instead of relying on directory order. For example:

```sh
rg --files docs/plan | rg 'qf-nia|qf-uflia'
rg --files docs/plan | rg 'preregistration|result|handoff'
rg -n 'ADR-0359|QF_UFLIA' docs/plan docs/research
```

Names normally encode the subject, milestone or revision, record type, and
date. Read an experiment's preregistration or plan together with its result;
later amendments and results supersede operational instructions but do not
rewrite the earlier record.

## Generated and retained artifacts

- [`generated/`](generated/) contains rendered reports derived from checked
  machine-readable sources. Regenerate them with the owning script; do not edit
  them by hand.
- [`evidence/`](evidence/) contains retained evidence inputs and manifests.
- [`fixtures/`](fixtures/) contains bounded test and measurement fixtures.

The source file or generator header is authoritative when a generated report
names one. The documentation gates verify many of these relationships; a clean
render alone is not evidence that an experiment ran.

## Record conventions

- Use `plan` or `preregistration` for authorization before observing target
  outcomes, `result` for retained observations, and `handoff` for a deterministic
  restart surface.
- Bind execution evidence to immutable commits, inputs, configurations, and
  artifacts. Keep local tests, committed state, remote integration, and hosted
  CI as separate evidence states.
- Record rejected and zero-gain experiments. Do not silently turn them into a
  new current policy.
- Put live status only in root [`PLAN.md`](../../PLAN.md); put durable detail in
  a dated file here and link it from the live plan.
- Public operators, rewrites, encodings, backends, evidence formats, logic
  fragments, or priority-changing architecture require an ADR.

The governing principle is **untrusted fast search, trusted small checking**:
search and tuning may be experimental, but accepted verdicts and public claims
must name their replay, certificate, checker, or explicit trust boundary.

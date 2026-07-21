# Agentic binary-security positioning

Status: current related-work guardrail
Date: 2026-07-21

## Purpose

Position Axeyum + Glaurung against two contemporary agentic vulnerability
research systems without treating unlike evaluation surfaces as solver
baselines. The comparison is architectural: where semantic evidence comes
from, what an agent is allowed to infer, and how a claim is checked.

## The neighboring systems

### Veritas

[Veritas](https://arxiv.org/abs/2605.15097) studies out-of-bounds reasoning over
stripped binaries. Its three stages are a deterministic static Slicer that
recovers witness-backed source-to-sink flows from lifted LLVM IR, an LLM
Discover stage that aligns decompiled and IR views, and a multi-agent Validator
that uses debugging and runtime oracles. Its reported evaluation is 20 samples
from 10 projects, 90% recall, no false positives among 623 exhaustively
validated candidates, and two observed false positives in sampled audits.

The closest conceptual agreement is the rejection of unconstrained agent
inference. Veritas statically materializes the propagation evidence that the
agent must carry and then grounds the claim in execution. Axeyum + Glaurung
materializes typed path obligations, checks solver results against the original
term, and keeps evidence/checking separate from heuristic search.

The systems are complementary rather than interchangeable. Veritas currently
specializes a stripped-binary source-to-sink and runtime-validation pipeline to
out-of-bounds bugs. Axeyum is a reusable reasoning/checking substrate, while
Glaurung supplies binary semantics, exploration, sink policy, and report
construction. The Axeyum/Glaurung paper must not compare solver latency against
Veritas's end-to-end agent/runtime cost or imply Veritas's 20-sample recall is a
QF_BV solver result.

### Microsoft codename MDASH

Microsoft describes [codename
MDASH](https://www.microsoft.com/en-us/security/blog/2026/05/12/defense-at-ai-speed-microsofts-new-multi-model-agentic-security-system-tops-leading-industry-benchmark/)
as a source-oriented vulnerability discovery and remediation pipeline with
prepare, scan, validate/debate, deduplicate, and prove stages. It orchestrates
more than 100 specialized agents and domain plugins. Microsoft reports 21/21
planted bugs with zero false positives on a private driver, 96% retrospective
recall on 28 `clfs.sys` cases, 100% on seven `tcpip.sys` cases, and 88.45% on
CyberGym; the system is used internally and offered through a limited private
preview.

MDASH is evidence that the surrounding system—not one model—is the relevant
unit of agentic security engineering. That supports Glaurung's deterministic
analysis backbone and role-specific tooling, but it is not reproducible solver
evidence for Axeyum. Its reported source/private-code populations, dynamic prove
plugins, and agent ensemble differ from Glaurung's current binary workloads and
from Axeyum's fixed query streams. Cite the reported numbers as vendor evidence
with their denominators and provenance; do not use them as direct recall,
precision, or performance baselines.

## Comparison boundary

| Axis | Veritas | MDASH | Axeyum + Glaurung |
|---|---|---|---|
| Primary surface | Stripped binaries lifted to LLVM IR plus decompiled/runtime views | Source repositories, historical context, domain plugins, and dynamic proving | Binary frontend and exploration in Glaurung; typed reasoning obligations in Axeyum |
| Search/reasoning | Witness slices constrain LLM claim construction | Specialized auditor, debater, and prover agents | Heuristic exploration may be untrusted; solver terms, replay, and evidence routes are explicit |
| Claim check | Debugger-guided execution and runtime oracles | Debate plus triggering/prove plugins | Original-term model replay, independent certificate checks, kernel/DRAT routes, and source-backed downstream controls |
| Current measured scope | OOB-focused curated stripped-binary benchmark | Vendor-reported private/public source benchmarks and production findings | Bounded multi-oracle solver populations, named Glaurung drivers, selected-pair recall, and one downstream proof-consumption cell |
| Defensible claim | Semantically grounded agentic binary vulnerability reasoning | Production-scale multi-agent vulnerability discovery system | Reusable typed/checkable reasoning substrate plus a measured binary-analysis integration |

## Attacker control is not one bit

Every finding and related-work comparison must keep these predicates separate:

1. **Provenance:** a value or memory content is derived from an external input.
2. **Region ownership:** an address denotes a caller-, kernel-, stack-, heap-, or
   otherwise classified memory region.
3. **Selection:** the analysis or attacker can choose a concrete value/address;
   Glaurung's `ConcretizationPolicy` changes deterministic value selection, not
   provenance or the memory model.
4. **Reachability:** the path conditions that reach the sink are satisfiable
   under the modeled environment.
5. **Violation:** the reached operation actually violates a bound, lifetime,
   privilege, or other security condition.
6. **Exploitability:** deployment preconditions and a usable security primitive
   exist; this normally needs evidence beyond a satisfiable path.

This separation is already encoded by the corrected Glaurung evidence line:
[ADR-0240](../09-decisions/adr-0240-corrected-taint-provenance-finding-baseline.md)
rejects generic-argument attacker-control assumptions,
[ADR-0242](../09-decisions/adr-0242-correct-wdm-systembuffer-finding-baseline.md)
separates `SystemBuffer` address ownership from attacker-controlled contents,
and
[ADR-0246](../09-decisions/adr-0246-model-independent-glaurung-stack-region-classification.md)
separates model-independent region classification from value choice. The
completed concretization sweep is reproducibility infrastructure; it is not a
taint analysis, memory model, vulnerability oracle, or exploitability proof.

## Paper claims and non-claims

Lead with the shared methodological principle: agentic search becomes credible
when safety-deciding semantics are materialized and checked outside the model.
Then state Axeyum's distinct contribution precisely:

- strict typed construction exposed real consumer translation bugs that a
  permissive native adapter masked;
- well-typed multi-oracle fuzzing, deterministic original-term replay, and
  checked proof/evidence routes turn that strictness into a standing method;
- the Glaurung integration measures how a reusable reasoning substrate behaves
  inside one real binary-analysis system, including divergent models,
  fallbacks, Unknown, resource limits, memory, and dropped work.

Do not claim general agentic vulnerability-detection superiority, Veritas-level
OOB recall, MDASH-scale production recall, or solver performance leadership.
The fair six-cell result rules out the last claim; current recall remains the
explicitly selected and source-backed population recorded in the PLAN.

## Placement in the manuscript

- **Related work:** use the comparison table and the semantic-grounding
  agreement/difference, not a feature checklist.
- **Methods:** define the six attacker-control predicates before presenting
  finding parity or recall.
- **Evaluation:** keep Veritas and MDASH numbers in related work. Solver timing
  tables contain only topology-equivalent solver cells; vulnerability tables
  retain their own denominators and authority policy.
- **Discussion:** identify a future composition point: Glaurung/Axeyum evidence
  could serve as one deterministic witness/checking plugin inside an agentic
  pipeline, while runtime validation remains a separate trust layer.

## Sources

- Zheng et al., [*Veritas: Grounding LLM Agents for Reliable Vulnerability
  Reasoning over Stripped Binaries*](https://arxiv.org/abs/2605.15097), v2,
  2026-07-06.
- Microsoft Security, [*Defense at AI speed: Microsoft's new multi-model
  agentic security system tops leading industry
  benchmark*](https://www.microsoft.com/en-us/security/blog/2026/05/12/defense-at-ai-speed-microsofts-new-multi-model-agentic-security-system-tops-leading-industry-benchmark/),
  2026-05-12.

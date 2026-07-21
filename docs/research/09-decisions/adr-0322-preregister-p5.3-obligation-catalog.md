# ADR-0322: Preregister the P5.3 obligation catalog

Status: accepted
Date: 2026-07-21

## Context

ADR-0321 closes bounded deterministic scalar T5.3.3 v1. P5.3 now has at least
one positive and one discriminating negative example in each planned obligation
family:

- T5.3.1 compares reflected MIR branch decisions under self-composition;
- T5.3.2 proves bounded memory/page-table-shaped properties from authenticated
  owning-build MIR; and
- T5.3.3 proves identity refinement and transports safety from a declarative
  handshake FSM to an authenticated reflected Rust step.

The sole remaining phase task, T5.3.4, is documentation: one page per family
with the exact goal shape, supported fragment, evidence route, and a worked
example. Existing planning and scoreboard prose predates the last two results
and can make the families look more uniform or general than the evidence
supports. In particular, T5.3.1 is control-flow leakage over committed MIR text,
not authenticated source capture or hardware timing; T5.3.2 is a four-byte
teaching model, not an MMU; and T5.3.3 is one finite identity relation, not a
general protocol-refinement framework.

## Decision

Create `docs/plan/track-5-verified-systems/obligations/` with an index and
exactly three family pages:

1. `control-flow-constant-time.md`;
2. `bounded-memory-and-page-table-math.md`; and
3. `fsm-refinement.md`.

The index answers “what can it prove?” with a compact comparison matrix. Each
family page independently states the mathematical obligation, accepted input
fragment, evidence and trust route, exact worked example, reproduction command,
measured observation, successful negative control, and explicit non-claims.
The Track 5 README and the primary Verify capability scoreboard link to the
catalog. The systems/protocols scoreboard may link the relevant family pages,
but its historical measurements are not rewritten as current results.

## Frozen documentation gates

1. Commit this zero-page ADR before creating the catalog directory or measuring
   a catalog-specific reproduction. Existing accepted evidence may be audited
   to define the schema, but no catalog completion result is claimed yet.
2. The catalog path set is exactly one `README.md` index plus the three family
   pages named above. One page per family means separate linkable artifacts,
   not three headings hidden in one long document.
3. Every family page contains these explicit sections: `Claim`, `Goal shape`,
   `Supported fragment`, `Evidence route`, `Worked example`, `Reproduce`, and
   `Boundaries and residuals`. A reader can identify the quantified variables,
   property, success verdict, counterexample route, and unsupported dimensions
   without reading implementation code.
4. The index matrix distinguishes at least: source form, authenticity level,
   proof scope, positive result, negative control, and principal residual. It
   never rolls the three rows into “kernel verification,” “constant-time,” or
   “protocol correctness” without the row-local qualifier.
5. The pages derive claims only from accepted committed evidence: T5.3.1
   `constant_time.rs` and commit `ac7494f0`; ADR-0320 plus its authenticated
   artifact; and ADR-0321 plus its authenticated artifact. Proposed work,
   hand-built predecessor examples, and historical scoreboard rows are labeled
   separately or omitted.
6. T5.3.1 says `control-flow constant-time` or `branch-decision
   noninterference`, records that its MIR is committed fixture text, and lists
   memory-index leakage, LLVM-side leakage, compiler-capture authentication,
   value/timing/cache behavior, and broader input shapes as residuals. Its
   worked example preserves the distinction between a public-predicated branch
   with secret-dependent output and a secret-predicated branch witness.
7. T5.3.2 reports the exact four-entry byte-table model, seven universal claims,
   three replayed controls, 4,096-row sampler, authenticated 8,218-byte module,
   and accepted timings. It repeats the ADR-0320 MMU/address-translation and
   systems-effect exclusions.
8. T5.3.3 reports the exact BV8 state, four-event alphabet, identity relation,
   eight universal per-event groups, complete relation equality, two PDR-safe
   systems, replayed blind-injection control, 2,048-row sampler, authenticated
   2,691-byte module, and accepted timings. It excludes off-alphabet inputs,
   liveness, fairness, concurrency, TCP, real networking, richer simulation,
   and a public reusable refinement API.
9. Reproduction commands are memory-safe and scoped. Run the existing focused
   suites with one Cargo job and one test thread under the 4 GiB cgroup. Record
   one fresh T5.3.1 focused wall observation; quote ADR-0320/0321 frozen timings
   as recorded evidence rather than silently replacing them with a new host
   sample.
10. Links from `docs/plan/track-5-verified-systems/README.md` and
    `docs/consumer-track/verify/SCOREBOARD.md` resolve to the catalog index.
    Update P5.3, PLAN, STATUS, the ADR index, and the relevant research question
    only after every page and link gate passes.
11. No Rust code, artifact bytes, solver/reflection semantics, public API,
    dependency, feature, unsafe policy, MSRV, WASM surface, benchmark result, or
    existing scoreboard datum changes. Scoped formatting, docs link checking,
    `git diff --check`, and the one-job/OOM audit are the acceptance gates.

No required section, qualifier, residual, or link may be removed after the
first catalog page or focused timing observation. A failed gate leaves ADR-0322
proposed and records the missing documentation explicitly.

## Result

Accepted. The catalog contains exactly one comparison index and three separate
family pages at the frozen paths. Every family page has all seven required
sections and identifies its quantified goal, admitted fragment, positive
verdict, counterexample route, reproduction command, evidence provenance, and
unsupported dimensions. The index compares source form, authenticity, proof
scope, positive result, negative control, and principal residual without
collapsing the rows into an unqualified systems-verification claim.

The control-flow page truthfully records committed MIR fixture text rather than
owning-build authentication and distinguishes branch-decision noninterference
from output noninterference and hardware timing. Its fresh memory-capped
reproduction passes four of four tests in 0.10 seconds wall time with 53,604
KiB peak RSS on a cached build. The bounded-memory and FSM pages retain the
accepted ADR-0320/0321 artifact identities, universal proof counts, negative
controls, exact sampler populations, and recorded timings rather than replacing
them with new host measurements. Their focused reproduction suites pass six of
six tests each under the 4 GiB cap.

The Track 5 README and primary Verify scoreboard link to the catalog index.
All relative links, required-section checks, `git diff --check`, and the kernel-
journal OOM audit pass. No Rust code, artifact byte, semantics, API, dependency,
feature, benchmark row, or historical scoreboard datum changed. T5.3.4 and the
bounded P5.3 v1 phase are complete; every family page's named residuals remain
open and require their own future evidence decisions.

## Rejected alternatives

- **One combined narrative page.** Rejected: independent family pages are the
  T5.3.4 exit criterion and make bounded claims directly linkable.
- **Promote every row to authenticated compiler evidence.** Rejected: T5.3.1's
  current fixture provenance is materially weaker and must remain visible.
- **Refresh all historical scoreboard timings.** Rejected: that is a separate
  benchmark protocol and would mix documentation synthesis with new performance
  claims.
- **Close the listed residuals while writing the catalog.** Rejected: T5.3.4 is
  a documentation task, not authorization for new semantics or research cells.

## Consequences

- A positive result completes T5.3.4 and the documented P5.3 v1 phase exit,
  while leaving every page's residual work open.
- The catalog becomes the reviewer-facing claim boundary for future Track 5
  extensions; a later result updates the relevant family page without erasing
  the earlier evidence level.

## References

- `docs/plan/track-5-verified-systems/P5.3-kernel-theories.md`.
- `crates/axeyum-verify/tests/constant_time.rs`.
- ADR-0320 and ADR-0321.
- `docs/consumer-track/verify/SCOREBOARD.md`.

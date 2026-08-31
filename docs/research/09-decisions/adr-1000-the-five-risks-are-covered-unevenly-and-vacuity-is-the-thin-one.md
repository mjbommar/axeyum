# ADR-1000: The five risks are covered unevenly; contamination is strong, vacuity is 8 facts, and independent replay is mismeasured in both directions

Status: accepted
Date: 2026-08-31
Index-summary: Audited ADR-0717's five risks against every L0 gate. Contamination
reaches ~1,956 facts through S2 with 15 mutation-verified guards, but 548 of
those subjects (28%) are chosen by the `theorem_of` regex the tree documents as
unreliable. Vacuity reaches 8 facts of 2,167, all one topic. `independent_replay`
at 7 misses all 9 checked-interchange roots (which read `no`) and includes one
crediting an argument-less gate. 434 facts hold exactly one protection and it is
a prelude-wide sweep; 105 hold none. No L0 gate runs in CI or pre-push.

Phase: audit of L0 (S0-S6) against ADR-0717's threat model
Lane: `five-risk-coverage-audit`

## Context

ADR-0717's roadmap names five risks that kernel acceptance alone leaves open —
kernel unsoundness, statement error, vacuity, contamination, false evidence —
and states that an empty axiom footprint addresses only part of two of them.
L0's seven phases are complete. Nobody had gone back and said, per risk, what
is now covered.

ADR-0795 had already established that the S0 census measures **per-fact
evidence** and that much real protection is **centrally enforced**, correcting
`circularity` (38 → 14 against a central 1,956) and marking
`semantic_falsification` as an upper bound (96 named, 8 demonstrated). It found
that only one gate published a per-fact set.

The full audit, with every measurement and every command, is in
[`docs/research/11-design-review/2026-08-31-five-risk-coverage-audit.md`](../11-design-review/2026-08-31-five-risk-coverage-audit.md).
This ADR records only what should bind future work.

## Decision

**1. Vacuity is the binding gap and is stated as 8 of 2,167, not as 100.**
S3's demonstrated load-bearing set is 8 facts, all `Nat.totient`
multiplicativity or the CRT counting argument underneath it. Unlike
contamination — which reads 14 per-fact and is actually 1,956 centrally — there
is no central gate covering the rest. Any claim about non-vacuity quotes 8, or
quotes the family it covers, and never the `semantic_falsification` column.

**2. `independent_replay` is wrong in both directions and neither number is
quotable until the join is published.** The 7 facts it credits are disjoint
from the 9 roots of
`artifacts/checked-interchange/census/credited-roots-v1.census.json` — the only
facts carrying a published per-fact, name-**and**-type, real-pinned-Lean-admitted
grade — every one of which reads `independent_replay: no`. The 7 also include
`F:schedule-critical-chain-infeasible`, crediting replay from
`scripts/check-lean-gate.sh` invoked with no arguments.

Lean's kernel really admitted ~1,972 declarations, and roughly 1,688 settled
facts name declarations in that population — but that is a **prefix proxy**
computed from carrier families, because the replayed name list and the 73-name
non-representable residue are never committed. So the coverage exists and is
unverifiable per fact.

**3. A regex chooses 28% of the contamination population's subjects, and that
is a population-level instance of the checker-that-cannot-fail defect.**
Replicating `subject_of` over today's ledger: 1,300 facts bind through
`formal.kernel_theorem`, 152 through a single `evidence[].kernel_declaration`,
**548 through the `theorem_of` regex**, 87 unresolved, of 2,087 kernel-route
settled facts. `theorem_of`'s own docstring says the extraction is
"demonstrably NOT reliable in general" and records it picking `Int.sub` instead
of `Int.fib_cassini`. When it picks wrongly, all four S2 guards run on the wrong
subject and pass.

Gross collisions are rare (6 names over 12 facts), so the finding is not "548
are wrong". It is that **548 are unaudited and the characteristic failure mode
is invisible to every screen available without the kernel**. Reducing that
number by filling in `formal.kernel_theorem` is worth more than any new gate.

**4. ADR-0795's "only one gate publishes a per-fact set" is superseded: two do,
and a third publishes half of one.** C2's checked-interchange census publishes
`credited_roots_replay.roots[].fact_id` with per-root `lean_admitted_by_name`,
`reimport_type_matches` and `status`, and is uncredited by the census today.
S3's `fixture-pack.json` carries `fixtures[].fact_ids` but not the
`load_bearing` map that adds the numerics half. S2 and S4 remain as ADR-0795
described them.

**5. "Axiom-free" is reported as a completeness property of the proofs, with
its two exclusions named in the same breath.** The replacement text:

> checked per subject by a closure walk from the admitted term for 1,956 ledger
> facts and independently re-checked by Lean 4.30.0's kernel for 1,972
> declarations of the constructed real carrier — which establishes the proofs
> are complete, not that the statements are the intended ones (582 bound by
> hash to pinned Mathlib, 9 additionally type-checked against Lean's
> reconstruction) and not that they are non-vacuous (8).

**6. A prelude-wide sweep is not per-fact protection and the count that matters
is how many facts have nothing else.** 434 facts (20%) hold exactly one
protection and it is `env_footprint`; 105 hold none; 440 read
`env_footprint: yes` with `coverage_bearing_checker: no`. The three widest
checker commands are one `nat_axiom_inventory --require-axiom-free` invocation
shared by 467, 347 and 290 facts.

**7. The L0 programme is enforced only by the local aggregate battery.** All
eight L0 gates plus the S5 differential appear in `justfile` and
`scripts/check.sh` and in **neither** `.github/workflows/ci.yml` nor
`hooks/pre-push`. The census was stale and `gen-safety-matrix.py --check` exited
1 at the time of this audit — the "records stale ledger state" clause of risk 5,
landing on the instrument that measures risk 5, undetected for seven hours
because nothing forces the battery to run.

## Evidence

Executed in the foreground, exit status read from the bare command:

| command | result |
|---|---|
| `check-settled-fact-statements.py` | 0 — `settled=2169 pinned=2169 identity_bound=1300 header_exempt=30 drifted=0` |
| `check-statement-identity-mutations.py` | 0 — 5/5 rejected, tree clean before and after; **mutations 1-3 caught by the pin alone**, i.e. only because the statement changed after pinning |
| `check-mirror-statement-fidelity.py` | 0 — `mirrors=594 hash_verified=582 unpinned=12` |
| `check-semantic-control-fixtures.py` | 0 — `fixtures=13 executed=9742 killed=18 also_true=1 survived=0`, `load_bearing=8` |
| `scripts/tests/test-trust-closure.sh` | 0 — `cases=17 mutations=15 not_exactly_one=0` |
| `scripts/tests/test_safety_matrix.py` | 0 — 7 tests |
| `check-kernel-differential-mutants.py` | 0 — 8 mutants, 8 killed, 8 subsystems |
| `check-kernel-differential.py --self-test` | 0 — G1-G6 each on its own fixture |
| `gen-safety-matrix.py --check` | **1 — stale** |

Not executed, and reported as read: `check-trust-closure.py` itself (its
projection needs a `--release` kernel build), the S5 differential against Lean,
the S4 replay census, `check-fact-evidence-replay.sh` (9,900 s deadline).

On risk 1 specifically: the differential covers all 8 roadmap subsystems in 35
cases with zero Axeyum-accepts/Lean-rejects and one pre-registered
Axeyum-rejects incompleteness, and it cannot pass by skipping (the gate forces
`AXEYUM_REQUIRE_LEAN=1`, and guard G4 fires independently on a missing
`AXEYUM-LEAN-CHECKED` line). "8 of 8 mutants killed" is a **pinned human
measurement** — the ratchet validates the artifact's internal consistency and
deliberately does not re-run mutations, and says so. Positivity is implemented
twice (`inductive.rs:1917` and `:2125`, sharing `mentions_group_family` at
`:1995`); neither copy is individually load-bearing, both disabled admits a
non-positive inductive, and the shipped mutation is aimed at the shared
predicate — so the `inductives` kill is real, and the residual limitation is
that a defect *in* the shared predicate is invisible, with only its `Const` arm
exercised.

## Alternatives

**Produce a weighted safety score.** Rejected: a single number hides exactly the
per-risk detail this audit exists to surface, and it would let contamination's
1,956 mask vacuity's 8.

**Repair the columns in this lane.** Rejected: an audit that edits its subject
cannot be checked against what it found. Each finding names the gate that owns
it.

**Read `circularity` at 14 as the contamination number.** Rejected, and this is
ADR-0795's finding restated because it keeps being quoted: per-fact evidence for
target self-occurrence is **0**, and the real coverage is S2's ~1,956.

## Consequences

- The next safety increment is vacuity, and its first task is a fixture family
  outside `Nat.totient`.
- The census can add a coverage row for the 9 checked-interchange roots today,
  from data already committed, with no new measurement.
- Filling `formal.kernel_theorem` on the 548 regex-resolved facts converts the
  largest unaudited surface in the programme into checked bindings and would
  raise `identity_bound`, `kernel_theorem` and `coverage_bearing_checker`
  together.
- Whether the L0 gates should move into CI or `hooks/pre-push` is a scheduling
  question this ADR does not decide; it records only that today they are in
  neither, and that a red census went unnoticed because of it.

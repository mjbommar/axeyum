# ADR-0219: Glaurung internal warm-regime attribution

Status: accepted
Date: 2026-07-17

## Context

ADR-0218 finds outcome, consumer purpose, and exact-query reuse composition,
but cannot explain which Axeyum phases or retained structures cause the
win/tie/loss map. Formula bytes and lexical operator counts are especially
weak proxies because rewriting and structural hashing can map similar text to
very different AIG/CNF work.

Glaurung already exposes complete opt-in cold and retained Axeyum profiles.
Their synchronous identity rendering and JSON output add diagnostic overhead,
so they cannot replace the unprofiled N=5 four-cell ratios. They can still
answer the internal-work question when joined to the same ordered checks.

## Decision

Accept a fail-closed ordered profile join and one diagnostic process on each of
the four mapped drivers. Require two consecutive profile records per check,
one native cold and one direct-delta warm in either rotated order, with exact
query hash, outcome, completeness, and cardinality. Require named phase time
plus unattributed time to equal adapter total.

Use this artifact only for internal phase and structural attribution. Continue
to source solver speed ratios and confidence intervals from the unprofiled N=5
reports. Do not compare the profiled outer fair timings: synchronous profile
emission visibly dominates them.

## Evidence

The join covers all 9,526 checks across four independent diagnostic runs.
Focused tests cover rotated cold/warm order, timing identity, cardinality, and
query-hash rejection. All 67 benchmark-script tests that do not invoke `just`
pass; the remaining nine recipe-expansion tests are unavailable on this host
because the `just` executable is not installed. Link and foundational-resource
checks pass independently.

Cold structure, not lexical bytes, explains the first discrepancy. Mean cold
AIG nodes/clauses per check are 5,513/7,250 Dptf, 5,150/6,371 vwififlt,
1,567/1,746 IntcSST, and 727/626 SurfacePen. Retention cuts new per-check
structure to 70/126, 13/49, 26/61, and 8/23, respectively.

After retention, SAT is Axeyum's largest measured phase on every driver:
65.10% Dptf, 70.32% vwififlt, 58.36% IntcSST, and 47.75% SurfacePen. CNF is
20.40%, 11.23%, 16.56%, and 12.02%. Thus broad warm construction work is no
longer the general performance boundary.

The UNSAT stratum selects a narrower residual. Dptf adds 148 AIG nodes and 258
clauses per warm UNSAT check and spends 36.55%/51.85% in CNF/SAT; its
unprofiled warm ratio is 0.3324x. vwififlt, IntcSST, and SurfacePen add
20/76, 53/134, and 31/73 with CNF/SAT shares 36.58%/42.44%, 51.26%/26.83%, and
37.02%/24.53%; their warm UNSAT ratios are 0.7887x, 0.9707x, and 2.0382x.

The exact reports and occurrence tables are committed under
[`bench-results/glaurung-profiled-four-driver-20260717/`](../../../bench-results/glaurung-profiled-four-driver-20260717/README.md).

## Alternatives

- Treat query bytes as construction work: rejected by the measured structural
  reversal.
- Publish profiled fair ratios: rejected because synchronous identity rendering
  and JSONL emission occur inside the outer cell and dominate it.
- Resume broad CNF optimization from cold shares: rejected because retained
  SAT is now the largest phase everywhere.
- Attribute Dptf solely to retained clause additions: rejected because similar
  UNSAT clause additions on vwififlt/SurfacePen yield different solver order.
- Generalize from one profiled process to a variance claim: rejected; N=1
  profiles select a mechanism experiment, not a timing estimate.

## Consequences

The performance story can now say that retained topology removes nearly all
repeated construction and moves the residual into SAT plus an UNSAT-sensitive
CNF/SAT boundary. It still cannot claim why one SAT core wins a stratum.

The next performance experiment is identical retained Dptf UNSAT CNF across
Axeyum's core and neutral/Z3 controls, repeated without synchronous profile
output. Construction work remains a reported covariate. Publication blockers
for multi-oracle fuzzing, neutral end-to-end baseline, timeout sensitivity, and
authoritative finding parity remain unchanged.

# ADR-0234: Real-query QF_BV term-to-CNF faithfulness

Status: accepted
Date: 2026-07-18

## Context

ADR-0230 proves that every UNSAT in the exact 128-query representative
Glaurung manifest carries an independently rechecked CNF DRAT proof. That
certifies the emitted CNF, but not the original term-to-AIG-to-CNF reduction.
ADR-0231 makes the stronger independent-reference bit-blast miter
deadline-aware on generated formulas, while explicitly leaving real-query
faithfulness open.

The reviewer checklist asks for the frequency at which the miter is actually
run and requires the trusted reduction boundary to remain visible. Selecting
only certificates that happen to finish would overstate coverage, and adding
certificate time to solver timing would corrupt the performance evidence.

## Decision

Advance `axeyum-bench` to artifact version 33 and expose
`--certify-end-to-end-unsat --end-to-end-deadline-ms N` only on the raw,
full-query, proof-producing `sat-bv` path. For every primary UNSAT, compose:

1. a DRAT-refuted miter between production bit lowering and an independent
   reference bit-blaster; and
2. the independently rechecked DRAT refutation of the production CNF.

Recheck both stored certificate texts before granting `certified`. Partition
every primary UNSAT into certified, not-certified, satisfiable contradiction,
recheck failure, or operational error. Keep not-certified rows in the declared
denominator; fail the run on the other three alarm classes or when the attempted
count differs from primary UNSAT.

Record certificate time as separate assurance work. State that the absolute
deadline is shared by the proof-producing searches, not by independent
construction or completed-proof checking. Whole-process isolation remains a
separate follow-up.

Artifact v33 also adds the already-reported `cnf_vivify` switch to
`config_hash`; v32 recorded the switch but did not fingerprint it.

## Evidence

At clean source `21738d42`, two CPU-3-pinned processes run the same exact
162-query `glaurung-qfbv-2026-07-16-corrected-wide-v3` representative manifest
accepted by ADR-0187 under a predeclared 1000 ms per-UNSAT proof-search policy.
Both runs have identical source, configuration, environment, manifest, and
per-query certification identities.

- 162/162 decide with zero Unknown, unsupported, error, oracle disagreement,
  manifest disagreement, or SAT-model replay failure;
- all 88 SAT models replay against the original query;
- 74/74 UNSAT rows carry independently rechecked CNF DRAT;
- 74/74 UNSAT rows also carry independently rechecked end-to-end
  faithfulness-plus-DRAT certificates;
- zero rows are not-certified; zero satisfiable contradictions, recheck
  failures, or certificate errors occur;
- certified families are 26 `register-slice`, 24 `slice-partial`, 18
  `arithmetic`, 5 `comparison`, and 1 `mixed`.

End-to-end assurance-work p50/p95 is 0.930/55.101 ms and 1.167/55.445 ms in
the two runs. Maxima are 152.718 and 154.163 ms, leaving headroom under the
1000 ms policy. These timings include completed-proof recheck and are not
solver performance measurements; ADR-0231 separately records generated rows
that expire under a tighter policy.

The raw v33 artifacts and fail-closed repetition join are committed under
[`bench-results/glaurung-real-query-faithfulness-20260718/`](../../../bench-results/glaurung-real-query-faithfulness-20260718/README.md).

## Consequences

The publication may report 74/74 (100%) end-to-end certified UNSAT over the
complete corrected five-driver representative real-query denominator. It must
keep this denominator distinct from ADR-0230's historical three-driver 64-row
CNF-only result and ADR-0231's 1,505-row generated cohort, and state the
independent-reference bit-blaster and Tseitin implementation in the TCB.

This closes representative real-query term-to-CNF faithfulness. It does not
cover the 30,628-query corrected full corpus, prove an external standard proof
format, bound the whole certificate call to one second, or affect the fair
performance map. Next proof work is killable whole-process isolation and wider
real-query manifests. Independent fuzz seeds plus another neutral implementation
and timeout-sensitive/wider sole-authority findings remain publication work.

## Alternatives

- Count only completed certificates: rejected because it drops the hard rows
  from the denominator.
- Treat deadline expiry as a proof failure or solver verdict: rejected because
  resource-bounded non-certification is neither an invalid proof nor SAT/UNSAT.
- Add assurance time to cold solver time: rejected because the certificate
  reruns independent construction and proof search under a different policy.
- Call CNF DRAT end-to-end: rejected because it leaves bit lowering trusted.
- Claim a one-second wall-clock API guarantee: rejected because construction
  and checking are not yet process-isolated.

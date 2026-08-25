# Lane: fp-misc-hang — the FP audit timeout was a classifier, not a budget

<!-- plan-section: lane-status -->

**`QF_FP/solver__fp__fp_misc.smt2` timed out because `array_bv_abs::abstract_term`
walks a DAG as a tree; memoized, the row goes from 124.7 s of a 125 s budget to
314 ms. It is now certified and independently checked and it is still not
dominant, and that second half is correct rather than unfinished** (`DONE`,
agent-fp-misc-hang, 2026-08-21).

**The null was the finding.** `audit_dominance` fills `timeout_phase_detail`
from `scan_proof_fragment` *before* reconstruction starts, so `fp_misc`'s
`detail: null` meant classification itself never returned — while three sibling
rows in the same run did name their fragment, which is the positive control that
the mechanism worked. Eight of eight `gdb` samples, 100% of the axeyum frames,
were in `abstract_term`, self-recursive dozens of frames deep. `perf` and a bare
`gdb -p` are both blocked on this host (`perf_event_paranoid=4`,
`ptrace_scope=1`); an unprivileged sampling loop returns an empty file that reads
exactly like "nothing to see". `sudo gdb -p` works.

Detail moved to [`../notes/115-fp-misc-hang.md`](../notes/115-fp-misc-hang.md).

<!-- plan-section: landed-changes -->

| 2026-08-21 | `a3799dca2` | **`QF_FP/fp_misc`'s "timeout" was an unmemoized DAG walk in the classifier.** `array_bv_abs::abstract_term` re-explored shared subterms once per path; 8/8 `gdb` samples sat in it. Memo + visit budget, each guard mutation-verified to kill exactly one test: **124.7 s timeout → 314 ms**, 4,194,309 visits → 4,365 over 5,762 nodes. QF_FP `timeouts 1 → 0`, certified/checked 15/16 → **16/16**; `dominant` stays 15/16 and the row now declares `bit-blast` instead of `timeout`, because `887b52e64` withdrew its term-level FP route on purpose. Also measured and pinned: `QF_BVFP/Float-no-simp3-main` is not the "evidence exceeds 120 s" it was recorded as — its reduction certificate is `proved` in **28.3 ms** and is withheld only by `produce_evidence`'s blanket "timeout set → skip", whose deadline covers the SAT search and none of `lower_terms` / `tseitin_encode` / `check_drat` / LRAT. QF_FP and QF_BVFP audits re-run at `a3799dca2`; `proof_errors` 4 → **3**, certified/checked 280 → **281**, and the four moved markers in `PROJECT-STATE.md` and the gap analysis renumbered with the account of what moved them. |

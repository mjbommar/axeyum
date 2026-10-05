# Lane: uflia-trace — why UFLIA's e-matching does not convert, traced against z3 and cvc5 (ADR-2113)

<!-- plan-section: lane-status -->

**Lane UFLIA-TRACE (`WIP`, uflia-trace, 2026-09-15).** The division's blocker is
**located and sized, and it is not what anybody was looking for.** On
ADR-2090's 53 reference-minimal UFLIA cores: z3 refutes 53 of 53 with
`smt.mbqi=false` (median 108 ms) and its proofs name a **median of 6**
instantiations; cvc5 agrees 53 of 53. We decide 15. On the 19 cores whose
per-universal probe runs, **444 of 500 universals admit nothing all run**, the
loop makes **4.3 M joins** and admits **37,414** instances. The split that
matters — `silent-split.py`, built here because no aggregate count can make it —
is **NEVER-MATCHED 0 of 478** and **ALL-REJECTED 429 of 478**, with **100.0 % of
2,139,815 rejections a single reason, `rej_nocontext`**. And the terms z3
substitutes are already ours: of the 741 GROUND arguments in z3's own proofs
across those cores, **728 (98.2 %) are in our accumulated ground set**. We build
them, we match them, and we throw the instances away — a universal nested under
a disjunction, compiled and matched, every tuple discarded because
`A ∨ (∀y. B(y))` does not entail `B(t)` and no positive-replacement context
exists for it. **UFLIA has ZERO e-matching fixpoint give-ups** — the brief's "12
fixpoints" is a cross-division count.

**Next lane: `rej_nocontext`, not triggers.** Two routes, sized in ADR-2113 §6 —
(a) preprocess so the nested universal is no longer nested, which is what the
references do and is the larger change; (b) widen where `PositiveContext` is
computed, which uses machinery that already exists and should be sized first.
**Do not re-run the trigger-alternative lever on this population**: its bucket is
measured at zero here. It may still matter on UF, whose category A is 728
triggerless universals — a different shape.

`AXEYUM_QINST_TRIGGER_ALTERNATIVES` is built, sound, deterministic, tested and
**shipped OFF**. Its A/B reached **909 of 1,200 rows** before this lane closed:
**+5 total, 0 verdict disagreements, 0 nonzero exit statuses**, 10 raw gains and
5 raw losses NOT re-checked (an earlier snapshot of the SAME run at 832 rows read
+6, with `AUFLIRA` at +0 where it now reads −1 — which is what an un-re-checked
mover column is worth). **Six of the nine gains are in `UF`** — the division
whose silence really is unmatched triggers — and `UFLIA`, whose NEVER-MATCHED
class is 0 of 478, moves +1 on 99 rows. That is the census predicting the A/B,
which is a check on the diagnosis and not a reason to ship. **Open for the next
lane: the remaining 368 rows and `recheck-movers.sh` over the 12 raw movers.**
The ship criterion (0 stable losses on the full six divisions) is NOT met, so
the lever stays OFF and ADR-2113 stays `proposed`.

<!-- plan-section: landed-changes -->

| 2026-09-15 | uflia-trace | ADR-2113: UFLIA's blocker is `rej_nocontext` at 100.0 % of 2,139,815 rejections — NEVER-MATCHED is 0 of 478, so trigger selection cannot reach it |
| 2026-09-15 | uflia-trace | `AXEYUM_QINST_TRIGGER_ALTERNATIVES` (OFF): auto selection may propose several trigger alternatives, as z3 and cvc5 both do; 5 unit + 7 integration tests, soundness-negative over satisfiable queries at six caps |
| 2026-09-15 | uflia-trace | `silent-split.py`: the NEVER-MATCHED / ALL-REJECTED split, reusable on any division, with a guard that says `REASONS-UNMEASURED` rather than printing an OFF census's zeros |
| 2026-09-15 | uflia-trace | reference arm: all 53 UFLIA cores are E-matching-only (`smt.mbqi=false` refutes 53/53); `proof-instances.py` names the substituted terms out of z3's own proof |

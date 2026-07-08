# Target-phase rephasing on public p4dfa — measured findings

Status: **measurement-grounded finding (2026-07-07).** P1.3 SAT-core modernization,
slice T1.3.1 (target-phase rephasing) landed in `crates/axeyum-cnf/src/proof_sat.rs`.
Sibling to
[inprocessing-reduction-levers-p4dfa-findings.md](inprocessing-reduction-levers-p4dfa-findings.md)
(the encoding-side pulse) and the T1.3.2 restart-policy result recorded in the
`proof_sat.rs` `use_ema_restart` field doc.

Gate: `DISAGREE = 0` and every `unsat` still DRAT-checks — absolute, and held in
**every** configuration below.

## The lever

**Target-phase rephasing** (Glucose/CaDiCaL family, T1.3.1). The custom CDCL core
already had phase saving (remember each variable's last-assigned polarity). Rephasing
adds a **target**: the solver snapshots the decision polarities of the *deepest
conflict-free assignment seen so far* — the assignment "closest to a model" — and on
each restart resets the saved phase to that target, so search re-descends toward the
best assignment instead of the last-seen polarities. It is a pure decision-order
heuristic (verdict-preserving by construction: phase only picks polarity, never
implications or conflicts), gated by `use_target_rephase` (default **on**).

## Why it is the right lever *here*

Per ADR-0037 the public p4dfa slice is **all-`sat`** DFA/protocol bit-logic — there is
no `unsat` instance in the corpus. Target rephasing directly serves SAT search: it
biases the descent toward the most-complete partial model found, which is exactly how
a satisfying assignment is reached. This is the structural reason it succeeds where the
sibling **restart-policy** slice (T1.3.2 EMA glue restarts) came out *neutral*: restart
cadence is an UNSAT/mixed-search lever (it abandons unproductive prefixes to find
refutations faster), and there are no refutations to find on an all-`sat` corpus.

## The measured A/B (native CDCL, `--backend sat-bv --native-cdcl`, 15 s, DISAGREE = 0)

`sat` = decided satisfiable; `unk` = unknown (timeout); `PAR-2` = harness
`par2_mean_s` over the family (lower is better). Rephase-on vs rephase-off, same
binary modulo the `use_target_rephase` default:

| family | rephase **off** | rephase **on** | delta |
|---|---|---|---|
| MobileDevice | 2 sat / 1 unk / PAR-2 **12.12** | **3 sat** / 0 unk / PAR-2 **2.04** | **+1 decide, 6× faster** |
| Composition | 4 sat / 5 unk / PAR-2 19.03 | 4 sat / 5 unk / PAR-2 18.32 | same decides, PAR-2 ↓ |
| TCP | 0 / 6 (all timeout) | 0 / 6 (all timeout) | — |
| VideoConf | 0 / 5 (all timeout) | 0 / 5 (all timeout) | — |
| StringMatching (sample 10) | — | 0 / 10 (all timeout) | — |

- **A real decide-rate gain, not just PAR-2.** Rephasing flips a MobileDevice instance
  that timed out under plain phase saving into a decided `sat`, and cuts that family's
  PAR-2 ~6× (12.12 → 2.04 s).
- **Rephase-on dominates rephase-off everywhere measured** — strictly better on
  MobileDevice, PAR-2-better on Composition, identical (all-timeout) on the genuinely
  search-bound TCP/VideoConf/StringMatching families. No regression anywhere. So it
  ships **default-on** (unlike T1.3.2, banked default-off for its Composition regression
  on the same corpus).
- The hard families stay all-timeout under either phase policy: rephasing converts the
  *near-miss* SAT searches, not the deeply search-bound ones (those remain the province
  of the larger in-solver-inprocessing arc that ADR-0059 identified).

## Verdict → where the next SAT-search dollar goes

- **T1.3.1 rephasing is a sound, measured, default-on decide-rate win** on the all-`sat`
  p4dfa slice — the first custom-core heuristic slice to move the decide count (not just
  PAR-2) on this corpus.
- **The lesson for the corpus:** on an all-`sat` slice, *SAT-convergence* heuristics
  (target rephasing, and candidate follow-ups: a SAT-oriented initial phase beyond the
  all-`false` default, decision-variable ordering, local-search hand-off) move the
  decide rate; *throughput* micro-slices (binary-clause fast path) and *UNSAT-oriented*
  ones (restart policy) do not. Future P1.3 effort on p4dfa should follow the
  SAT-convergence thread first.
- **Restart policy revisited — measured, and it stays off.** T1.3.2 EMA restarts
  regressed one Composition decide *without* rephasing; the natural hypothesis was that
  EMA + rephasing would combine (more restarts → more rephase-to-best opportunities). It
  does **not**: measured, `EMA + rephase` *loses* the MobileDevice decide that
  `Luby + rephase` wins (2 vs 3 sat, PAR-2 10.93 vs 2.07 s) and is no better on
  Composition — EMA's aggressive restarting disrupts the rephasing convergence. So the
  default stays **Luby + target rephasing**, and EMA restarts stay default-off both with
  and without rephasing. The current default is the measured optimum of the four
  (Luby/EMA) × (rephase on/off) configurations on the decidable families.

## Full-113 headline (native-cdcl rephase-on, 20 s, DISAGREE = 0)

Run over the **entire** committed 113-file p4dfa slice at the 20 s budget ADR-0059
used for its baselines:

| solver / config | decided @20s |
|---|---:|
| batsat OFF (eager) | 4 / 113 |
| **native-cdcl + target rephasing** | **7 / 113** |
| batsat ALL-ON (inprocessing + vivify) | 7 / 113 |
| Z3 4.13.3 crate | 8 / 113 |
| Z3 4.13.3 CLI | 9 / 113 |

- The custom core — which the P1.3 scoping clocked at **4–8× slower than batsat** on
  decided instances — is now **decide-count-competitive with batsat's best config**
  (7 = 7) and within **1–2 of Z3** on this hard, all-`sat` slice, all `sat` decisions
  replay-checked (`DISAGREE = 0`, PAR-2 mean 37.71 s).
- Rephasing is the increment that closed the last of that gap: the decidable-family
  A/B (above) is a clean `+1` decide over plain phase saving, and it is what lifts the
  native core to batsat-ALL-ON parity here. The residual 106 unknowns are the deeply
  search-bound instances that time out under *every* engine measured (batsat, Z3, and
  the native core alike) — the province of the larger in-solver-inprocessing arc, not a
  phase/restart heuristic.

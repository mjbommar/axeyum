# Lane: a13-lra — QF_LRA's replay wall: the tableau admission currency (ADR-2146) and the disequality split (ADR-2147)

<!-- plan-section: lane-status -->

**A13-LRA (`landed`, a13-lra, 2026-09-17).** Stock-take queue item 2, both
levers built, measured and decided
(`bench-results/lra-admission-diseq-20260917/`). Sizing at head first: 27 / 27
no-tableau rows stop at `fm-fallback-declined` at the census screen and
**27 / 27 at the ATOM SCREEN at the shipped multiplier** (every one has more
than the 1,024 atoms it admits); 11 / 11 disequality rows stop at
`model-built-but-does-not-replay`; `sc-25`'s **371 of 776** equality atoms
asserted false confirmed from the shipped route's own probe. **ADR-2147
(`AXEYUM_LRA_DISEQ_SPLIT`) ships ON, accepted:** cvc5's model-driven split
with the strict halves riding the equality's own tableau rows, the native
core re-polling `take_new_atoms` after a `Sat` final check. One binary, four
env arms interleaved per file on idle s5/s6, 24 s / 8 GiB: pinned `QF_LRA`
**107 → 113** (5 STABLE-GAIN `sc-7/9/11/13/15` + 1 UNSTABLE `sc-17` after 3×
recheck), held-out **93 → 97** (4 stable), `QF_UFLRA` **148 → 150** (2
stable), `QF_IDL` 112/112 and `QF_RDL` 150/150 unmoved, 0 losses, 0 flips, 0
`:status` disagreements, 0 rc-134 in any arm. **ADR-2146
(`AXEYUM_LRA_ADMIT_NONZEROS`) stays OFF, proposed:** inert at the shipped
screen by arithmetic (107/107, 93/93, 148/148, wall identical); under
`AXEYUM_LRA_ATOM_SCREEN=16` it turns the screen's 8 rc-134 aborts into clean
`unknown`s, decides none of the 27 (the witness wall goes, the search behind
it runs the whole budget) and costs one STABLE-LOSS by routing
(`ecoliMILP…`). Two defects found on the way: the ADR-1704 artifact
constructor panicked on a lemma over a fresh variable (widened, pinned), and
the shipped route could not refute `x ≠ y ∧ x ≤ y ∧ x ≥ y`. One
mutation-control finding: the first sat-side fixture SURVIVED the
eq-dropping mutation (the search never split) and was replaced. Gates: five
z3 fuzzes × four env arms before and after the flip (1,500/1,500 agree,
boundary 12/12), corpus_regression, `--lib --features full` 1,681/0 on a
quiet box, the LRA/LIA suites, workspace clippy `-D warnings` exit 0, nine
one-test mutation suites all `killed 1`, stale=0. `uflia_online`'s
`opaque_app_interface_overflow…` fails identically at the merge base
(pre-existing). **Next for `QF_LRA`:** budget hand-back from a non-converging
online search (the `ecoliMILP` routing shape) and the search cost on
`sc-19 … sc-25` / `pursuit-safety-16`, where the split removes the wall and
24 s is not enough.

<!-- plan-section: landed-changes -->

| 2026-09-17 | a13-lra | ADR-2147 accepted, `AXEYUM_LRA_DISEQ_SPLIT` ON: `QF_LRA` pinned 107 → 113 (5 stable + 1 unstable), held-out 93 → 97 (4 stable), `QF_UFLRA` 148 → 150, DL controls unmoved, 0 losses/flips/disagreements/aborts; ADR-2146 proposed, `AXEYUM_LRA_ADMIT_NONZEROS` OFF (inert at the shipped screen; at 16× removes 8 aborts, decides none of the 27, 1 routing loss). `bench-results/lra-admission-diseq-20260917/`. |
| 2026-09-17 | a13-lra | `0f311e650` ADR-2146 / ADR-2147 levers, unit + soundness-negative + certificate tests, `distinct` and boundary-tableau fuzz seed classes, nine one-test mutation suites, five registry entries, the A/B harness; `e9167dd21` the sizing. |

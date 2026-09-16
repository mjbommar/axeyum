# Lane: quant-instance-probe — separating instance SELECTION from ground REFUTATION on ADR-2113's 53 UFLIA cores

<!-- plan-section: lane-status -->

**Lane QUANT-INSTANCE-PROBE (`DONE`, quant-instance-probe, 2026-09-16).**
ADR-2113/ADR-2120/ADR-2124/ADR-2130 left one question unreconciled: our
engine admits a median of 1,473 quantifier instances per core against z3's
proof using 6 (ADR-2113) — is the block instance SELECTION (our 1,473 drown a
ground solver that would refute z3's 6 at once) or ground REFUTATION (even
handed z3's own instances, our ladder does not decide the set)? This lane ran
the experiment: extracted z3's own used instantiations from its refutation
proof (`scripts/z3-proof-instances.py`, new), built ground-only `QF_UFLIA`
files from them with every quantifier stripped, and ran our release engine on
them directly — bypassing our own e-matching loop entirely.

**Answer: predominantly SELECTION.** Of 53 cores, z3-checking the
reconstructed file finds **7 z3-confirmed-complete** (the extraction
recovered every used instance) and **41 incomplete** (some instance was not
recovered — 46 % of the 1,021 raw recovered bodies across all 53 cores still
carry an unresolved outer bound variable from a NESTED instantiation, the
same `rej_nocontext` mechanism ADR-2113 §4b already named, independently
reconfirmed here from the opposite direction). **Of the 7 complete cores, our
existing ladder (`euf-online`/`uf-arithmetic`) refutes 6 (86 %)** — handed
z3's own minimal instance set as plain ground assertions, with no selection
problem left to solve, our ground checker closes the SAME refutation z3 finds
in 5 of 6 cases in ~107 ms. Zero wrong-unsat disagreements against the
z3-ground check across all 48 built files.

**A second arm (our OWN admitted instances, via `AXEYUM_QGROUNDDUMP`) found a
tooling gap worth naming precisely because it is a NEW finding.** 16 of 29
buildable files fail immediately at PARSE — not at solve — because the
dumped admitted-instance set leaks OUR OWN internal Skolem constant names
(`!qsk_N`/`!qu_N`/`!q.?x_.N`, declared in `quant_skolemize.rs:64-65` with no
standalone `declare-fun`) that `axeyum-smtlib/src/parse.rs:16570` correctly
refuses once re-serialized bare. This is a defect in this lane's OWN
`build-ground-from-dump.py`, not a ground-refutation measurement, and is
reported as such rather than left to read as a negative result. Of the 13
files that DID parse, our engine decided only 1 (`unsat`, using 2,828 of its
own admitted instances) and 5 of the remaining 8 unknowns ran to the full
~25 s budget — consistent with, though at n=13 not conclusive proof of, the
"large admitted set drowns the ground checker" half of the hypothesis.

**Full table, methodology, and both dominant-typed-reason citations** (one
already-known and independently reconfirmed, one new) are in
[`bench-results/quant-instance-probe-20260916/README.md`](../../../bench-results/quant-instance-probe-20260916/README.md).

**What is left.** The nested-instantiation chain that makes 46 % of z3's own
instances not-ground is not resolved (would need enough of z3's
`quant-intro` proof-rule semantics reimplemented to track schema variables
across the proof DAG) — this is why Count 1 is 7 of 53 rather than higher,
and a cleaner extraction is the most direct way to widen the clean-ground-truth
population this experiment runs on. The Skolem-leak parse failure on the
admitted-instances arm is fixable (`build-ground-from-dump.py` would need to
also emit `declare-fun` lines for every referenced internal symbol, with the
right sort) but was not attempted here. `FFT_smtlib.898060` is a genuine,
narrow ground-refutation miss (whole ladder declines, 107 ms, 26 attempts) —
worth a look on its own, separate from the selection question this lane
answers.

<!-- plan-section: landed-changes -->

| 2026-09-16 | quant-instance-probe | `scripts/z3-proof-instances.py` + 27 unit tests: recovers the GROUND consequence of a z3 `quant-inst` proof step (not just the substituted terms `proof-instances.py` already named), splitting GROUND from NOT-GROUND (nested-instantiation) bodies; 53/53 positive control against ADR-2113's `proof_qinst` |
| 2026-09-16 | quant-instance-probe | `bench-results/quant-instance-probe-20260916/`: the ground-only file builders (`build-ground-only.py`, `build-ground-from-dump.py`), the driver scripts, and the full 53-core × 2-arm result table + README — 6 of 7 z3-confirmed-complete cores refuted correctly by our own ladder, zero wrong-unsat disagreements |

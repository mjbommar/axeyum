# Lane: evidence-certification — the verdict is not the certificate

<!-- plan-section: lane-status -->

**32.5% of the Lean gate's headline is an axiom shim, and nothing pinned which
routes are which** (`WIP`, evidence-certification, 2026-08-17). A
`StructuralAttestation` module is not a proof: the shared emitter takes no arena
and no assertions, so its output cannot depend on the query — it declares
`axiom prop : Prop`, `axiom hyp1 : prop`, `axiom hyp2 : Not prop` and derives
`False` by application. Lean accepts it, and that acceptance says nothing about
the proposition. Measured: of the **126** real-Lean checks
`scripts/check-lean-gate.sh` reports (the script's own floor still says ~113),
**41 are shims** — 56% of `lean_crosscheck`'s own checks, across 27 refuters —
including `qf_bv`, a test named for bit-vectors whose module contains no
bit-vector reasoning. The gate reports one undifferentiated total and
distinguishes the two nowhere.

Five of 61 fragments had their class pinned; the other 55 recorded it only in
the table, so editing emitter and table together moved a route from proof to
shim silently. `every_fragment_content_class_is_pinned_by_name` closes that,
and the control is measured, not asserted: moving `QfBv` to the attestation arm
(a clean-compiling change) turns 1164 passed / 0 failed into **1163 passed / 1
failed, and the one is this test**. Before it, nothing in the workspace caught
that move.

*Not yet done:* the gate still prints one number. Splitting it needs the suites
to report their class — most `report_checked` counts are hardcoded literals, not
tallies — so that is its own slice. **Do not quote the 126 as "modules Lean
proved" until then.**

**The e-matching route can now hand out the instances it used.** The driver
built exact provenance per instance and exposed an independent replay checker,
then dropped the map at every `return Ok(Unsat)`.
`prove_quantified_unsat_via_egraph_with_instances` reports a
`QuantifierInstanceSetCertificate`; `check_quantifier_instance_set` replays every
derivation against the caller's assertions, rejects a ground member that is
neither asserted nor derived, **and re-refutes the ground set** — checking only
provenance would certify true-but-insufficient instances. Four capture sites,
the fourth found by measurement: the smallest possible query (`∀x. f(x)=0` with
`f(5)≠0`) refutes through the *online CDCL(T)* session, not through any of the
three obvious checks.

*Blocked, structurally, not mechanically:* it is not wired to `Evidence`. The
certificate carries `TermId`s naming terms **created during** e-matching, which
do not exist in the arena `Evidence::check` is handed. Every family already
wired is arena-independent for this reason. Interning does not rescue it — that
needs identical rebuild order, which nothing enforces and no test would catch.
Making the certificate arena-independent is the next slice.

**Settled SMT-route facts are gated on `certified=1`, not just on the
verdict.** The
[`ledger-integrity`](97-ledger-integrity.md) lane re-measured finding 8 as
remediated — 177/177 checker runs *can* fail. That is true and it is not
sufficient: a run can fail on the wrong axis. Every settled `smt-term-level` /
`smt-clausal` fact carries evidence shaped
`test "$(… smtcomp_cli --evidence <i>.smt2 | tail -1)" = unsat`, which tests
the **verdict** and is blind to whether the refutation produced a **checkable
object**. Verified, not argued: that exact command shape **exits 0** on
`artifacts/facts/smt2/neg-barber-no-such-barber.smt2`, which reports
`kind=unsat-uncertified certified=0`.

Measured: **17 of 17** gated instances are `certified=1` (14 `unsat-term-level`,
2 `unsat-drat`, 1 `unsat-bool-simplification`). So the invariant held by
practice, with nothing enforcing it.
`scripts/check-smt-evidence-certified.py` now enforces it, using the barber as a
**real** negative control rather than a synthetic one — genuinely unsat, so a
verdict-only checker accepts it; genuinely uncertified, so a certification-aware
one must not. If it ever reports `certified=1` the check fails *on purpose*,
saying the fact can now be closed and the control must be repointed.

All seven guards were mutation-tested: delete any one and **exactly one** test
dies. (The first mutation run reported a wrong casualty — deleting the *verdict*
guard killed the *floor* test — which was stale `.pyc` reuse from rewriting one
filename inside a timestamp tick: the repository's documented cargo mtime trap,
in Python. Fixed with per-guard filenames and `dont_write_bytecode`.)

**`F:barber-no-such-barber` stays `open`, and one claim in its note was wrong.**
The note said the instantiation step was "one no component of ours performed or
recorded". Measured with `AXEYUM_QTRACE=1`, the solver performs it and records
it: `auto::solve` skolemizes to `!sk_0`, the e-graph route admits exactly one
instance, and `check_auto` refutes `p = ¬p`. That instance becomes a
`QuantifierInstanceCertificate` (`qinst_egraph.rs:2737`) which already has a
public independent checker, `check_quantifier_ground_derivation` (`:2821`). It
is never plumbed out — `ground_derivations` (`:1162`) is function-local and dies
at each `return Ok(Unsat)`, `skolemize_top_existentials` (`auto.rs:889`) returns
a bare `Vec<TermId>` discarding the assertion→`!sk_k` correspondence, and
`evidence.rs` references neither (grep: 0). `prove_unsat_to_lean` declines at
`skolem_alethe.rs:102-105`, whose slice requires the existential's body to be a
quantifier-free equality; the barber's body is a universal. The reconstruction
path is not failing to reconstruct — it is **re-deriving the instantiation from
scratch with weaker tools** than the decider that already succeeded. Control:
the fully instantiated ground formula reconstructs kernel-checked today.

**Next.** Slice 4 of that analysis, because it is orthogonal and the widest win:
thread the decider's instantiation certificates out and add an `Evidence`
variant whose `check` calls the existing public checker. That upgrades the whole
e-matching route from `unsat-uncertified` to certified, not just the barber.
Slices 1–3 (widen the ∀ emitter's witness vocabulary; make its ground tail
pluggable; relax the `Exists` body restriction) close the barber itself.

Caveat carried forward, not yet acted on: `certified=` and Lean reconstruction
are **independent axes**. A fact can be `certified=1` with no Lean module. Of the
61 `ProofFragment` variants, 29 are `StructuralAttestation` — a ~21-line
`axiom P` shim with no reasoning. Whether any settled fact rests on one is
unmeasured and is the obvious next audit.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `078b2776` | Every `ProofFragment`'s Lean content class pinned by name (`every_fragment_content_class_is_pinned_by_name`). 5 of 61 were pinned before; the other 55 recorded their class only in the table, so a coordinated emitter+table edit moved a route from theory reconstruction to `axiom P` shim with nothing failing. Control measured: moving `QfBv` to the attestation arm gives 1163 passed / 1 failed, and the one is this test. Context: 41 of the Lean gate's 126 real-Lean checks (32.5%, and 56% of `lean_crosscheck`) are already shims, `qf_bv` among them; the gate reports one undifferentiated total. |
| 2026-08-17 | `28755674` | The e-matching driver can report the instances that justified an `unsat`: `prove_quantified_unsat_via_egraph_with_instances` + `QuantifierInstanceSetCertificate` + `check_quantifier_instance_set`, which replays each derivation against the caller's assertions, rejects unlicensed ground members, and re-refutes the ground set (provenance alone would certify insufficient instances). Four capture sites; the fourth (online CDCL(T) replay) found only by measuring — the three obvious ones never fire for the smallest query. Not wired to `Evidence`: the certificate names terms created during e-matching that do not exist in the arena `Evidence::check` receives. |
| 2026-08-17 | `502c0503` | Settled SMT-route facts gated on certification, not just verdict: `scripts/check-smt-evidence-certified.py` requires `certified=1` for all 17 `smt-term-level`/`smt-clausal` instances (the ledger's own evidence commands test only the verdict and exit 0 on an uncertified refutation — demonstrated against the barber instance). Wired into `check.sh` and `justfile`; 16s warm in release (233s in debug, 232 of it DRAT-checking two fp16 instances). Seven guards, each mutation-tested to kill exactly one test. `F:barber-no-such-barber` stays `open`; its note corrected — the solver *does* record the instantiation as a `QuantifierInstanceCertificate` with a public checker, it is simply never plumbed to the emitter. |

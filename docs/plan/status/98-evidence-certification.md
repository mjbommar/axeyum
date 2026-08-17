# Lane: evidence-certification — the verdict is not the certificate

<!-- plan-section: lane-status -->

**Settled SMT-route facts are now gated on `certified=1`, not just on the
verdict** (`WIP`, evidence-certification, 2026-08-17). The
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

| 2026-08-17 | `pending` | Settled SMT-route facts gated on certification, not just verdict: `scripts/check-smt-evidence-certified.py` requires `certified=1` for all 17 `smt-term-level`/`smt-clausal` instances (the ledger's own evidence commands test only the verdict and exit 0 on an uncertified refutation — demonstrated against the barber instance). Wired into `check.sh` and `justfile`; 16s warm in release (233s in debug, 232 of it DRAT-checking two fp16 instances). Seven guards, each mutation-tested to kill exactly one test. `F:barber-no-such-barber` stays `open`; its note corrected — the solver *does* record the instantiation as a `QuantifierInstanceCertificate` with a public checker, it is simply never plumbed to the emitter. |

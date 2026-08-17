# Lane: evidence-certification — the verdict is not the certificate

<!-- plan-section: lane-status -->

**32.5% of the Lean gate's headline is an axiom shim, and nothing pinned which
routes are which** (`WIP`, evidence-certification, 2026-08-17). A
`StructuralAttestation` module is not a proof: the shared emitter takes no arena
and no assertions, so its output cannot depend on the query — it declares
`axiom prop : Prop`, `axiom hyp1 : prop`, `axiom hyp2 : Not prop` and derives
`False` by application. Lean accepts it, and that acceptance says nothing about
the proposition. Measured on arrival: of the **126** real-Lean checks
`scripts/check-lean-gate.sh` reported, **41 were shims** — 56% of
`lean_crosscheck`'s own checks, across 27 refuters — including `qf_bv`, a test
named for bit-vectors whose module contains no bit-vector reasoning. The gate
reported one undifferentiated total and distinguished the two nowhere. All three
of those are now fixed; the current gate output is below.

Five of 61 fragments had their class pinned; the other 55 recorded it only in
the table, so editing emitter and table together moved a route from proof to
shim silently. `every_fragment_content_class_is_pinned_by_name` closes that,
and the control is measured, not asserted: moving `QfBv` to the attestation arm
(a clean-compiling change) turns 1164 passed / 0 failed into **1163 passed / 1
failed, and the one is this test**. Before it, nothing in the workspace caught
that move.

`lean_crosscheck` now measures and ratchets that split, classifying from the
**rendered module source** (`LeanModuleContent::of_module_source`) rather than
from the fragment table — the artifact classifies itself, and no `lean` binary
is needed. Measured: **41 structural / 32 theory families**, and **72 / 95
modules** across the exhaustive sweep, which nobody had counted. Two families
are *mixed* — representative theory, other rows shims — so a representative-only
view undercounts. Ratcheted in both directions, because deleting a theory family
moves nothing a shim-count ratchet watches. The control is the point: adding a
duplicate contentless family trips it, while `lean_crosscheck_representative`
happily raised its own count 73 → 74 and **passed** — so until now, adding a
contentless refuter to the headline was entirely unguarded.

**The gate itself now reports both halves and floors the reasoning one**,
verified end to end under real Lean 4.30.0:

```
check-lean-gate: 16 suites, 54 tests, 127 real-Lean checks (floor 115)
check-lean-gate: crosscheck content: 33 families carry a theory reconstruction,
                 41 are structural attestations -- floor 33 on the reasoning half
check-lean-gate: OK -- 127 modules/controls were READ by a real Lean kernel
                 (41 of 74 crosscheck families are attestations, so this is not
                 a count of propositions proved)
```

Flooring only the sum is what let this hide: swapping a theory family for an
attestation leaves the total unmoved. Three guards, each driven to fail — raising the
theory floor exits 1 while the total stays put; an absent summary exits 1,
because silence must not read as a pass; and a present-but-unparseable summary
fails on the parse rather than letting the arithmetic print a confident wrong
split. The `qf_bv` test's own comment, which claimed "the bit-level resolution
refutation must type-check in real Lean", is corrected: that module is an
attestation with no bit-vectors in it. The refutation is real and checked in
Rust; only its Lean half is a shim.

**And the `qf_bv` puzzle is closed — it was a width, not a defect.**
`scan_ground_bv_proof_fragment` tries `term_level_enum_certifies` *before*
falling through to `ProofFragment::QfBv`, and rightly: exhaustive term-level
evaluation is the **stronger** Rust-side certificate, trusting neither the
bit-blaster, the CNF encoder, nor the SAT solver. It just has no theory Lean
module. Measured on `bvule a b ∧ bvult b a`:

```
width  2 / 4 / 8  → TermLevelEnum → StructuralAttestation
width 16 / 32     → QfBv          → TheoryReconstruction
```

The crossover sits between 8 and 16 bits, and the `qf_bv` family uses
`BitVec(2)` — so the test that reads as "the foundational bit-blasting path
checks in real Lean" runs at a width where bit-blasting is never used. QF_BV
*does* have a real reconstruction; nothing was exercising it.

So a `qf_bv_wide` family now runs the same theorem at `BitVec(16)` and asserts
the module is a theory reconstruction rather than merely that Lean accepted it —
"Lean accepted it" is precisely what an attestation also achieves. Real Lean
accepts it. The split moves **32 → 33 theory** families (structural unchanged at
41), and both floors are raised to lock the gain in. The boundary itself is
pinned by `narrow_bv_enumerates_and_wide_bv_reconstructs`, so it cannot move
silently.

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

**And it is now wired — I was wrong that it could not be.** I recorded this as
blocked by arena identity: the certificate names terms created *during*
e-matching, which are not in the arena the query was parsed into. The premise is
right and the conclusion was not. `produce_evidence` holds `&mut TermArena`, so
the producer runs the driver on **that** arena instead of a scratch clone, and
the instances land in the arena `Evidence::check` is later handed. A plain
universal now reports `kind=unsat-quant-instance-set certified=1 arena=ok`.

*Ordering was the real hazard, and I got it wrong first.* Placed among the
specialised quantified producers it **shadowed** stronger evidence — four
`evidence_finite_quant_uf_cert` tests and one in `evidence` lost their
guarded-quantifier UF Alethe certificate to this generic one. It is now the last
certifying arm, immediately before the bare fallback: the job is to upgrade what
was `Unsat(None)`, never to demote a stronger certificate.

*Still true:* the certificate is not **portable**. Its ids mean nothing to
another arena, so unlike an Alethe proof it cannot be serialised and re-checked
in a later process. Carrying the instances as data is a separate slice. The
barber also still needs the skolemisation record.

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

| 2026-08-17 | `pending` | QF_BV reaches Lean as REASONING: a `qf_bv_wide` crosscheck family runs `a <= b && b < a` at `BitVec(16)` and asserts the module is a theory reconstruction, not merely that Lean accepted it. The existing `qf_bv` family uses `BitVec(2)`, where `term_level_enum_certifies` wins before `ProofFragment::QfBv` is reached -- so the test named for the foundational bit-blasting path ran at a width where bit-blasting is never used. Crossover measured between 8 and 16 bits and pinned by `narrow_bv_enumerates_and_wide_bv_reconstructs`. Split moves 32 -> 33 theory families (structural unchanged at 41); both crosscheck floors and the gate's reasoning floor raised to match. Real Lean accepts it; gate reports 127 checks. |
| 2026-08-17 | `4cd5d6f0` | `scripts/check-lean-gate.sh` reports the two halves of its headline and floors the REASONING one (`THEORY_FAMILY_FLOOR=32`), verified end-to-end under real Lean 4.30.0. Flooring only the sum is what let the gap hide: swapping a theory family for an attestation leaves the 126 unmoved. Three guards each driven to fail — raised floor, absent summary, unparseable summary. Also corrects the `qf_bv` test's doc comment, which claimed a bit-level refutation type-checks in Lean; that module is an attestation containing no bit-vectors (the refutation is real and checked in Rust). |
| 2026-08-17 | `a1493099` | The e-matching route CERTIFIES: `Evidence::UnsatQuantInstanceSet` wired through `produce_evidence` / `kind_label` / `recheck_certificate` / `is_certified`; a plain universal goes from `unsat-uncertified certified=0` to `unsat-quant-instance-set certified=1`. Corrects my own claim that this was blocked by arena identity — `produce_evidence` holds `&mut TermArena`, so producing on it rather than a clone puts the instances where `Evidence::check` will look. Ordering is load-bearing and was wrong first: placed early it displaced the guarded-quantifier UF Alethe cert in 5 tests, so it is now the last certifying arm. Also fixes a `clippy::match_same_arms` my previous commit put on main. |
| 2026-08-17 | `c5f4c04b` | The Lean gate's content split is measured, printed per family, and ratcheted in both directions: 41 structural / 32 theory families, 72 / 95 modules. Classified from rendered module source, so no `lean` binary is required and the artifact classifies itself; a module claimed structural must also HAVE the shape, so the marker cannot become a sticker. Control: adding a contentless family trips the ratchet — while `lean_crosscheck_representative` raised its count 73→74 and passed, which is what was unguarded. |
| 2026-08-17 | `078b2776` | Every `ProofFragment`'s Lean content class pinned by name (`every_fragment_content_class_is_pinned_by_name`). 5 of 61 were pinned before; the other 55 recorded their class only in the table, so a coordinated emitter+table edit moved a route from theory reconstruction to `axiom P` shim with nothing failing. Control measured: moving `QfBv` to the attestation arm gives 1163 passed / 1 failed, and the one is this test. Context: 41 of the Lean gate's 126 real-Lean checks (32.5%, and 56% of `lean_crosscheck`) are already shims, `qf_bv` among them; the gate reports one undifferentiated total. |
| 2026-08-17 | `28755674` | The e-matching driver can report the instances that justified an `unsat`: `prove_quantified_unsat_via_egraph_with_instances` + `QuantifierInstanceSetCertificate` + `check_quantifier_instance_set`, which replays each derivation against the caller's assertions, rejects unlicensed ground members, and re-refutes the ground set (provenance alone would certify insufficient instances). Four capture sites; the fourth (online CDCL(T) replay) found only by measuring — the three obvious ones never fire for the smallest query. Not wired to `Evidence`: the certificate names terms created during e-matching that do not exist in the arena `Evidence::check` receives. |
| 2026-08-17 | `502c0503` | Settled SMT-route facts gated on certification, not just verdict: `scripts/check-smt-evidence-certified.py` requires `certified=1` for all 17 `smt-term-level`/`smt-clausal` instances (the ledger's own evidence commands test only the verdict and exit 0 on an uncertified refutation — demonstrated against the barber instance). Wired into `check.sh` and `justfile`; 16s warm in release (233s in debug, 232 of it DRAT-checking two fp16 instances). Seven guards, each mutation-tested to kill exactly one test. `F:barber-no-such-barber` stays `open`; its note corrected — the solver *does* record the instantiation as a `QuantifierInstanceCertificate` with a public checker, it is simply never plumbed to the emitter. |

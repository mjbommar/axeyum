# Lane: evidence-certification — the verdict is not the certificate

<!-- plan-section: lane-status -->

**Certification is now gated on being re-derivable, not on being claimed**
(`WIP`, evidence-certification, 2026-08-17). Full record:
[`diary-evidence-certification.md`](../../refactor-2026-08/diary-evidence-certification.md).

Three measurements drove the day, each a claim that was true in a way that read
as stronger than it was:

- **Ledger.** Settled SMT-route facts test the *verdict* (`… | tail -1` =
  `unsat`) and are blind to certification. 17 of 17 happened to be
  `certified=1`; nothing enforced it. Now gated, with the barber instance as a
  real negative control — genuinely unsat, genuinely uncertified.
- **Lean gate.** Of 74 crosscheck families, **41 hand Lean a structural
  attestation** — an axiom pair it cannot fail on the merits. The gate reported
  one undifferentiated total; it now prints both halves and floors the
  *reasoning* one, because flooring the sum lets reasoning be swapped for
  attestation with the headline unmoved. `qf_bv` was one of the 41: not a defect
  but a **width**, since enumeration beats bit-blasting below ~16 bits.
  `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation).
- **My own claim.** I wired the e-matching route to `Evidence` and shipped
  `certified=1` on evidence whose independent re-check said FAIL. Reverted, then
  fixed properly: the certificate is portable now — instances are rebuilt in the
  checker's arena rather than trusted by `TermId`, and the ground set is rebuilt
  rather than stored. One/two/four instances all `certified=1 arena=ok`.

**Next.** Carry the skolemisation record so a skolemised refutation can certify
(unblocked now that portability is solved); that closes `F:barber-no-such-barber`
and with it every query whose top-level existentials are eliminated. Then A6's
remainder: split the 38 QF_BV bare-UNSAT rows by route provenance.

**Two standing cautions for anyone quoting these numbers.** `certified=` and Lean
reconstruction are *independent axes* — a fact can be certified with no Lean
module, and 41 of 74 Lean-checked families prove nothing about their proposition
— so the two must never be summed. And `just check` is red independently of this
lane: `check-plan-authority.py` budgets the `PLAN.md` sources at 52 KB and they
were already 57 KB before this lane existed.

<!-- plan-section: landed-changes -->

| 2026-08-17 | `07ffe852` | The e-matching route certifies AND survives an independent re-parse: instances rebuilt in the checker's arena rather than trusted by `TermId`, ground set rebuilt rather than stored (making "nothing smuggled in" structural). One/two/four instances `certified=1 arena=ok`, against `arena=FAIL` for the last two before. Reinstates `a1493099` after `9853fb6c` reverted it. |
| 2026-08-17 | `3cc574c7` | Both counted proof-production errors closed (A6 first slice): `int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, so `produce_evidence` lost a verdict `check_auto` decides in 0.13ms. Now declines to `unsat` / `unsat-uncertified`. |
| 2026-08-17 | `e97db72b` | `check-parity-docs.py` crashed before running a single check — it runs in `just check`, not CI, so the preferred aggregate gate failed for everyone as a traceback. Fixing it exposed 14 real failures; 2 mine, 12 other lanes' and now visible. |
| 2026-08-17 | `2c535667` | CI's representative-crosscheck grep still pinned `families=73`; the new family made it 74. Invisible to every local gate. |
| 2026-08-17 | `9853fb6c` | REVERTED `a1493099` — it claimed `certified=1` on evidence whose independent re-check FAILED. Adds `tests/certified_implies_revalidatable.rs`: `is_certified()` must imply `Verified` against an independently re-parsed arena, which per-variant suites structurally cannot enforce. |
| 2026-08-17 | `c2365718` | QF_BV reaches Lean as reasoning: `qf_bv_wide` runs the theorem at `BitVec(16)`, where bit-blasting actually owns it, asserting a theory reconstruction rather than mere acceptance. Split 32 → 33 theory families; both floors raised. |
| 2026-08-17 | `4cd5d6f0` | The Lean gate reports both halves of its headline and floors the reasoning one, verified under real Lean 4.30.0. Three guards each driven to fail. Corrects the `qf_bv` doc comment, which claimed a bit-level refutation type-checks in Lean. |
| 2026-08-17 | `c5f4c04b` | The Lean content split is measured, printed per family, and ratcheted both ways: 41 structural / 32 theory families, 72 / 95 modules, classified from rendered module source so no `lean` binary is needed. |
| 2026-08-17 | `28755674` | The e-matching driver can report the instances that justified an `unsat`, with a checker that replays each derivation, rejects unlicensed ground members, and re-refutes the ground set. Fourth capture site found by measurement — the smallest query refutes through the online CDCL(T) session. |
| 2026-08-17 | `078b2776` | Every `ProofFragment`'s Lean content class pinned by name. 5 of 61 were pinned before; moving `QfBv` to the attestation arm now gives 1163 passed / 1 failed, and the one is this test. |
| 2026-08-17 | `502c0503` | Settled SMT-route facts gated on certification, not just verdict: 17 of 17 report `certified=1`, enforced rather than assumed. Seven guards, each mutation-tested to kill exactly one test. |

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

| 2026-08-17 | `ae13cd6e` | A kernel fact's `depends_on` is DERIVED from the proof term, not transcribed: `Kernel::theorem_dependencies` keeps the half of the constant closure `axiom_footprint` discards. 18 edges were missing — two of them on facts proved the same day, by hand. Isolation 65 → 62. Restraints pinned by tests; the vacuity floor had no test until mutation-checking found it killed zero. |
| 2026-08-17 | `07ffe852` `9853fb6c` `28755674` | The e-matching route certifies, on the third design. It first shipped `certified=1` on evidence whose independent re-check said FAIL (one instance passed by `TermId` coincidence, two did not); reverted, then made portable — instances rebuilt in the checker's arena, ground set rebuilt rather than stored. `tests/certified_implies_revalidatable.rs` is the guard that caught it and now licenses it. |
| 2026-08-17 | `c2365718` `4cd5d6f0` `c5f4c04b` `078b2776` | The Lean gate stops overstating: 41 of 74 crosscheck families hand Lean an `axiom P` shim, so the headline is split, the reasoning half floored, and every fragment's class pinned by name. `qf_bv` was a WIDTH, not a defect — enumeration beats bit-blasting below ~16 bits — so `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation). |
| 2026-08-17 | `3cc574c7` `502c0503` | Both counted proof-production errors closed (`int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, losing a verdict `check_auto` decides in 0.13ms), and settled SMT-route facts gated on certification rather than verdict — 17 of 17, enforced. |
| 2026-08-17 | `ea9500bc` `e97db72b` `2c535667` `f40f7dc4` | Gate repairs: `check-parity-docs.py` crashed before running a single check (hiding 14 failures); CI's crosscheck grep still pinned 73 families; and `PLAN.md`'s sources were 24 KB over a 52 KB budget, journal moved to result notes. |

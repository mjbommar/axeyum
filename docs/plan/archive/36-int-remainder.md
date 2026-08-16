# Lane: int-remainder — the `subNatNat` borrow, and the last of the integer axioms

<!-- plan-section: lane-status -->

**Lane state (`WIP`, int-remainder, 2026-08-15).** `integer` went **6 axioms →
1**. `Int.add_assoc`, `Int.mul_assoc`, `Int.left_distrib`, `Int.add_le_add` and
`Int.add_lt_add_of_le_of_lt` are theorems; only
`Int.euclidean_decomposition` is still asserted. `int_theorem_inventory` reports
**50 derived, 50 with an EMPTY `axiom_footprint`, 1 still asserted**.

The blocker the previous lane named was real and was one obstruction, not four:
`Int.subNatNat` is a `Nat.rec` on `n − m`, stuck whenever its arguments are
variables, and every mixed-sign branch of `Int.add` is one. The development that
unblocks it is three steps — the shift lemma
`subNatNat (m+k) (n+k) = subNatNat m n` (induction on `k` over two rewrites by
`Nat.succ_sub_succ`, one for the value and one for the scrutinee, which sit in
different holes); the anchors `subNatNat m 0 = ofNat m` and
`subNatNat 0 k = negOfNat k`, whose shifts are the two characterisations; and
`Int.subNatNat_elim`, which turns `Nat.le_total` + `Nat.le_dest` into a
two-branch case analysis on which constructor the borrow lands in. 25 reusable
lemmas, all with empty footprints.

Two findings worth carrying. `mul_assoc` never needed the borrow at all — it is
blocked by a stuck `negOfNat` under `Int.mul`, which four two-case lemmas
unstick, and then it is eight branches of `Nat.mul_assoc`. And the two additive
**order** laws are proved with **no `Int.rec` in the proof term**: `le a b` iff
`b = a + ofNat i` (`Int.le_dest` / `Int.le_ofNat_add`), so sixteen structural
branches over a stuck `Int.add` become one ring rearrangement over `add_assoc`.
Replacing a case-defined relation by its witness is the transferable move.

Controls held. `nat_theorem_inventory` is **byte-identical**: 119 theorems, diff
clean, `nat: axiom=0 opaque=0 quotient=0`. `cargo test -p axeyum-lean-kernel`
green (249 lib + every integration suite); clippy `-D warnings` clean. **A real
Lean 4.30.0 kernel read the grown export** — the thing the previous lane flagged
as not done: `scripts/check-lean-gate.sh` reports `12 suites, 49 tests, 112
real-Lean checks (floor 105)`, green. The Diophantine golden module hash moved
(1,049,867 → 1,142,494 bytes) and was updated by a script that parses the value
the failing test printed, because the previous lane got that constant wrong by
typing it. Seven integer facts landed and replay: `kernel-lean 30/30 re-derived`
under `check-fact-evidence-replay.sh`.

`tests/axiom_footprint.rs` had built its composite witness out of
`Int.add_assoc` and `Int.mul_assoc`; both are theorems now, so an integer-only
composite is no longer constructible and that suite reaches into `arith` to keep
testing an exact closure rather than "return the root and stop".

Next: `Int.euclidean_decomposition` is a **different kind of problem** and is why
this lane stopped. Every law discharged here is an equation or inequality between
terms already in the language, so the work was making definitions reduce. This
one asserts the existence of two integers the language cannot name, so it needs
`Int.div`/`Int.mod` defined and specified — a new definition with its own
recursion, not another rewriting lemma. The `Nat` side already has
`div_mod_exists`, `div_mod_unique`, `mod_lt` and a certified executable
`Nat.divMod`; the interesting case is negative dividends, where Euclidean
rounding is not truncation and the sign convention must be defended by the
`0 ≤ r < k` bound rather than assumed. `Int.le_dest` and `Int.subNatNat_elim`
are both directly useful there.

Full reasoning, including the three `symm`-direction bugs and why `ExprId`s in
kernel errors cost more than the proofs did:
[`docs/mathematics-2026-08/diary-int-remainder.md`](../../mathematics-2026-08/diary-int-remainder.md).

<!-- plan-section: landed-changes -->

| 2026-08-15 | `0fc7cc357` | `Int.subNatNat`'s borrow proved (shift lemma, two characterisations, elimination principle) and five of the six remaining integer axioms discharged: `add_assoc`, `mul_assoc`, `left_distrib`, `add_le_add`, `add_lt_add_of_le_of_lt`. `integer: axiom=6 → 1`; 50 `Int` theorems, all with an empty axiom footprint; real-Lean gate green at 112 checks. |

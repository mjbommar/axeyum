# Lane: fo-diagonal — the round trip carries its fuel, and Leibniz needed no induction

<!-- plan-section: lane-status -->

**The decoder round trip is proved; the self-fuelled wrapper is REFUTED, not
merely unproved** (`WIP`, fo-diagonal, 2026-09-05). Thirteen new checked,
axiom-free declarations in `crates/axeyum-lean-kernel/src/fo_roundtrip.rs`:
`FO.Term.size`, `FO.Formula.size`, `FO.Term.decode_code`,
`FO.Formula.decode_code` and their `Nat.zero_add` corollaries
`*.decode_code_at_size`; then `FO.Code.substCodeAux` with
`FO.Code.substCodeAux_commutes` (the commuting lemma),
`FO.Code.isFormulaCodeAux` with `FO.Code.isFormulaCodeAux_code`, and
`FO.Term.numeral`, `FO.Code.diagAux`, `FO.Code.diagAux_code`. Plus, additively,
`FO.Provable`'s **seventeenth** constructor `eqf_subst` — the Leibniz rule —
with its soundness minor; `FO.soundness` and `FO.consistency` stay green and
axiom-free.

ADR-1640 made three predictions about the round trip's cost. **Two were right
and one was false in a way only building it could show.** The fuel goes on the
LEFT of the `Nat.add` (`Nat.add` recurses right, so `Nat.add f (Nat.succ x)`
ι-reduces and the recursive call's fuel *is* the induction hypothesis's — the
mutation putting it on the right makes the kernel reject the theorem); each of
the thirteen minors does cost one transport along `FO.Code.fst_pair`, because
`FO.Code.fst (FO.Code.pair 4 x)` is not definitionally `4` when `unpair` of a
symbolic code is stuck. But item (3), `Nat.le (size p) (code p)` for the
self-fuelled `decode n := decodeAux n n`, is **false**: `FO.Formula.code
FO.Formula.bot` and `FO.Term.code (FO.Term.var 0)` are both `Nat.zero` while
both sizes are `1`, pinned by `def_eq`. So every downstream theorem is stated
at EXPLICIT fuel — `substCodeAux`, `isFormulaCodeAux`, `diagAux` — and the
self-fuelled wrappers stay untheoremed. `F:fo-formula-decoder` therefore stays
`open`, with its remaining route rewritten from "prove the size bound" to
"strong induction on the code via `Nat.lt (FO.Code.snd n) n`", which needs
`FO.Code.tri` monotonicity and a well-founded `Nat` recursion.

**ADR-1636's estimate for the Leibniz rule was also wrong, and in our favour.**
It recorded that the soundness case needed "a fifth induction over
`FO.Formula`". It needs none. `FO.sat_inst` already reduces `sat (φ[t]) w` to
`sat φ (Val.cons M (Term.eval M S t w) w)`, in which the term appears ONLY as
the value `Term.eval M S t w` — a valuation entry, not a subterm — so the minor
is `sat_inst` forward, one `Eq.rec` at the motive `fun x => sat p (Val.cons M x
w)`, and `sat_inst` backward. The rule is stated with the substitution on both
sides for exactly this reason; a form with `s` occurring literally inside `φ`
would have needed the predicted induction. The general lesson: a cost estimate
for a soundness case is a claim about **where the syntax appears in the
semantics**, and the substitution lemma had already moved it.

**The provability-level diagonal lemma did NOT land**, and the obstruction is a
strand rather than a step: `Γ_Q` has to *prove* `diag m̄ = ⌜δ⌝`, i.e. the
diagonal function must be representable in Q. Three things are missing and none
is proof-term engineering — nothing in `fo_*.rs` relates `FO.Provable` to a
computation on `Nat` in either direction (there is no "`Nat.beq a b = true` →
`Provable Γ_Q (eqf ā b̄)`", the base case of Σ₁-completeness, and `Γ_Q` is not
written down as an `FO.Context`); `FO.Formula` has no `Iff` connective; and
representing `diag` means Σ₁-defining `FO.Code.pair`, `tri`, `unpair` and the
fuel recursion. Gödel I was not attempted. What DID land is the arithmetization
half, `FO.Code.diagAux_code : diag ⌜p⌝ = ⌜p(⌜p⌝)⌝`, which is one application of
the commuting lemma.

One measured hazard worth carrying forward: **the diagonal is not evaluable in
this kernel at any genuine code.** Numerals are unary, and `diagAux (code p)`
contains `FO.Term.code (FO.Term.numeral (FO.Formula.code p))`. At the smallest
formula with a free variable — `FO.Formula.eqf (var 0) (var 0)`, code `2` — the
diagonalised code is over ten million; at `FO.Formula.rel1 0 (var 0)` (code `5`)
the first draft of the evaluation test **overflowed the stack**, measured on
this host. `FO.Code.diagAux` is therefore pinned by `def_eq` at three FREE
variables, which is pure δ/β, with a negative control that its fourth argument
is the code of the *numeral* of `n` and not `n`. A later lane should not read
the absence of a concrete evaluation test as an oversight, and should not expect
"just compute δ and check it" to be an available shortcut.

Detail and the sizing of each obstruction:
[ADR-1648](../../research/09-decisions/adr-1648-the-round-trip-carries-its-fuel-and-leibniz-needed-no-induction.md).

Mutation evidence, both RUN against a 12-test green baseline: the round trip's
fuel moved to the right of the `Nat.add` killed **12 of 12** with
`TypeMismatch`; the commuting lemma with `FO.Formula.code p` and `FO.Term.code
t` swapped in `substCodeAux`'s argument list killed **12 of 12** with
`DeclarationValueMismatch`. Both are mass kills through the fixture, because a
rejected declaration fails `build_fo_roundtrip_prelude` and every test builds
it — that is honest but weak evidence about any individual test, which is why
the shape guards (`eqf_subst_consumes_the_equality_and_moves_the_instance`,
`subst_code_aux_actually_substitutes`,
`diag_aux_is_subst_code_aux_at_the_formulas_own_numeral`,
`size_is_not_bounded_by_the_code`) each carry their own negative control built
from a specific wrong variant.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `24a055abf` | The arithmetization half of the diagonal lemma: `FO.Term.numeral`, `FO.Code.diagAux`, `FO.Code.diagAux_code` (`diag ⌜p⌝ = ⌜p(⌜p⌝)⌝`). Records the measured fact that the diagonal is NOT evaluable at any genuine code — unary numerals put `eqf (var 0) (var 0)`'s diagonalised code over ten million and `rel1 0 (var 0)`'s past the stack — so `diagAux` is pinned symbolically. |
| 2026-09-05 | `b6d2de455` | The commuting lemma at explicit fuel (`FO.Code.substCodeAux_commutes`), the image lemma (`FO.Code.isFormulaCodeAux_code`), and `FO.Provable`'s seventeenth constructor `eqf_subst` — the Leibniz rule — with its soundness minor. ADR-1636's "needs a fifth induction over `FO.Formula`" was wrong: `FO.sat_inst` puts the term in as a VALUE, so the case is one `Eq.rec`. |
| 2026-09-05 | `752e3c483` | `fo_roundtrip.rs`: `FO.Term.size`, `FO.Formula.size` and the fuel-additive decoder round trip for both carriers, with the fuel on the LEFT of the `Nat.add`. Also the measurement that `Nat.le (size x) (code x)` is FALSE at `FO.Term.var 0` and `FO.Formula.bot`, which is why nothing downstream is stated at the self-fuelled wrappers. |

/-!
# `Axeyum.Shim` — the name-correspondence layer, proved in Lean

Axeyum's kernel has its own ℕ (`AxNat` — the `Ax` is *axeyum*, and it is not
axiomatized) and its own prelude lemmas. A term the `ring` / `linarith`
producers emit references those names, **fully applied with every argument
explicit**, in axeyum's own argument order. Lean core has lemmas of the same
mathematical content, but with different implicitness and, in several cases, a
different argument order.

So a rename is not enough. This file is one Lean theorem per emitted axeyum
constant, stated with **exactly** axeyum's signature (all arguments explicit,
in axeyum's order, spelled with `Nat.add` / `Nat.mul` / `Nat.le` rather than
notation so the correspondence is visible in the source) and **proved from
Lean core**. Nothing here is an axiom and nothing is `sorry`; `Tests/`
asserts that with `#print axioms`.

That makes the file the correspondence table *and* its own check: if a row is
wrong, Lean refuses this file and the gate is red before any tactic runs.

Three grades appear below and are recorded in ADR-1666:

* **`exact`** — Lean core has the same statement with the same argument order,
  and the shim is the core constant applied to its own arguments.
* **`reordered`** — Lean core has the statement, but with a different
  argument order or different implicitness; the shim permutes.
* **`derived`** — Lean core has no single constant with this statement; the
  shim proves it.

Numerals are deliberately absent: axeyum emits `Nat.succ (Nat.succ Nat.zero)`
for `2`, never an `OfNat` literal, so no numeral shim is needed.
-/

namespace Axeyum.Shim

/-! ## ℕ ordering -/

/-- axeyum `AxNat.le.refl : (a : AxNat) → AxNat.le a a`. Grade: **reordered**
(Lean's `Nat.le.refl` takes `n` implicitly). -/
theorem natLeRefl (a : Nat) : Nat.le a a := Nat.le.refl

/-- axeyum `AxNat.le_trans : (a b c : AxNat) → a ≤ b → b ≤ c → a ≤ c`.
Grade: **reordered** (Lean's `Nat.le_trans` takes `n m k` implicitly). -/
theorem natLeTrans (a b c : Nat) (h₁ : Nat.le a b) (h₂ : Nat.le b c) :
    Nat.le a c := Nat.le_trans h₁ h₂

/-- axeyum `AxNat.le_add_right : (a b : AxNat) → a ≤ a + b`.
Grade: **exact** (`Nat.le_add_right (n k : Nat) : n ≤ n + k`). -/
theorem natLeAddRight (a b : Nat) : Nat.le a (Nat.add a b) := Nat.le_add_right a b

/-- axeyum `AxNat.add_le_add_left : (k m n : AxNat) → m ≤ n → k + m ≤ k + n`.
Grade: **reordered** (Lean's `Nat.add_le_add_left {m n} (h) (k)` puts the
proof before the added constant and both bounds implicit). -/
theorem natAddLeAddLeft (k m n : Nat) (h : Nat.le m n) :
    Nat.le (Nat.add k m) (Nat.add k n) := Nat.add_le_add_left h k

/-- axeyum `AxNat.add_le_add_right : (k m n : AxNat) → m ≤ n → m + k ≤ n + k`.
Grade: **reordered**, same reason as `natAddLeAddLeft`. -/
theorem natAddLeAddRight (k m n : Nat) (h : Nat.le m n) :
    Nat.le (Nat.add m k) (Nat.add n k) := Nat.add_le_add_right h k

/-- axeyum `AxNat.le_of_add_le_add_right : (k m n : AxNat) → m + k ≤ n + k → m ≤ n`.
Grade: **reordered** (Lean's `Nat.le_of_add_le_add_right {k n m}` takes all
three implicitly and infers them from the hypothesis). -/
theorem natLeOfAddLeAddRight (k m n : Nat) (h : Nat.le (Nat.add m k) (Nat.add n k)) :
    Nat.le m n := Nat.le_of_add_le_add_right h

/-! ## ℕ ring laws -/

/-- axeyum `AxNat.add_comm`. Grade: **exact**. -/
theorem natAddComm (a b : Nat) : Nat.add a b = Nat.add b a := Nat.add_comm a b

/-- axeyum `AxNat.add_assoc`. Grade: **exact**. -/
theorem natAddAssoc (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add a (Nat.add b c) := Nat.add_assoc a b c

/-- axeyum `AxNat.add_right_comm : (a b c) → a + b + c = a + c + b`.
Grade: **exact** (`Nat.add_right_comm (n m k : Nat) : n + m + k = n + k + m`). -/
theorem natAddRightComm (a b c : Nat) :
    Nat.add (Nat.add a b) c = Nat.add (Nat.add a c) b := Nat.add_right_comm a b c

/-- axeyum `AxNat.mul_comm`. Grade: **exact**. -/
theorem natMulComm (a b : Nat) : Nat.mul a b = Nat.mul b a := Nat.mul_comm a b

/-- axeyum `AxNat.mul_assoc`. Grade: **exact**. -/
theorem natMulAssoc (a b c : Nat) :
    Nat.mul (Nat.mul a b) c = Nat.mul a (Nat.mul b c) := Nat.mul_assoc a b c

/-- axeyum `AxNat.left_distrib : (a b c) → a * (b + c) = a * b + a * c`.
Grade: **exact**. -/
theorem natLeftDistrib (a b c : Nat) :
    Nat.mul a (Nat.add b c) = Nat.add (Nat.mul a b) (Nat.mul a c) :=
  Nat.left_distrib a b c

/-- axeyum `AxNat.right_distrib : (a b c) → (a + b) * c = a * c + b * c`.
Grade: **exact**. -/
theorem natRightDistrib (a b c : Nat) :
    Nat.mul (Nat.add a b) c = Nat.add (Nat.mul a c) (Nat.mul b c) :=
  Nat.right_distrib a b c

end Axeyum.Shim

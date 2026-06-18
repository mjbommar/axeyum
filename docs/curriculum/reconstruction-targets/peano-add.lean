/- Peano addition reconstruction target (Lean 4 sketch).
   The destination for the SMT `unknown`s in `peano-add.smt2`: these universals
   are proved by INDUCTION, which a proof assistant (Lean) checks and an SMT
   solver cannot decide. Aligns with Software Foundations in Lean
   (see ../foundational-books/proof-assistants.md). Proofs are `sorry`'d — this
   is a TARGET, not a finished artifact. -/

namespace ReconstructionTarget

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

def add : Nat → Nat → Nat
  | Nat.zero,   n => n
  | Nat.succ m, n => Nat.succ (add m n)

/-- Right identity: `add n zero = n`. Proof: induction on `n`. -/
theorem add_zero (n : Nat) : add n Nat.zero = n := by
  sorry

/-- Commutativity: `add m n = add n m`. Proof: induction (with `add_zero` and a
    `succ` lemma). -/
theorem add_comm (m n : Nat) : add m n = add n m := by
  sorry

end ReconstructionTarget

import Mathlib.Data.Nat.ModEq

/-!
An empty-footprint behaviour-contract family for seven still-`open`
`natural-modular-equivalence` propositions in the Axeyum fact ledger.

Every public `Nat` remainder lemma in this environment carries `propext`
(measured: `Nat.mod_zero`, `Nat.mod_eq_of_lt`, `Nat.add_mod`,
`Nat.mod_mod_of_dvd`, `Nat.mod_self` all do; `Nat.gcd_rec` additionally
carries `Quot.sound`), and the imported-candidate transport route requires an
EMPTY axiom footprint. So the remainder recurrence is rebuilt here directly
over `Nat.mod`, `Nat.modCore` and `Nat.modCore.go` — the same technique, and
the same first four spine theorems, as
`scripts/lean/autogenesis_nat_mod_remainder_contract_v2.lean` — and every
congruence law below is derived from that recurrence by structural induction
on an explicit fuel parameter. The only imported facts used are the
`Nat.add_*`/`Nat.le_*`/`Nat.lt_*`/`Nat.mul_*` order and ring lemmas and
`Nat.mod_lt`, each of which is independently axiom-free in this environment.

No declaration here cites the Mathlib theorem it is a candidate for
(`Nat.mod_modEq`, `Nat.modEq_one`, `Nat.ModEq.add_left`,
`Nat.ModEq.add_right`, `Nat.ModEq.of_dvd`, `Nat.ModEq.of_mul_left`,
`Nat.ModEq.of_mul_right`). That is not asserted by this comment: the
mechanical circularity audit in
`crates/axeyum-lean-import/examples/imported_candidate_transport_probe.rs`
re-derives it over `Kernel::declaration_dependency_closure`.
-/

namespace Axeyum.Autogenesis.Candidate.NatModEqCongruence

/-! ### Spine: the `Nat.mod` recurrence, rebuilt without `propext` -/

theorem modCoreGoFuelCongr
    (x y fuel₁ fuel₂ : Nat)
    (hy : 0 < y)
    (h₁ : x < fuel₁)
    (h₂ : x < fuel₂) :
    Nat.modCore.go y hy fuel₁ x h₁ = Nat.modCore.go y hy fuel₂ x h₂ := by
  match fuel₁, fuel₂ with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | Nat.succ fuel₁, Nat.succ fuel₂ =>
    simp only [Nat.modCore.go]
    split
    next => rw [modCoreGoFuelCongr]
    next => rfl
termination_by structural fuel₁

theorem modCoreEq (x y : Nat) : Nat.modCore x y =
    if 0 < y ∧ y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  split
  next hy =>
    rw [Nat.modCore.go]
    split
    next hle =>
      rw [if_pos ⟨hy, hle⟩]
      apply modCoreGoFuelCongr
    next hnle =>
      rw [if_neg (fun pair => hnle pair.2)]
  next hzero =>
    rw [if_neg (fun pair => hzero pair.1)]

theorem modCoreEqMod (n m : Nat) : Nat.modCore n m = n % m := by
  change Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
    rw [modCoreEq]
    exact if_neg fun ⟨hlt, hle⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
    rw [Nat.mod.eq_def]
    dsimp
    refine iteInduction (fun _ => rfl) (fun h => ?false)
    rw [modCoreEq]
    exact if_neg fun ⟨_hlt, hle⟩ => h hle

/-- The remainder recurrence, the one primitive every law below rests on. -/
theorem modRec (x y : Nat) : x % y =
    if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [← modCoreEqMod x y, ← modCoreEqMod (x - y) y, modCoreEq]

theorem addSubCancelRight (n m : Nat) : n + m - m = n := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.sub_zero]
  | succ m ih =>
    rw [Nat.add_succ, Nat.succ_sub_succ_eq_sub, ih]

/-! ### Base consequences of the recurrence -/

/-- A zero modulus is the identity. -/
theorem modZero (x : Nat) : x % 0 = x := by
  rw [modRec]
  exact if_neg fun pair => Nat.lt_irrefl 0 pair.1

/-- Below the modulus the remainder is the argument itself. -/
theorem modOfLt {x y : Nat} (h : x < y) : x % y = x := by
  rw [modRec]
  exact if_neg fun pair => Nat.lt_irrefl x (Nat.lt_of_lt_of_le h pair.2)

/-- Adding the modulus on the right does not move the remainder. -/
theorem addModRight (x z : Nat) : (x + z) % z = x % z := by
  cases z with
  | zero => rw [Nat.add_zero]
  | succ z =>
    rw [modRec]
    rw [if_pos ⟨Nat.zero_lt_succ _, Nat.le_add_left _ _⟩]
    rw [addSubCancelRight]

/-- Adding the modulus on the left does not move the remainder. -/
theorem addModLeft (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm]
  exact addModRight z x

/-! ### Candidate: `Nat.mod_modEq` -/

/-- Reducing a remainder again changes nothing. -/
theorem modModSelf (a n : Nat) : a % n % n = a % n := by
  cases n with
  | zero => rw [modZero a]; exact modZero a
  | succ n => exact modOfLt (Nat.mod_lt a (Nat.zero_lt_succ n))

/-! ### Candidate: `Nat.modEq_one` -/

theorem modOne (a : Nat) : a % 1 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.mod_lt a Nat.one_pos))

theorem modEqOne (a b : Nat) : a % 1 = b % 1 := by
  rw [modOne a, modOne b]

/-! ### Candidates: `Nat.ModEq.add_left` and `Nat.ModEq.add_right` -/

/-- Structural-fuel form of the additive normalisation below. -/
theorem addModCongrFuel :
    ∀ (fuel n c a : Nat), a ≤ fuel → (c + a) % n = (c + a % n) % n
  | 0, n, c, a, h => by
    have ha : a = 0 := Nat.eq_zero_of_le_zero h
    subst ha
    cases n with
    | zero => rw [modZero 0]
    | succ n => rw [modOfLt (Nat.zero_lt_succ n)]
  | fuel + 1, n, c, a, h => by
    cases n with
    | zero => rw [modZero a]
    | succ n =>
      rcases Nat.lt_or_ge a (n + 1) with hlt | hge
      · rw [modOfLt hlt]
      · obtain ⟨k, hk⟩ := Nat.le.dest hge
        subst hk
        have hkle : k ≤ fuel := by
          have hstep : n + 1 + k = n + k + 1 := by
            rw [Nat.add_right_comm]
          rw [hstep] at h
          exact Nat.le_trans (Nat.le_add_left k n) (Nat.le_of_succ_le_succ h)
        have hshift : c + (n + 1 + k) = c + k + (n + 1) := by
          rw [Nat.add_comm (n + 1) k, ← Nat.add_assoc]
        rw [addModLeft (n + 1) k, hshift, addModRight (c + k) (n + 1)]
        exact addModCongrFuel fuel (n + 1) c k hkle

/-- Reducing the varying summand before adding does not move the remainder. -/
theorem addModCongr (n c a : Nat) : (c + a) % n = (c + a % n) % n :=
  addModCongrFuel a n c a (Nat.le_refl a)

/-- Candidate for `Nat.ModEq.add_left`. -/
theorem addLeft (n a b c : Nat) (h : a % n = b % n) :
    (c + a) % n = (c + b) % n := by
  rw [addModCongr n c a, addModCongr n c b, h]

/-- Candidate for `Nat.ModEq.add_right`. -/
theorem addRight (n a b c : Nat) (h : a % n = b % n) :
    (a + c) % n = (b + c) % n := by
  rw [Nat.add_comm a c, Nat.add_comm b c]
  exact addLeft n a b c h

/-! ### Candidates: `Nat.ModEq.of_dvd`, `.of_mul_left`, `.of_mul_right` -/

/-- A left multiple of the modulus is invisible to the remainder. -/
theorem mulAddModLeft (m t k : Nat) : (m * t + k) % m = k % m := by
  induction t with
  | zero => rw [Nat.mul_zero, Nat.zero_add]
  | succ t ih =>
    have hstep : m * (t + 1) + k = m * t + k + m := by
      rw [Nat.mul_succ, Nat.add_right_comm]
    rw [hstep, addModRight (m * t + k) m, ih]

/-- Structural-fuel form of the divisor weakening below. -/
theorem modModOfMulFuel :
    ∀ (fuel m t a : Nat), a ≤ fuel → a % (m * t) % m = a % m
  | 0, m, t, a, h => by
    have ha : a = 0 := Nat.eq_zero_of_le_zero h
    subst ha
    cases Nat.eq_zero_or_pos (m * t) with
    | inl hz => rw [hz, modZero 0]
    | inr hp => rw [modOfLt hp]
  | fuel + 1, m, t, a, h => by
    cases Nat.eq_zero_or_pos (m * t) with
    | inl hz => rw [hz, modZero a]
    | inr hp =>
      rcases Nat.lt_or_ge a (m * t) with hlt | hge
      · rw [modOfLt hlt]
      · obtain ⟨k, hk⟩ := Nat.le.dest hge
        subst hk
        have hkle : k ≤ fuel := by
          have hp1 : 1 ≤ m * t := hp
          have hone : 1 + k ≤ fuel + 1 :=
            Nat.le_trans (Nat.add_le_add_right hp1 k) h
          have hk1 : k + 1 ≤ fuel + 1 := by
            rw [Nat.add_comm k 1]
            exact hone
          exact Nat.le_of_succ_le_succ hk1
        rw [addModLeft (m * t) k, mulAddModLeft m t k]
        exact modModOfMulFuel fuel m t k hkle

/-- `m ∣ n` makes the coarser remainder a function of the finer one. -/
theorem modModOfMul (m t a : Nat) : a % (m * t) % m = a % m :=
  modModOfMulFuel a m t a (Nat.le_refl a)

/-- Candidate for `Nat.ModEq.of_dvd`. -/
theorem ofDvd (m n a b : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  obtain ⟨t, ht⟩ := hmn
  subst ht
  rw [← modModOfMul m t a, ← modModOfMul m t b, h]

/-- Candidate for `Nat.ModEq.of_mul_left`. -/
theorem ofMulLeft (n a b m : Nat) (h : a % (m * n) = b % (m * n)) :
    a % n = b % n :=
  ofDvd n (m * n) a b ⟨m, Nat.mul_comm m n⟩ h

/-- Candidate for `Nat.ModEq.of_mul_right`. -/
theorem ofMulRight (n a b m : Nat) (h : a % (n * m) = b % (n * m)) :
    a % n = b % n :=
  ofDvd n (n * m) a b ⟨m, rfl⟩ h


/-! ### Candidates: `Nat.ModEq.add_left_cancel'` and `.add_right_cancel'` -/

/-- `Nat.add_left_cancel` rebuilt without `propext`. -/
theorem addLeftCancelNat : ∀ (n m k : Nat), n + m = n + k → m = k
  | 0, m, k, h => by
    rw [Nat.zero_add, Nat.zero_add] at h
    exact h
  | n + 1, m, k, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact addLeftCancelNat n m k (Nat.succ.inj h)

/-- Candidate for `Nat.ModEq.add_left_cancel'`. -/
theorem addLeftCancel (n a b c : Nat) (h : (c + a) % n = (c + b) % n) :
    a % n = b % n := by
  cases n with
  | zero =>
    rw [modZero (c + a), modZero (c + b)] at h
    rw [modZero a, modZero b]
    exact addLeftCancelNat c a b h
  | succ m =>
    have hstep := addLeft (m + 1) (c + a) (c + b) (c * m) h
    have hre : ∀ z : Nat, c * m + (c + z) = (m + 1) * c + z := by
      intro z
      rw [← Nat.add_assoc, Nat.succ_mul, Nat.mul_comm m c]
    rw [hre a, hre b, mulAddModLeft (m + 1) c a, mulAddModLeft (m + 1) c b]
      at hstep
    exact hstep

/-- Candidate for `Nat.ModEq.add_right_cancel'`. -/
theorem addRightCancel (n a b c : Nat) (h : (a + c) % n = (b + c) % n) :
    a % n = b % n := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact addLeftCancel n a b c h

/-! ### Candidate: `Nat.ModEq.dvd_iff` -/

/-- Zero has remainder zero under every modulus. -/
theorem zeroMod (d : Nat) : 0 % d = 0 := by
  cases d with
  | zero => exact modZero 0
  | succ d => exact modOfLt (Nat.zero_lt_succ d)

/-- A multiple has remainder zero. -/
theorem modEqZeroOfDvd (d a : Nat) (h : d ∣ a) : a % d = 0 := by
  obtain ⟨t, ht⟩ := h
  subst ht
  have hre : d * t = d * t + 0 := (Nat.add_zero _).symm
  rw [hre, mulAddModLeft d t 0, zeroMod d]

/-- Structural-fuel form of the converse. -/
theorem dvdOfModEqZeroFuel :
    ∀ (fuel d a : Nat), a ≤ fuel → a % d = 0 → d ∣ a
  | 0, d, a, hfuel, _ => by
    have ha : a = 0 := Nat.eq_zero_of_le_zero hfuel
    subst ha
    exact ⟨0, (Nat.mul_zero d).symm⟩
  | fuel + 1, d, a, hfuel, h => by
    cases Nat.eq_zero_or_pos d with
    | inl hz =>
      subst hz
      rw [modZero a] at h
      subst h
      exact ⟨0, (Nat.mul_zero 0).symm⟩
    | inr hp =>
      rcases Nat.lt_or_ge a d with hlt | hge
      · rw [modOfLt hlt] at h
        subst h
        exact ⟨0, (Nat.mul_zero d).symm⟩
      · obtain ⟨k, hk⟩ := Nat.le.dest hge
        subst hk
        have hkle : k ≤ fuel := by
          have hone : 1 + k ≤ fuel + 1 :=
            Nat.le_trans (Nat.add_le_add_right hp k) hfuel
          have hk1 : k + 1 ≤ fuel + 1 := by
            rw [Nat.add_comm k 1]
            exact hone
          exact Nat.le_of_succ_le_succ hk1
        rw [addModLeft d k] at h
        obtain ⟨t, ht⟩ := dvdOfModEqZeroFuel fuel d k hkle h
        subst ht
        exact ⟨t + 1, (Nat.add_comm d (d * t)).trans (Nat.mul_succ d t).symm⟩

/-- Divisibility is exactly a zero remainder. -/
theorem dvdOfModEqZero (d a : Nat) (h : a % d = 0) : d ∣ a :=
  dvdOfModEqZeroFuel a d a (Nat.le_refl a) h

/-- Candidate for `Nat.ModEq.dvd_iff`. -/
theorem dvdIff (m a b d : Nat) (h : a % m = b % m) (hd : d ∣ m) :
    d ∣ a ↔ d ∣ b := by
  have hab : a % d = b % d := ofDvd d m a b hd h
  exact Iff.intro
    (fun hda => dvdOfModEqZero d b (hab ▸ modEqZeroOfDvd d a hda))
    (fun hdb => dvdOfModEqZero d a (hab.symm ▸ modEqZeroOfDvd d b hdb))

end Axeyum.Autogenesis.Candidate.NatModEqCongruence


#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.modModSelf
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.modEqOne
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.addLeft
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.addRight
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.ofDvd
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.ofMulLeft
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.ofMulRight
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.addLeftCancel
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.addRightCancel
#print axioms Axeyum.Autogenesis.Candidate.NatModEqCongruence.dvdIff

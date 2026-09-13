/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Nilpotent

/-!
## 可解 Lie 代数に対する Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open Module LieAlgebra LieModule

variable {K 𝔰 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔰] [LieAlgebra K 𝔰] [FiniteDimensional K 𝔰]

-- 注意: 正標数では成り立たない。別ファイルの反例を参照。
public axiom LieIdeal.lieIdealOf_nilradical_eq_of_le (I : LieIdeal K 𝔰) (hN : nilradical K 𝔰 ≤ I) :
    nilradical K I = lieIdealOf (nilradical K 𝔰) I

variable [LieAlgebra.IsSolvable 𝔰]

variable (K 𝔰) in
public axiom LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian (n : ℕ)
    (h𝔫r : finrank K (𝔰 ⧸ nilradical K 𝔰) = n + 1) :
    ∃ 𝔞 : LieIdeal K 𝔰, finrank K (𝔞 ⧸ nilradical K 𝔞) = n ∧ nilradical K 𝔰 ≤ 𝔞

structure SolStepAdoData (K 𝔰 : Type*)
    [Field K] [CharZero K] [LieRing 𝔰] [LieAlgebra K 𝔰] [FiniteDimensional K 𝔰]
    [LieAlgebra.IsSolvable 𝔰] where
  protected 𝔞 : LieIdeal K 𝔰
  protected 𝔥 : LieSubalgebra K 𝔰
  nilradical_le_𝔞 : nilradical K 𝔰 ≤ 𝔞
  isCompl_toSubmodule : IsCompl 𝔞.toSubmodule 𝔥.toSubmodule
  [instIsAdo𝔞 : IsAdo K 𝔞]

public axiom SolStepAdoData.isAdo (D : SolStepAdoData K 𝔰) : IsAdo K 𝔰

public local instance LieAlgebra.IsAdo.of_isSolvable : IsAdo K 𝔰 := by
  generalize hn : finrank K (𝔰 ⧸ nilradical K 𝔰) = n
  induction n generalizing 𝔰 with
  | zero =>
    rw [LieIdeal.finrank_quotient, Nat.sub_eq_zero_iff_le, ← not_lt, LieIdeal.finrank_lt_iff,
      not_lt_top_iff, ← top_le_iff, ← LieIdeal.isNilpotent_iff_le_nilradical,
      LieRing.isNilpotent_lieIdeal_top_iff] at hn
    exact IsAdo.of_isNilpotent
  | succ n hin =>
    rsuffices ⟨D⟩ : Nonempty (SolStepAdoData K 𝔰)
    · exact D.isAdo
    obtain ⟨𝔞, hn𝔞, h𝔞⟩ := LieIdeal.exists_for_solStepAdoData_of_not_isLieAbelian K 𝔰 n hn
    specialize hin hn𝔞
    obtain ⟨𝔥, h𝔥₁⟩ : ∃ 𝔥 : LieSubalgebra K 𝔰, IsCompl 𝔞.toSubmodule 𝔥.toSubmodule := by
      obtain ⟨𝔥', h𝔥'⟩ := exists_isCompl 𝔞.toSubmodule
      simp_rw [← hn𝔞, LieIdeal.finrank_quotient, 𝔞.lieIdealOf_nilradical_eq_of_le h𝔞,
        LieIdeal.finrank_lieIdealOf _ _ h𝔞, ← Submodule.finrank_add_eq_of_isCompl h𝔥',
        LieIdeal.finrank_toSubmodule] at hn
      conv at hn => equals finrank K 𝔥' = 1 => grind only [LieIdeal.finrank_mono h𝔞]
      existsi 𝔥'.toLieSubalgebraOfDimOne hn
      exact h𝔥'
    exact ⟨{ 𝔞, 𝔥, nilradical_le_𝔞 := h𝔞, isCompl_toSubmodule := h𝔥₁ }⟩

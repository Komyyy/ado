/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Solvable

/-!
## 一般の場合の Ado の定理
-/

-- 公理を公開するために使用
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section Levi

open Function LieAlgebra

-- 正直もっと良い書き方があるかもしれないけど暫定的にこれで
public axiom LieHom.exists_levi_splitting (K 𝔤 : Type*)
    [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤] :
    ∃ (s : 𝔤 ⧸ radical K 𝔤 →ₗ⁅K⁆ 𝔤), LeftInverse LieIdeal.Quotient.mk s

end Levi

open Function LieAlgebra LieIdeal SemiDirectSum

variable {K 𝔤 : Type*}
variable [Field K] [CharZero K] [LieRing 𝔤] [LieAlgebra K 𝔤] [FiniteDimensional K 𝔤]

attribute [local instance] LieAlgebra.IsAdo.of_isSolvable_of_charZero in
public instance LieAlgebra.IsAdo.of_charZero : IsAdo K 𝔤 := by
  obtain ⟨s, hs⟩ := LieHom.exists_levi_splitting K 𝔤
  let ψ : 𝔤 ⧸ radical K 𝔤 →ₗ⁅K⁆ LieDerivation K (radical K 𝔤) (radical K 𝔤) :=
    LieHom.comp (LieDerivation.adIdeal (radical K 𝔤)) s
  let f : 𝔤 →ₗ[K] radical K 𝔤 :=
    show 𝔤 →ₗ[K] (radical K 𝔤).toSubmodule from
    LinearMap.codRestrict _ (LinearMap.id - (LieHom.comp s (LieIdeal.Quotient.mk' _)).toLinearMap)
      (by simp [← LieSubmodule.Quotient.mk_eq_zero, hs.eq])
  have hf x : (f x : 𝔤) = x - s (LieIdeal.Quotient.mk x) :=
    rfl
  let e : (radical K 𝔤 ⋊⁅ψ⁆ 𝔤 ⧸ radical K 𝔤) ≃ₗ⁅K⁆ 𝔤 :=
    { toLieHom := lift ψ (incl (radical K 𝔤)) s (by intro x; ext y; simp [ψ, - incl_coe])
      invFun x := ⟨f x, LieIdeal.Quotient.mk x⟩
      left_inv x := by ext <;> simp [hf, hs.eq, LieSubmodule.Quotient.mk_eq_zero'.mpr]
      right_inv x := by simp [hf] }
  have he x : e.symm x = ⟨f x, LieIdeal.Quotient.mk x⟩ := rfl
  rw [← e.isAdo_iff]
  apply IsAdo.semiDirectSum_of_isSolvable
  grw [← map_equiv_nilradical e.symm, map_le_iff_le_comap, nilradical_le_radical,
    IsConcreteLE.le_iff, Subtype.forall']
  simp +contextual [he, eq_comm (a := (0 : 𝔤 ⧸ radical K 𝔤))]

/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Ado.ForMathlib.LieIdealLieSubalgebra
public import Ado.ForMathlib.LieModuleRestr
public import Ado.ForMathlib.LieQuotient

public import Mathlib.Tactic.Replace

public section

open Filter Function
open LieSubmodule hiding eq_bot_iff

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

namespace LieModule

omit [LieModule R L M] in
@[gcongr]
lemma lowerCentralSeries_mono (m n : ℕ) (h : n ≤ m) :
    lowerCentralSeries R L M m ≤ lowerCentralSeries R L M n :=
  antitone_lowerCentralSeries R L M h

variable (R) in
lemma isNilpotent_iff_eventually :
    IsNilpotent L M ↔ ∀ᶠ (k : ℕ) in atTop, lowerCentralSeries R L M k = ⊥ := by
  rw [isNilpotent_iff R L M, eventually_atTop]
  congr! with k
  constructor
  case mpr => intro h; exact h k le_rfl
  intro hk n hn
  rw [eq_bot_iff] at hk ⊢
  grw [← hn, hk]

lemma isNilpotent_iff_eventually_int :
    IsNilpotent L M ↔ ∀ᶠ (k : ℕ) in atTop, lowerCentralSeries ℤ L M k = ⊥ :=
  isNilpotent_iff_eventually ℤ

lemma isNilpotent_of_lieIdeal_le_left (I₁ I₂ : LieIdeal R L) (h : I₁ ≤ I₂) [IsNilpotent I₂ M] :
    IsNilpotent I₁ M :=
  Function.Injective.lieModuleIsNilpotent (f := LieIdeal.inclusion h) (g := LinearMap.id)
    (by simp) injective_id

lemma _root_.LieRing.isNilpotent_of_lieIdeal_le (I₁ I₂ : LieIdeal R L) (h : I₁ ≤ I₂)
    [LieRing.IsNilpotent I₂] : LieRing.IsNilpotent I₁ :=
  (LieIdeal.inclusion_injective h).lieAlgebra_isNilpotent

@[congr]
lemma isNilpotent_lieIdeal_congr_left (I₁ I₂ : LieIdeal R L) (h : I₁ = I₂) :
    IsNilpotent I₁ M ↔ IsNilpotent I₂ M where
  mp _ := isNilpotent_of_lieIdeal_le_left I₂ I₁ h.ge
  mpr _ := isNilpotent_of_lieIdeal_le_left I₁ I₂ h.le

@[simp]
theorem isNilpotent_of_top_lieIdeal_iff :
    IsNilpotent (⊤ : LieIdeal R L) M ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff LieIdeal.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

lemma _root_.LieRing.isNilpotent_lieIdeal_top_iff :
    LieRing.IsNilpotent (⊤ : LieIdeal R L) ↔ LieRing.IsNilpotent L := by
  simp

variable (R) in
lemma nilpotencyLength_eq_iInf :
    nilpotencyLength L M = sInf {k | LieModule.lowerCentralSeries R L M k = ⊥} := by
  unfold nilpotencyLength
  congr! with n
  simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int]

variable (R) in
lemma nilpotencyLength_le_iff [IsNilpotent L M] {n} :
    nilpotencyLength L M ≤ n ↔ lowerCentralSeries R L M n = ⊥ := by
  classical
  simp_rw [nilpotencyLength_eq_iInf R,
    -- intentional defeq abuce, because `Nat.sInf_def` have defeq issue.
    Nat.sInf_def
      (show ∃ k, k ∈ {k | lowerCentralSeries R L M k = ⊥} from IsNilpotent.nilpotent R L M),
    Nat.find_le_iff, Set.mem_ofPred]
  constructor
  case mp =>
    rintro ⟨m, hm₁, hm₂⟩
    grw [eq_bot_iff, ← antitone_lowerCentralSeries R L M |>.imp hm₁, ← eq_bot_iff] at hm₂
    exact hm₂
  case mpr =>
    intro h
    exact ⟨n, le_rfl, h⟩

variable (R) in
@[simp]
lemma lowerCentralSeries_nilpotencyLength [IsNilpotent L M] :
    lowerCentralSeries R L M (nilpotencyLength L M) = ⊥ :=
  nilpotencyLength_le_iff R |>.mp le_rfl

variable (R) in
lemma list_prod_map_toEnd_apply_mem_lowerCentralSeries (l : List L) (m : M) :
    List.prod (List.map (toEnd R L M) l) m ∈ lowerCentralSeries R L M (List.length l) := by
  induction l with
  | nil => simp
  | cons x l hl => simp [LieSubmodule.lie_mem_lie, hl]

@[congr]
lemma isNilpotent_congr_left (L' L'' : LieSubalgebra R L) (h : L' = L'') :
    IsNilpotent L' M ↔ IsNilpotent L'' M :=
  Equiv.lieModule_isNilpotent_iff (LieEquiv.ofEq L' L'' (by simp [h])) (LinearEquiv.refl R M)
    (by simp)

instance (I : LieIdeal R L) [IsNilpotent L M] : IsNilpotent I M :=
  Function.Injective.lieModuleIsNilpotent (f := LieIdeal.incl I) (g := LinearMap.id)
    (by simp) injective_id

instance (L' : LieSubalgebra R L) [IsNilpotent L M] : IsNilpotent L' M :=
  Function.Injective.lieModuleIsNilpotent (f := LieSubalgebra.incl L') (g := LinearMap.id)
    (by simp) injective_id

instance (N : LieSubmodule R L M) [IsNilpotent L M] : IsNilpotent L N :=
  Function.Injective.lieModuleIsNilpotent (f := LieHom.id) (g := N.incl.toLinearMap)
    (by simp [- LieSubmodule.incl_coe]) N.injective_incl

instance (I : LieIdeal R L) [IsNilpotent I M] : IsNilpotent I.toLieSubalgebra M :=
  inferInstanceAs (IsNilpotent I M)

instance (L' : LieSubalgebra R L) (N : LieSubmodule R L M) [IsNilpotent L' M] : IsNilpotent L' N :=
  inferInstanceAs (IsNilpotent L' (N.restr L'))

instance (I : LieIdeal R L) (N : LieSubmodule R L M) [IsNilpotent I M] : IsNilpotent I N :=
  inferInstanceAs (IsNilpotent I.toLieSubalgebra N)

instance isNilpotent_sup_left (L' : LieSubalgebra R L) (I : LieIdeal R L)
    [IsNilpotent L' M] [IsNilpotent I M] : IsNilpotent ↥(L' ⊔ I.toLieSubalgebra) M := by
  suffices h : ∀ n,
      IsNilpotent ↥(L' ⊔ I.toLieSubalgebra) (I.lcs M n ⧸ comap (I.lcs M n).incl (I.lcs M (n + 1)))
  · rename IsNilpotent I M => hI
    change ∀ n,
      IsNilpotent ↥(L' ⊔ I.toLieSubalgebra)
        ((I.lcs M n).restr (L' ⊔ I.toLieSubalgebra) ⧸
          comap ((I.lcs M n).restr (L' ⊔ I.toLieSubalgebra)).incl
            ((I.lcs M (n + 1)).restr (L' ⊔ I.toLieSubalgebra))) at h
    simp_rw [isNilpotent_quotient_iff, lowerCentralSeries_eq_lcs_comap,
      ← LieSubmodule.map_le_iff_le_comap, LieSubmodule.map_comap_incl,
      inf_of_le_right (lcs_le_self _ _), lcs_le_iff] at h
    simp_rw [isNilpotent_iff R, ← toSubmodule_inj, ← LieIdeal.coe_lcs_eq,
      LieSubmodule.bot_toSubmodule, toSubmodule_eq_bot] at hI
    obtain ⟨k, hk⟩ := hI
    replace h : ∀ n ≤ k, ∃ m,
        (I.lcs M n).restr (L' ⊔ LieIdeal.toLieSubalgebra R L I) ≤
          ucs m ((I.lcs M k).restr (L' ⊔ LieIdeal.toLieSubalgebra R L I))
    · intro n hn
      induction hn using Nat.decreasingInduction with
      | self => existsi 0; simp
      | of_succ n hn hin =>
        specialize h n
        obtain ⟨m₁, hm₁⟩ := h
        obtain ⟨m₂, hm₂⟩ := hin
        existsi m₁ + m₂
        grw [hm₁, hm₂, ucs_add]
    specialize h 0 zero_le
    simp_rw [LieIdeal.lcs_zero, hk, restr_top, restr_bot, ← eq_top_iff,
      ← isNilpotent_iff_exists_ucs_eq_top] at h
    exact h
  intro n
  have hL' : IsNilpotent L' (I.lcs M n)
  · change IsNilpotent L' ((I.lcs M n).restr L')
    have : IsNilpotent L' (⊤ : LieSubmodule R L' M)
    · rw [isNilpotent_of_top_iff']; infer_instance
    refine isNilpotent_of_le _ _ _ _ ⊤ le_top
  replace hL' : IsNilpotent L' (I.lcs M n ⧸ comap (I.lcs M n).incl (I.lcs M (n + 1)))
  · change IsNilpotent L' (I.lcs M n ⧸ (comap (I.lcs M n).incl (I.lcs M (n + 1))).restr L')
    infer_instance
  have : IsTrivial I (I.lcs M n ⧸ comap (I.lcs M n).incl (I.lcs M (n + 1)))
  · constructor
    intro x a
    obtain ⟨a, rfl⟩ := LieSubmodule.Quotient.surjective_mk' _ a
    simp [lie_mem_lie]
  suffices h : ∀ k,
      (lowerCentralSeries R ↥(L' ⊔ I.toLieSubalgebra)
        (I.lcs M n ⧸ comap (I.lcs M n).incl (I.lcs M (n + 1))) k).toSubmodule =
        (lowerCentralSeries R L'
          (I.lcs M n ⧸ comap (I.lcs M n).incl (I.lcs M (n + 1))) k).toSubmodule
  · simp_rw [isNilpotent_iff R, ← toSubmodule_eq_bot, h, toSubmodule_eq_bot, ← isNilpotent_iff, hL']
  intro k
  induction k with
  | zero => simp
  | succ k hk =>
    simp_rw [lowerCentralSeries_succ, lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and,
      ← mem_toSubmodule, hk, mem_toSubmodule, SetLike.exists, LieSubalgebra.coe_bracket_of_module,
      exists_prop, ← (L' ⊔ I.toLieSubalgebra).mem_toSubmodule,
      LieSubalgebra.toSubmodule_sup_lieIdeal, Submodule.exists_mem_sup,
      LieSubalgebra.mem_toSubmodule, mem_toSubmodule, add_lie, ← exists_prop (a := _ ∈ I),
      Subtype.exists', ← LieIdeal.coe_bracket_of_module, trivial_lie_zero]
    simp

instance (I I' : LieIdeal R L) [IsNilpotent I M] [IsNilpotent I' M] : IsNilpotent ↥(I ⊔ I') M := by
  change IsNilpotent ↥(I ⊔ I').toLieSubalgebra M
  conv => equals IsNilpotent ↥(I.toLieSubalgebra ⊔ I'.toLieSubalgebra) M =>
    simp
  infer_instance

instance (I : LieIdeal R L) [LieRing.IsNilpotent I] : IsNilpotent I L := by
  suffices h : ∀ n, I.lcs L (n + 1) ≤ (I.lcs I n).map (LieSubmodule.incl I)
  · rename LieRing.IsNilpotent I => hI
    simp_rw [isNilpotent_iff R, ← LieSubmodule.toSubmodule_eq_bot, ← I.coe_lcs_eq,
      LieSubmodule.toSubmodule_eq_bot] at hI ⊢
    obtain ⟨k, hk⟩ := hI
    specialize h k
    grw [hk, LieSubmodule.map_bot, le_bot_iff] at h
    exists k + 1
  intro n
  induction n with
  | zero => simp [LieSubmodule.lie_le_left]
  | succ n hn =>
    grw [I.lcs_succ _ (n + 1), hn, I.lcs_succ, LieSubmodule.map_bracket_eq]

end LieModule

/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Data.Finset.NatAntidiagonal
public import Ado.ForMathlib.LieModuleShrink
public import Ado.ForMathlib.LieModuleNilpotent

/-!
## Ado の定理の主張
-/

section ForMathlib

public section LieModuleBracket

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

namespace LieSubmodule

@[simp]
lemma lie_finset_sup {ι} (I : LieIdeal R L) (s : Finset ι) (f : ι → LieSubmodule R L M) :
    ⁅I, s.sup f⁆ = s.sup (fun i ↦ ⁅I, f i⁆) := by
  classical
  induction s using Finset.induction <;> simp [*]

end LieSubmodule

end LieModuleBracket

public section Nilradical

open Finset.HasAntidiagonal

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **注意:** これは `maxNilpotentIdeal` とは異なります。`maxNilpotentIdeal` は最大の `L`-冪零イデアル
ですが、`nilradical R L = 𝔫` は最大の `𝔫`-冪零イデアルです。 -/
def nilradical : LieIdeal R L :=
  sSup {N | LieRing.IsNilpotent N}

variable {R L}

instance (L₁ L₂ : LieIdeal R L) [LieRing.IsNilpotent L₁] [LieRing.IsNilpotent L₂] :
    LieRing.IsNilpotent ↥(L₁ ⊔ L₂) := by
  have hlcs (L' : LieIdeal R L) :
      Antitone (fun n : ℕ ↦
        (n.casesAuxOn ⊤ (fun n ↦ (L'.lcs L' n).map (LieSubmodule.incl L')) : LieIdeal R L))
  · apply antitone_nat_of_succ_le
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp -iota [Nat.casesAuxOn_succ, LieSubmodule.map_le_map_iff (LieSubmodule.injective_incl L'),
        LieSubmodule.lie_le_right]
  suffices h : ∀ n, ((L₁ ⊔ L₂).lcs ↥(L₁ ⊔ L₂) n).map (LieSubmodule.incl (L₁ ⊔ L₂)) ≤
      (antidiagonal (n + 1)).sup (fun p ↦
        p.1.casesAuxOn ⊤ (fun n ↦ (L₁.lcs L₁ n).map (LieSubmodule.incl L₁)) ⊓
          p.2.casesAuxOn ⊤ (fun n ↦ (L₂.lcs L₂ n).map (LieSubmodule.incl L₂)))
  · rename LieRing.IsNilpotent L₁ => hL₁
    rename LieRing.IsNilpotent L₂ => hL₂
    simp_rw [LieModule.isNilpotent_iff R, ← LieSubmodule.toSubmodule_eq_bot,
      ← LieIdeal.coe_lcs_eq, LieSubmodule.toSubmodule_eq_bot] at hL₁ hL₂ ⊢
    obtain ⟨m, hm⟩ := hL₁
    obtain ⟨n, hn⟩ := hL₂
    specialize h (m + n)
    conv_rhs at h =>
      apply Finset.sup_congr
      · skip
      · tactic =>
          intro p hp
          rw [eq_bot_iff]
          replace hp :=
            mem_antidiagonal.mp hp |>.ge |> Nat.add_one_le_iff.mp |> lt_or_lt_of_add_lt_add
          simp_rw [Nat.lt_iff_add_one_le] at hp
          obtain (hp | hp) := hp
          · grw [(hlcs L₁).imp hp, Nat.casesAuxOn_succ, hm, LieSubmodule.map_bot, bot_inf_eq]
          · grw [(hlcs L₂).imp hp, Nat.casesAuxOn_succ, hn, LieSubmodule.map_bot, inf_bot_eq]
    rw [LieSubmodule.map_le_iff_le_comap, Finset.sup_bot] at h
    existsi m + n
    grw [eq_bot_iff, h, ← eq_bot_iff, LieSubmodule.comap_incl_eq_bot, inf_bot_eq]
  intro n
  induction n with
  | zero =>
    simp [Finset.Nat.antidiagonal_succ]
  | succ n hn =>
    grw [LieIdeal.lcs_succ, LieSubmodule.map_bracket_eq, hn, LieSubmodule.lie_finset_sup]
    simp_rw [LieSubmodule.sup_lie, ← Pi.sup_def, Finset.sup_sup, sup_le_iff]
    constructor <;>
      [rw [Finset.Nat.antidiagonal_succ (n + 1)]; rw [Finset.Nat.antidiagonal_succ' (n + 1)]]
    all_goals
      simp only [Finset.sup_cons, Nat.casesAuxOn_zero, top_inf_eq, inf_top_eq,
        Nat.casesAuxOn_succ _ _ (n + 1), Finset.sup_map, Function.comp_def,
        Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
        Nat.succ_eq_add_one, Function.Embedding.refl_apply]
      grw [← le_sup_right]
      apply Finset.sup_mono_fun
      rintro ⟨m, n⟩ hmn
      grw [LieSubmodule.lie_inf, Nat.casesAuxOn_succ]
      simp_rw [le_inf_iff]
      constructor
    next =>
      grw [inf_le_left]
      cases m <;>
        simp -iota [Nat.casesAuxOn_succ, LieSubmodule.map_bracket_eq, LieSubmodule.lie_le_left]
    next => grw [inf_le_right, LieSubmodule.lie_le_right]
    next => grw [inf_le_left, LieSubmodule.lie_le_right]
    next =>
      grw [inf_le_right]
      cases n <;>
        simp -iota [Nat.casesAuxOn_succ, LieSubmodule.map_bracket_eq, LieSubmodule.lie_le_left]

instance [IsNoetherian R L] : LieRing.IsNilpotent (nilradical R L) := by
  have hwf := WellFoundedGT.isSupClosedCompact (α := LieIdeal R L) inferInstance
  refine hwf {N | LieRing.IsNilpotent N} ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all only [Set.mem_ofPred] <;> infer_instance

end LieAlgebra

end Nilradical

end ForMathlib

public section

universe u

open LieAlgebra LieModule

namespace LieAlgebra

structure BundledAdoSpace (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] where
  mk' ::
  protected V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module K V]
  [instFiniteDimentional : FiniteDimensional K V]
  [instLieRingModule : LieRingModule 𝔤 V]
  [instLieModule : LieModule K 𝔤 V]
  [instIsFaithful : IsFaithful K 𝔤 V]
  [instIsNilpotentMaxNilpotentIdeal : IsNilpotent (maxNilpotentIdeal K 𝔤) V]

attribute [instance]
  BundledAdoSpace.instAddCommGroup
  BundledAdoSpace.instModule
  BundledAdoSpace.instFiniteDimentional
  BundledAdoSpace.instLieRingModule
  BundledAdoSpace.instLieModule
  BundledAdoSpace.instIsFaithful
  BundledAdoSpace.instIsNilpotentMaxNilpotentIdeal

@[expose]
noncomputable def BundledAdoSpace.mk {K : Type u} {𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (maxNilpotentIdeal K 𝔤) V] :
    BundledAdoSpace K 𝔤 :=
  haveI : Small.{u} V := Module.Finite.small K V
  { V := Shrink.{u} V }

class IsAdo (K : Type u) (𝔤 : Type*) [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] :
    Prop where
  nonempty_bundledAdoSpace : Nonempty (BundledAdoSpace K 𝔤)

lemma IsAdo.intro {K 𝔤 : Type*} [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [LieRingModule 𝔤 V]
    [LieModule K 𝔤 V] [IsFaithful K 𝔤 V] [IsNilpotent (maxNilpotentIdeal K 𝔤) V] : IsAdo K 𝔤 :=
  ⟨⟨.mk V⟩⟩

end LieAlgebra

def AdoSpace (K : Type u) (𝔤 : Type*)
    [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤] : Type u :=
  ia.nonempty_bundledAdoSpace.some.V

variable (K : Type u) (𝔤 : Type*)
variable [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤] [ia : IsAdo K 𝔤]

@[no_expose]
noncomputable instance : AddCommGroup (AdoSpace K 𝔤) :=
  inferInstanceAs (AddCommGroup ia.nonempty_bundledAdoSpace.some.V)

@[no_expose]
noncomputable instance : Module K (AdoSpace K 𝔤) :=
  inferInstanceAs (Module K ia.nonempty_bundledAdoSpace.some.V)

instance : FiniteDimensional K (AdoSpace K 𝔤) :=
  inferInstanceAs (FiniteDimensional K ia.nonempty_bundledAdoSpace.some.V)

@[no_expose]
noncomputable instance : LieRingModule 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (LieRingModule 𝔤 ia.nonempty_bundledAdoSpace.some.V)

instance : LieModule K 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (LieModule K 𝔤 ia.nonempty_bundledAdoSpace.some.V)

instance : IsFaithful K 𝔤 (AdoSpace K 𝔤) :=
  inferInstanceAs (IsFaithful K 𝔤 ia.nonempty_bundledAdoSpace.some.V)

instance : IsNilpotent (maxNilpotentIdeal K 𝔤) (AdoSpace K 𝔤) :=
  inferInstanceAs (IsNilpotent (maxNilpotentIdeal K 𝔤) ia.nonempty_bundledAdoSpace.some.V)

instance [LieRing.IsNilpotent 𝔤] : IsNilpotent 𝔤 (AdoSpace K 𝔤) := by
  simpa using (inferInstance : IsNilpotent (maxNilpotentIdeal K 𝔤) (AdoSpace K 𝔤))

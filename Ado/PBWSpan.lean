/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.ForMathlib.UniversalEnvelopingAlgebra
public import Mathlib.LinearAlgebra.TensorAlgebra.Basis
public import Mathlib.Order.CompletePartialOrder

public import Mathlib.Tactic.Have
public import Mathlib.Tactic.Replace

/-!
## 弱いPBW定理: 整列単項式は普遍被覆代数を生成する
-/

section PBWSpan

open Function List Module TensorAlgebra UniversalEnvelopingAlgebra
open Set hiding prod
open LinearMap hiding prod
open Submodule hiding prod
open TensorAlgebra renaming ι → ιₜ
open Finsupp hiding prod

variable {m R L : Type*} [LinearOrder m] [CommRing R] [LieRing L] [LieAlgebra R L]
variable (B : Basis m R L)

namespace List

end List

namespace UniversalEnvelopingAlgebra

set_option allowUnsafeReducibility true in
attribute [reducible] AlgHom.toLinearMap

attribute [- simp] TensorAlgebra.tprod_apply

attribute [local instance 100] LieRing.ofAssociativeRing

public lemma pbw_span : span R ((prod ∘ map (ι R ∘ B)) '' {l : List m | SortedLE l}) = ⊤ := by
  have ht : span R (range (prod ∘ map (ιₜ R ∘ B))) = ⊤
  · let Bₜ : Basis (List m) R (TensorAlgebra R L) :=
      Basis.reindex (Basis.tensorAlgebra B) FreeMonoid.toList
    have hbₜ l : Bₜ l = prod (map (ιₜ R ∘ B) l)
    · simp [Bₜ, Basis.tensorAlgebra, FreeAlgebra.basisFreeMonoid,
        FreeAlgebra.equivMonoidAlgebraFreeMonoid, ← prod_hom, comp_def]
    convert Bₜ.span_eq
    ext l
    simp [hbₜ]
  replace ht : span R (range (prod ∘ map (ι R ∘ B))) = ⊤
  · apply_fun Submodule.map (mkAlgHom R L).toLinearMap at ht
    simpa [comp_def, range_eq_top_of_surjective, mkAlgHom_surjective, Submodule.map_span,
      ← range_comp, ← prod_hom] using ht
  simp_rw [eq_top_iff, ← ht, span_le, range_subset_iff, Function.comp_apply, SetLike.mem_coe]
  suffices h : ∀ l : List m, ∃ x ∈ span R ((prod ∘ map (ι R ∘ B)) '' {l' | length l' < length l}),
      prod (map (ι R ∘ B) l) = prod (map (ι R ∘ B) (insertionSort (· ≤ ·) l)) + x
  · intro l
    induction hn : length l using Nat.strongRecOn generalizing l with
    | ind n hin =>
      subst hn
      replace hin l hl := hin (length l) hl l rfl
      specialize h l
      obtain ⟨x, hx, h⟩ := h
      rw [h]
      apply add_mem
      · apply mem_span_of_mem
        apply mem_image_of_mem
        simp [sortedLE_insertionSort]
      · refine mem_of_le_of_mem ?_ hx
        simp_rw [span_le, Set.subset_def, forall_mem_image, mem_ofPred]
        exact hin
  suffices h : ∀ (l : List m) (a : m),
      ∃ x ∈ span R ((prod ∘ map (ι R ∘ B)) '' {l' | length l' ≤ length l}),
        prod (map (ι R ∘ B) (orderedInsert (· ≤ ·) a l)) = prod (map (ι R ∘ B) (a :: l)) + x
  · intro l
    induction l with
    | nil => exists 0; simp
    | cons a l hil =>
      simp only [insertionSort_cons]
      replace hl := h (insertionSort (· ≤ ·) l) a
      obtain ⟨x, hx, hl⟩ := hl
      obtain ⟨y, hy, hil⟩ := hil
      existsi ι R (B a) * y - x
      constructor
      · replace hy := mul_mem_mul (mem_span_singleton_self (ι R (B a))) hy
        simp_rw [span_singleton_mul, smul_span, ← image_smul] at hy
        apply sub_mem <;> refine mem_of_le_of_mem ?_ (by assumption) <;> apply span_mono
        on_goal 2 => simp
        simp_rw [Set.subset_def, forall_mem_image, mem_ofPred, mem_image]
        intro l' hl'
        exists a :: l'
        simp [hl']
      simp_rw [hl, map_cons, comp_apply, prod_cons, hil]
      noncomm_ring
  intro l a
  induction l with
  | nil => existsi 0; simp
  | cons b l hil =>
    simp only [orderedInsert_cons]
    split_ifs with hab
    case pos => exists 0; simp
    case neg =>
      obtain ⟨x, hx, hil⟩ := hil
      exists ι R (B b) * x + ⁅ι R (B b), ι R (B a)⁆ * prod (map (ι R ∘ B) l)
      constructor
      · replace hx := mul_mem_mul (mem_span_singleton_self (ι R (B b))) hx
        simp_rw [span_singleton_mul, smul_span, ← image_smul] at hx
        apply add_mem
        · refine mem_of_le_of_mem ?_ hx
          apply span_mono
          simp_rw [Set.subset_def, forall_mem_image, mem_ofPred, mem_image]
          intro l' hl'
          exists b :: l'
          simp [hl']
        · conv_rhs =>
            equals ι R (linearCombination R B (B.repr ⁅B b, B a⁆)) * prod (map (ι R ∘ B) l) => simp
          conv_rhs => arg 1; apply apply_linearCombination _ (ι R).toLinearMap
          simp_rw [LieHom.coe_toLinearMap, mem_span_image_iff_linearCombination]
          conv_rhs =>
            -- 後で `linearCombination_mul` という補題に分けたい
            tactic => simp_rw [linearCombination_apply, sum_mul, ← linearCombination_apply]
          have hli : Injective ((· :: l) : m → List m) := fun _ _ _ ↦ by simp_all
          exists embDomain ⟨(· :: l), hli⟩ (B.repr ⁅B b, B a⁆)
          simp [comp_def, mem_supported, - ι_apply]
          simp [linearCombination_apply]
      simp_rw [map_cons, prod_cons, Function.comp_apply] at hil
      simp_rw [map_cons, Function.comp_apply, prod_cons, hil, LieRing.of_associative_ring_bracket]
      noncomm_ring

end UniversalEnvelopingAlgebra

end PBWSpan

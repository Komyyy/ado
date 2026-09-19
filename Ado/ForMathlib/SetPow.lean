/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Data.List.FinRange

public section

variable {α : Type*} [Monoid α]

open List
open scoped Pointwise

namespace Set

lemma mem_pow_iff_fin_prod {a} {s : Set α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ Fin.prod f = a := by
  simp_rw [mem_pow, Fin.prod_eq_prod_map_finRange, ← List.ofFn_eq_map,
    Equiv.subtypePiEquivPi.surjective.exists, Subtype.exists]
  simp [Equiv.subtypePiEquivPi]

lemma mem_pow_iff_list_prod {a} {s : Set α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ l : List α, length l = n ∧ (∀ x ∈ l, x ∈ s) ∧ List.prod l = a := by
  simp [mem_pow_iff_fin_prod, List.exists_iff_exists_tuple, ← List.ofFn_eq_map]

lemma pow_subset {s t : Set α} {n : ℕ} :
    s ^ n ⊆ t ↔ ∀ l : List α, length l = n → (∀ x ∈ l, x ∈ s) → List.prod l ∈ t := by
  grind only [= Set.subset_def, = mem_pow_iff_list_prod]

end Set

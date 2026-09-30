/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Artinian.Module
public import Ado.ForMathlib.LinearMapBasic
public import Ado.ForMathlib.SetMapsTo

public import Mathlib.Tactic.Have

public section

open Filter LinearMap Module Submodule
open Set hiding restrict range

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsArtinian R M] [IsNoetherian R M]

namespace LinearMap

-- Fitting の条件を満たす具体的な部分加群を記さないとLie加群に一般化出来ない。
theorem fitting_explicit (f : End R M) :
    letI N₀ := ⨆ n : ℕ, ker (f ^ n); letI N₁ := ⨅ n : ℕ, range (f ^ n)
    IsCompl N₀ N₁ ∧
      (∃ (hN₀ : MapsTo f N₀ N₀), IsNilpotent (restrict f hN₀)) ∧ BijOn f N₁ N₁ := by
  suffices h : ∀ᶠ n in (atTop : Filter ℕ),
      let N₀ : Submodule R M := ker (f ^ n); let N₁ : Submodule R M := range (f ^ n)
      IsCompl N₀ N₁ ∧ (∃ (hN₀ : MapsTo f N₀ N₀), IsNilpotent (restrict f hN₀.imp)) ∧ BijOn f N₁ N₁
  · apply (atTop : Filter ℕ).eventually_const.mp
    filter_upwards [h, f.eventually_iSup_ker_pow_eq, f.eventually_iInf_range_pow_eq]
      with n h hf₁ hf₂
    rw [hf₁, hf₂]
    exact h
  filter_upwards [f.eventually_isCompl_ker_pow_range_pow, f.eventually_iSup_ker_pow_eq,
    f.eventually_iInf_range_pow_eq]
  -- 仮定の順序を動かせるタクティックがないせいで、`refold_let` の処理がややこしい
  lift_lets
  intro n N₀ N₁ hnc hnk hnr
  refold_let N₀ N₁ at *
  exists hnc
  have hN₁r : map f N₁ = N₁
  · simp_rw +zetaDelta [← LinearMap.range_comp, ← End.iterate_succ']
    apply le_antisymm
    · simp_rw [End.iterate_succ, LinearMap.range_comp, ← Submodule.map_top,
        Submodule.map_mono le_top]
    · simp_rw +zetaDelta [← hnr, iInf_le]
  have hN₀k : ker f ≤ N₀
  · rw [← hnk]; apply le_iSup_of_le 1; simp
  have hN₁k : Disjoint N₁ (ker f)  := hnc.disjoint.symm.mono_right hN₀k
  constructor
  on_goal 2 =>
    rw [disjoint_ker_iff_injOn] at hN₁k
    convert ← hN₁k.bijOn_image
    simpa using congr(($hN₁r : Set M))
  have hN₀r : map f N₀ ≤ N₀
  · simp_rw +zetaDelta [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp, ← End.iterate_succ,
      End.iterate_succ', LinearMap.ker_comp, ← Submodule.comap_bot, Submodule.comap_mono bot_le]
  existsi map_le_iff_mapsTo.mp hN₀r
  apply IsNilpotent.mk _ n
  -- 先述の `Set.MapsTo.imp` が無いと単純化してくれない！
  simp +zetaDelta [← LinearMap.range_eq_bot, End.pow_restrict _, LinearMap.range_restrict]

theorem fitting (f : End R M) : ∃ (N₀ N₁ : Submodule R M), IsCompl N₀ N₁ ∧
    (∃ (hN₀ : MapsTo f N₀ N₀), IsNilpotent (restrict f hN₀.imp)) ∧ BijOn f N₁ N₁ :=
  ⟨⨆ n : ℕ, ker (f ^ n), ⨅ n : ℕ, range (f ^ n), f.fitting_explicit⟩

end LinearMap

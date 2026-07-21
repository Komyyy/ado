/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.TransferInstance

public section

-- TODO: 今見たけど `Function.Injective.addCommGroup` はまだ `NSMul` じゃなく `SMul ℕ` を使ってた
--       修正した方がいいかも ついでに `abbrev (reducible)` から `instance_reducible` にした方がいい

variable (R : Type*) {L₁ L₂ : Type*}

@[instance_reducible]
protected def Function.Injective.lieRing
    [Add L₁] [Zero L₁] [SMul ℕ L₁] [Neg L₁] [Sub L₁] [SMul ℤ L₁] [Bracket L₁ L₁] [LieRing L₂]
    (f : L₁ → L₂) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (bracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) : LieRing L₁ where
  __ := hf.addCommGroup f zero add neg sub nsmul zsmul
  add_lie x y z := hf <| by simp [*]
  lie_add x y z := hf <| by simp [*]
  lie_self x := hf <| by simp [*]
  leibniz_lie x y z := hf <| by simp [*]

@[instance_reducible]
protected def Function.Injective.lieAlgebra
    [CommRing R] [LieRing L₁] [SMul R L₁] [LieRing L₂] [LieAlgebra R L₂]
    (f : L₁ →+ L₂) (hf : Injective f) (smul : ∀ (c : R) (x), f (c • x) = c • f x)
    (bracket : ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆) : LieAlgebra R L₁ where
  __ := hf.module R f smul
  lie_smul t x y := hf <| by simp [*]

@[instance_reducible]
protected def Equiv.bracketSelf (e : L₁ ≃ L₂) [Bracket L₂ L₂] : Bracket L₁ L₁ where
  bracket x y := e.invFun ⁅e.toFun x, e.toFun y⁆

@[instance_reducible]
protected def Equiv.lieRing (e : L₁ ≃ L₂) [LieRing L₂] : LieRing L₁ := by
  let add := e.add
  let zero := e.zero
  let nsmul := e.smul ℕ
  let neg := e.Neg
  let sub := e.sub
  let zsmul := e.smul ℤ
  let bracket := e.bracketSelf
  apply e.injective.lieRing _ <;> intros <;> exact e.apply_symm_apply _

@[instance_reducible]
protected def Equiv.lieAlgebra (e : L₁ ≃ L₂) [CommRing R] [LieRing L₂]
    [LieAlgebra R L₂] : by
    let := e.lieRing
    exact LieAlgebra R L₁ := by
  let := e.lieRing
  let smul := e.smul R
  let bracket := e.bracketSelf
  refine e.injective.lieAlgebra R ⟨⟨e, ?_⟩, ?_⟩ ?_ ?_ <;> intros <;> exact e.apply_symm_apply _

def Equiv.lieEquiv (e : L₁ ≃ L₂) [CommRing R] [LieRing L₂]
    [LieAlgebra R L₂] : by
    let := e.lieRing
    let := e.lieAlgebra R
    exact L₁ ≃ₗ⁅R⁆ L₂ := by
  intros
  exact
    { e.linearEquiv R with
      map_lie' {x y} := e.symm.injective <| by
        simp [Equiv.linearEquiv, show ⁅x, y⁆ = e.symm ⁅e x, e y⁆ from rfl] }

-- これ自動で生成できるようにならないかな

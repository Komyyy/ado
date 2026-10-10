/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog
import AdoPage.Posts.SubobjectHell

open Verso Genre Blog AdoPage

set_option linter.unusedVariables false

#doc (Post) "Subobject Hell (en)" =>

%%%
authors := ["Miyahara Kō"]
date := {year := 2026, month := 10, day := 8}
categories := [english, proposal, aiTranslated]
%%%

```leanInit hellExample
```

> ⚠️ *CAUTION*

  This page was translated by Claude from Japanese. The original page is {page_link AdoPage.Posts.SubobjectHell}[HERE].

In this post, I (Miyahara Kō) write about a possible improvement to Mathlib that I noticed while formalizing Ado's theorem.

The phenomenon described here is the one that troubled me the most during the formalization.

It is easier to explain with a concrete example, so let us consider the following theorem in practice. It was actually formalized in this repository. ([link](../docs/Ado/ForMathlib/LieTheoremCorollary.html) — sorry if it is broken)

# A concrete example

Don't worry if you don't understand this section. It is enough to understand the formalization issue at the end.

I didn't understand it myself until I formalized it, after all.

> *Corollary of Lie's theorem*

  A finite-dimensional module $`V` over a solvable Lie algebra $`L` over an algebraically closed field of characteristic zero can be made upper triangular by choosing a suitable basis.

The proof uses Lie's theorem below.

> *Lie's theorem*

  For a nontrivial finite-dimensional module $`V` over a solvable Lie algebra $`L` over an algebraically closed field of characteristic zero, there exists a nonzero vector $`\lambda` in $`V` that is a common eigenvector for the actions of all elements of $`L` on $`V`.

The corollary can be proved by applying this theorem inductively to $`V`, $`V / \langle \lambda_0 \rangle`, $`V / \langle \lambda_0, \lambda_1 \rangle`, and so on.

Now, anyone who has used a proof assistant to some extent will know that inductive arguments like this are a common stumbling block in formalization. Let us carry the actual proof partway through.

```lean hellExample -keep
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  -- First, we use induction on the dimension of $`V`.
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    -- Handle the trivial case
    rw [finrank_eq_zero_iff_of_free] at hn
    simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
  | succ n hin =>
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    -- The dimension is positive, so `V` is nontrivial; hence we can take an eigenvector `v`.
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    -- Since `v` is an eigenvector, `V₀ := K ∙ v` is an `L`-module.
    let V₀ : LieSubmodule K L V :=
      { toSubmodule := K ∙ v
        lie_mem {x w} hw := by
          conv at hw => equals ∃ k : K, k • v = w => simp [Submodule.mem_span_singleton]
          obtain ⟨k, rfl⟩ := hw
          simp [hvw, smul_smul, SMulMemClass.smul_mem] }
    have hV₀ : finrank K V₀ = 1 := by
      simp [← finrank_toSubmodule, V₀, finrank_span_singleton hvz]
    replace hV₀ : finrank K (V ⧸ V₀) = n := by simp [hn, hV₀]
    -- Hence `V ⧸ V₀` is also an `L`-module, so by the induction hypothesis
    -- we get an upper triangular basis `b₀` of `V ⧸ V₀`.
    have hvq : (LieSubmodule.Quotient.mk v : V ⧸ V₀) = 0 := by simp [V₀]
    specialize hin (V ⧸ V₀) hV₀
    obtain ⟨b₀, hb₀⟩ := hin
    -- Also take the obvious basis `bᵥ` of `V₀`.
    let bᵥ : Basis Unit K V₀ :=
      Module.Basis.ofRepr
        ((LinearEquiv.coord K V v hvz).trans (Finsupp.uniqueLinearEquiv K K ()).symm)
    have hbv : (bᵥ () : V) = v := by simp [bᵥ, LinearEquiv.toSpanNonzeroSingleton]
    sorry
```

```leanInit hellExample2
```
```lean hellExample2 -show
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K L V) [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] (n) (V₀ : LieSubmodule K L V)
    (b₀ : Basis (Fin n) K (V ⧸ V₀)) (bᵥ : Basis Unit K V₀)
```

Now we want to lift the basis {lean hellExample2}`b₀` of {lean hellExample2}`V ⧸ V₀` to {lean hellExample2}`V` and combine it with the basis {lean hellExample2}`bᵥ` of {lean hellExample2}`V₀` to construct a basis of {lean hellExample2}`V`, but constructing it directly is tedious.

Just to confirm: {lean hellExample2}`V₀` is a submodule of the module `V` over the Lie algebra `L`, that is, a {lean hellExample2}`LieSubmodule K L V`, which is a special case of a submodule in the ordinary sense, {lean hellExample2}`Submodule K V`.

```lean hellExample2
recall LieSubmodule (R L M) [CommRing R] [LieRing L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] /- extends Submodule R M -/ : Type*

-- There is also a coercion.
example (W : LieSubmodule K L V) : Submodule K V := ↑W
```

Conveniently, Mathlib has a definition that builds a new basis by combining a basis of a submodule with a basis of the quotient, exactly as in the example above. It even comes with many simp lemmas.

```lean hellExample -keep
variable {R L V} [CommRing R] [AddCommGroup V] [Module R V]
variable {W : Submodule R V} {m n}

namespace Module.Basis

recall sumQuot (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) : Basis (m ⊕ n) R V

variable (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

-- The three simp lemmas we are going to use

recall sumQuot_inl (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) (i) :
    sumQuot bW bQ (Sum.inl i) = bW i

/- Note: since we are dealing with a quotient of a Lie module here, `LieSubmodule.Quotient.mk`
would be preferable to `Submodule.Quotient.mk`, but the former is just an abbreviation of the
latter anyway, so using it with `simp` should be fine... or so it should be...? -/
recall sumQuot_inr (j : n) :
    Submodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j

recall sumQuot_repr_inr (v : V) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j

end Module.Basis
```

Let us use it right away to prove the theorem.

```lean hellExample -show
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

macro "THE_PROOF_ABOVE" : tactic =>
  set_option hygiene false in `(tactic| (
    generalize hn : finrank K V = n
    induction' n with n hin generalizing V
    · rw [finrank_eq_zero_iff_of_free] at hn
      simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    -- Since `v` is an eigenvector, `V₀ := K ∙ v` is an `L`-module.
    let V₀ : LieSubmodule K L V :=
      { toSubmodule := K ∙ v
        lie_mem {x w} hw := by
          conv at hw => equals ∃ k : K, k • v = w => simp [Submodule.mem_span_singleton]
          obtain ⟨k, rfl⟩ := hw
          simp [hvw, smul_smul, SMulMemClass.smul_mem] }
    have hV₀ : finrank K V₀ = 1 := by
      simp [← finrank_toSubmodule, V₀, finrank_span_singleton hvz]
    replace hV₀ : finrank K (V ⧸ V₀) = n := by simp [hn, hV₀]
    -- Hence `V ⧸ V₀` is also an `L`-module, so by the induction hypothesis
    -- we get an upper triangular basis `b₀` of `V ⧸ V₀`.
    have hvq : (LieSubmodule.Quotient.mk v : V ⧸ V₀) = 0 := by simp [V₀]
    specialize hin (V ⧸ V₀) hV₀
    obtain ⟨b₀, hb₀⟩ := hin
    -- Also take the obvious basis `bᵥ` of `V₀`.
    let bᵥ : Basis Unit K V₀ :=
      Module.Basis.ofRepr
        ((LinearEquiv.coord K V v hvz).trans (Finsupp.uniqueLinearEquiv K K ()).symm)
    have hbv : (bᵥ () : V) = v := by simp [bᵥ, LinearEquiv.toSpanNonzeroSingleton]))

set_option linter.unusedSimpArgs false
```

```lean hellExample +error (name := hellExampleError)
public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  THE_PROOF_ABOVE
  -- To use the definition above, we need an equivalence identifying `Fin (n + 1)` with `Unit ⊕ Fin n`.
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
  -- Use the `Basis.sumQuot` from above here.
  let b := Basis.reindex (Basis.sumQuot bᵥ b₀) e
  existsi b
  intro x
  -- Preprocessing so that `simp` can finish the proof
  simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
  simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
  -- This should close the goal...!?
  simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]
```

The proof doesn't go through. Why? Let us look at the goal.

```leanOutput hellExampleError
unsolved goals
case succ
K : Type u_1
L : Type u_2
inst✝¹⁰ : Field K
inst✝⁹ : CharZero K
inst✝⁸ : IsAlgClosed K
inst✝⁷ : LieRing L
inst✝⁶ : LieAlgebra K L
inst✝⁵ : IsSolvable L
n : ℕ
V : Type u_3
inst✝⁴ : AddCommGroup V
inst✝³ : Module K V
inst✝² : LieRingModule L V
inst✝¹ : LieModule K L V
inst✝ : FiniteDimensional K V
hn : finrank K V = n + 1
hV : Nontrivial V
χ : Dual K L
v : V
hvw : ∀ (x : L), ⁅x, v⁆ = χ x • v
hvz : v ≠ 0
V₀ : LieSubmodule K L V :=
  let __Submodule := K ∙ v;
  { toSubmodule := __Submodule, lie_mem := ⋯ }
hV₀ : finrank K (V ⧸ V₀) = n
hvq : LieSubmodule.Quotient.mk v = 0
b₀ : Basis (Fin n) K (V ⧸ V₀)
bᵥ : Basis Unit K ↥V₀ := { repr := LinearEquiv.coord K V v hvz ≪≫ₗ (Finsupp.uniqueLinearEquiv K K ()).symm }
hbv : ↑(bᵥ ()) = v
e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
  (Equiv.sumComm Unit (Fin n)).trans ((Equiv.optionEquivSumPUnit (Fin n)).symm.trans (finSuccEquiv n).symm)
b : Basis (Fin (n + 1)) K V := (bᵥ.sumQuot b₀).reindex e
x : L
hb₀ : ∀ (x : L) ⦃i j : Fin n⦄, j < i → (b₀.repr ⁅x, b₀ j⁆) i = 0
⊢ ∀ (b b_1 : Fin n), b_1 < b → (b₀.repr (Submodule.Quotient.mk ⁅x, (bᵥ.sumQuot b₀) (Sum.inr b_1)⁆)) b = 0
```

The `sumQuot_inr` lemma from earlier should apply to this goal. What on earth is going on?

In fact, the problem is that {lean hellExample2}`↥V₀` and {lean hellExample2}`↥(↑V₀ : Submodule K V)` cannot be unified. In other words, it is caused by the coercion from modules over a Lie algebra (`LieSubmodule`) to ordinary modules (`Submodule`) appearing inside a type.

# Subobject hell

Let us tentatively call this kind of problem, where coercions between `SetLike` objects appear inside types and cause trouble, *Subobject hell*.

This problem was my biggest headache in proving Ado's theorem. When working with Lie algebras, the coercions `LieSubmodule K L V ⊆ Submodule K V` and `LieIdeal K L ⊆ LieSubalgebra K L ⊆ Submodule K V` come up constantly, and it is not unusual for them to appear inside types.

During the formalization, I made a small attempt to solve Subobject hell using Lean metaprogramming knowledge, but it remains unsolved to this day. Now that the formalization is finished, it might be a good time to tackle this problem seriously.

# Workaround

In the end, I worked around it by copy-pasting the definitions, as follows.

```lean hellExample -keep
variable {R L V} [CommRing R] [LieRing L] [AddCommGroup V] [Module R V] [LieRingModule L V]
variable {W : LieSubmodule R L V} {m n}

namespace Module.Basis

recall sumLieQuot (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) : Basis (m ⊕ n) R V :=
  sumQuot bW bQ

variable (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

recall sumLieQuot_inl (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) (i) :
    sumLieQuot bW bQ (Sum.inl i) = bW i

recall sumLieQuot_inr (j : n) :
    LieSubmodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j

recall sumLieQuot_repr_inr [LieAlgebra R L] [LieModule R L V] (v : V) (j : n) :
    (sumLieQuot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j

end Module.Basis
```

```lean hellExample
public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  THE_PROOF_ABOVE
  -- To use the definition above, we need an equivalence identifying `Fin (n + 1)` with `Unit ⊕ Fin n`.
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
  -- Use `Basis.sumLieQuot` instead of `Basis.sumQuot`.
  let b := Basis.reindex (Basis.sumLieQuot bᵥ b₀) e
  existsi b
  intro x
  simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
  simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
  simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]
  -- Q.E.D.
```

I'm thinking about whether this could be automated with a command.

# Closing remarks

Besides Subobject hell, I found many other possible improvements to Mathlib, and I would like to introduce them in blog posts like this one.

Personally, I think many of these improvements are metaprogramming problems, so I'm considering contributing metaprogramming-related work to Mathlib, deepening my knowledge of metaprogramming, and starting to review PRs with the t-meta label. (These are just plans, though.)

Also, this post is written in Verso, and you can see its source [here](https://github.com/Komyyy/ado/tree/master/AdoPage).

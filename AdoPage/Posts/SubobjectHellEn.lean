/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog
import AdoPage.Posts.SubobjectHell

open Verso Genre Blog AdoPage

set_option linter.unusedVariables false
set_option maxHeartbeats 300000
set_option maxRecDepth 10240

#doc (Post) "Subobject Hell (en)" =>

%%%
authors := ["Miyahara Kō"]
date := {year := 2026, month := 10, day := 8}
categories := [english, proposal, aiTranslated]
%%%

> ⚠️ *CAUTION*

  This page was translated by Claude from Japanese. The original page is {page_link AdoPage.Posts.SubobjectHell}[HERE].

# Correction

I found a serious mistake in what I wrote previously, which made it nonsensical, so feel free to forget the previous content!

::::html details

:::html summary
What was wrong
:::

```leanInit fixHell
```

In the previous content, I presented [this proof](../docs/Ado/ForMathlib/LieTheoremCorollary.html) as an example that fails.

```lean fixHell -keep
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    rw [finrank_eq_zero_iff_of_free] at hn
    simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
  | succ n hin =>
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    let V₀ : LieSubmodule K L V :=
      { toSubmodule := K ∙ v
        lie_mem {x w} hw := by
          conv at hw => equals ∃ k : K, k • v = w => simp [Submodule.mem_span_singleton]
          obtain ⟨k, rfl⟩ := hw
          simp [hvw, smul_smul, SMulMemClass.smul_mem] }
    have hV₀ : finrank K V₀ = 1 := by
      simp [← finrank_toSubmodule, V₀, finrank_span_singleton hvz]
    replace hV₀ : finrank K (V ⧸ V₀) = n := by simp [hn, hV₀]
    have hvq : (LieSubmodule.Quotient.mk v : V ⧸ V₀) = 0 := by simp [V₀]
    specialize hin (V ⧸ V₀) hV₀
    obtain ⟨b₀, hb₀⟩ := hin
    let bᵥ : Basis Unit K V₀ :=
      Module.Basis.ofRepr
        ((LinearEquiv.coord K V v hvz).trans (Finsupp.uniqueLinearEquiv K K ()).symm)
    have hbv : (bᵥ () : V) = v := by simp [bᵥ, LinearEquiv.toSpanNonzeroSingleton]
    let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
    let b := Basis.reindex (Basis.sumQuot bᵥ b₀) e
    existsi b
    intro x
    simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
    simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
    -- This was supposed to fail here
    simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]
```

```leanInit fixHell2
```
```lean fixHell2 -show
open Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K L V) [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] (n) (V₀ : LieSubmodule K L V)
    (b₀ : Basis (Fin n) K (V ⧸ V₀)) (bᵥ : Basis Unit K V₀)
```

I then explained that the cause of this failure was that {lean fixHell2}`↥V₀` and {lean fixHell2}`↥(↑V₀ : Submodule K V)` cannot be unified, in other words, that it was a problem caused by the coercion from modules over a Lie algebra (`LieSubmodule`) to ordinary modules (`Submodule`) appearing inside a type, and I named this phenomenon *Subobject Hell*.

However, the real cause was something else: I had previously written the following simp lemma in the wrong direction.

```lean fixHell
namespace LieSubmodule.Quotient

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M]
variable [Module R M] [LieRingModule L M] [LieAlgebra R L] [LieModule R L M]
variable (N : LieSubmodule R L M)

-- Correct:
recall mk_module_bracket (x : L) (m : M) :
    (LieSubmodule.Quotient.mk ⁅x, m⁆ : M ⧸ N) = ⁅x, LieSubmodule.Quotient.mk m⁆ :=
  rfl

-- Wrong:
lemma lie_bracket_mk (x : L) (m : M) :
    ⁅x, (LieSubmodule.Quotient.mk m : M ⧸ N)⁆ = LieSubmodule.Quotient.mk ⁅x, m⁆ :=
  rfl
```

The reason `lie_bracket_mk` above is in the wrong direction is that {lean fixHell}`(LieSubmodule.Quotient.mk : M → M ⧸ N)` has a bundled hom version, {lean fixHell}`(LieSubmodule.Quotient.mk' N : M →ₗ⁅R,L⁆ M ⧸ N)`, and this hom type (`LieModuleHom`) has the following simp lemma.

```lean fixHell
end LieSubmodule.Quotient

namespace LieModuleHom

variable {R L M N : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [LieRingModule L M] [LieRingModule L N] [LieAlgebra R L]
variable [LieModule R L M] [LieModule R L N]

recall map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆

end LieModuleHom
```

Therefore, making `lie_bracket_mk` a simp lemma breaks confluence and leads to unstable behavior.

The issue went away when I created the copied definitions below only because adding new simp lemmas changed the order in which simp lemmas are applied.

```lean fixHell -keep
namespace Module.Basis

variable {R L V} [CommRing R] [LieRing L] [AddCommGroup V] [Module R V] [LieRingModule L V]
variable {W : LieSubmodule R L V} {m n}

noncomputable def sumLieQuot (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) : Basis (m ⊕ n) R V :=
  sumQuot bW bQ

variable (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

@[simp]
axiom sumLieQuot_inl (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) (i) :
    sumLieQuot bW bQ (Sum.inl i) = bW i

@[simp]
axiom sumLieQuot_inr (j : n) :
    LieSubmodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j

@[simp]
axiom sumLieQuot_repr_inr [LieAlgebra R L] [LieModule R L V] (v : V) (j : n) :
    (sumLieQuot bW bQ).repr v (Sum.inr j) = bQ.repr (LieSubmodule.Quotient.mk' W v) j

end Module.Basis
```

In fact, after I deleted `lie_bracket_mk` and made `mk_module_bracket` a simp lemma instead, the first proof went through without the copied definitions above.

Please don't misunderstand: this doesn't mean that the phenomenon of *Subobject Hell* itself doesn't exist. In fact, in [ForMathlib.LieSemiDirectSum](../docs/Ado/ForMathlib/LieSemiDirectSum.html), which deals with semidirect sums of Lie algebras (put simply, the Lie algebra version of semidirect products of groups), defining the isomorphism between the internal and external semidirect sums the ordinary way fails, as shown below.

```leanInit fixHell3
```

```lean fixHell3 +error (name := fixHellError)
open LieHom LieSubalgebra LieDerivation

namespace LieAlgebra.SemiDirectSum

variable {R} [CommRing R] {L} [LieRing L] [LieAlgebra R L]
variable {I : LieIdeal R L} {L' : LieSubalgebra R L}

recall lieEquivLieSubalgebra (h : IsInnerSemiDirectSum I L') :
    (I ⋊⁅comp (adIdeal I) (incl L')⁆ L') ≃ₗ⁅R⁆ L where
  __ := LinearEquiv.trans (toProdl _) (Submodule.prodEquivOfIsCompl _ _ (by simp [h.isCompl]))
  map_lie' {x y} := by
    conv => equals
        ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ -
          ⁅y.right.1, x.left.1⁆ + ⁅x.right.1, y.right.1⁆ =
            ⁅x.left.1, y.left.1⁆ + ⁅x.right.1, y.left.1⁆ +
              (⁅x.left.1, y.right.1⁆ + ⁅x.right.1, y.right.1⁆) =>
      simp -- `Submodule.coe_prodEquivOfIsCompl'` is not applied
    grind only [=_ lie_skew]
```

```leanOutput fixHellError
unsolved goals
R : Type ?u.3
inst✝² : CommRing R
L : Type ?u.6
inst✝¹ : LieRing L
inst✝ : LieAlgebra R L
I : LieIdeal R L
L' : LieSubalgebra R L
h : IsInnerSemiDirectSum I L'
x y : ↥I ⋊⁅(adIdeal I).comp L'.incl⁆ ↥L'
⊢ ((↑I).prodEquivOfIsCompl L'.toSubmodule ⋯)
        (⁅↑x.left, y.left⁆ + ⁅↑x.right, y.left⁆ - ⁅↑y.right, x.left⁆, ⁅x.right, y.right⁆) =
      ⁅((↑I).prodEquivOfIsCompl L'.toSubmodule ⋯) (x.left, x.right),
        ((↑I).prodEquivOfIsCompl L'.toSubmodule ⋯) (y.left, y.right)⁆ ↔
    ⁅↑x.left, ↑y.left⁆ + ⁅↑x.right, ↑y.left⁆ - ⁅↑y.right, ↑x.left⁆ + ⁅↑x.right, ↑y.right⁆ =
      ⁅↑x.left, ↑y.left⁆ + ⁅↑x.right, ↑y.left⁆ + (⁅↑x.left, ↑y.right⁆ + ⁅↑x.right, ↑y.right⁆)
```

```lean fixHell3 -show
open LieHom LieSubalgebra LieDerivation

namespace LieAlgebra.SemiDirectSum

variable {R} [CommRing R] {L} [LieRing L] [LieAlgebra R L]
variable {I : LieIdeal R L} {L' : LieSubalgebra R L}
```

This problem is caused by the difference between {lean fixHell3}`↥I` and {lean fixHell3}`↥(↑I : Submodule R L)`, and between {lean fixHell3}`↥L'` and {lean fixHell3}`↥(↑L' : Submodule R L)`, showing up in the discrimination tree.

```lean fixHell3 (name := fixHellDiscrTree1)
#discr_tree_simp_key Submodule.coe_prodEquivOfIsCompl'
```

```leanOutput fixHellDiscrTree1
@DFunLike.coe
  (@LinearEquiv
     _
     _
     _
     _
     (RingHom.id _ _)
     _
     _
     _
     (Prod
        (@Subtype _ (@Membership.mem _ (Submodule _ _ _ _ _) _ _))
        (@Subtype _ (@Membership.mem _ (Submodule _ _ _ _ _) _ _)))
     _
     _
     _
     _
     _)
  (Prod
     (@Subtype _ (@Membership.mem _ (Submodule _ _ _ _ _) _ _))
     (@Subtype _ (@Membership.mem _ (Submodule _ _ _ _ _) _ _)))
  _
  _
  (@Submodule.prodEquivOfIsCompl _ _ _ _ _ _ _ _)
  _
```

In the key above, {lean fixHell3}`↥(?N₁ : Submodule R L) × ↥(?N₂ : Submodule R L)` appears as the `α` argument (and as part of the `F` argument) of {lean fixHell3}`(DFunLike.coe : Π {F α : Sort*} {β : α → Sort*} [inst : DFunLike F α β], F → Π (a : α), β a)`. However, in the failing example above, the left-hand side has the form {lean fixHell3}`DFunLike.coe (α := ↥I × ↥L') (Submodule.prodEquivOfIsCompl ↑I ↑L' ?_)`, and since {lean fixHell3}`↥I × ↥L'` and {lean fixHell3}`↥(↑I : Submodule R L) × ↥(↑L' : Submodule R L)` are not identified, the discrimination tree does not match and simp does not rewrite it. That is roughly the mechanism behind Subobject Hell.

With that in mind, let us look at the first proof again. The proof of the first theorem used to fail because `sumQuot_inr` and `sumQuot_repr_inr` were not applied. If this were due to Subobject Hell, their discrimination trees should contain a type of the form `{ x // x ∈ S }` (`@Subtype _ (@Membership.mem _ _ _ _)`).

```lean fixHell3 (name := fixHellDiscrTree2)
#discr_tree_simp_key Module.Basis.sumQuot_inr
```

```leanOutput fixHellDiscrTree2
@Submodule.Quotient.mk
  _
  _
  _
  _
  _
  _
  (@DFunLike.coe
     (Module.Basis (Sum _ _) _ _ _ _ _)
     (Sum _ _)
     _
     _
     (@Module.Basis.sumQuot _ _ _ _ _ _ _ _ _ _)
     (@Sum.inr _ _ _))
```

```lean fixHell3 (name := fixHellDiscrTree3)
#discr_tree_simp_key Module.Basis.sumQuot_repr_inr
```

```leanOutput fixHellDiscrTree3
@DFunLike.coe
  (Finsupp (Sum _ _) _ _)
  (Sum _ _)
  _
  _
  (@DFunLike.coe
     (@LinearEquiv _ _ _ _ (RingHom.id _ _) _ _ _ _ (Finsupp (Sum _ _) _ _) _ _ _ _)
     _
     _
     _
     (@Module.Basis.sumQuot _ _ _ _ _ _ _ _ _ _).1
     _)
  (@Sum.inr _ _ _)
```

As you can see, the discrimination trees of these lemmas do not contain `{ x // x ∈ S }`. This shows that the first example did not fail because of Subobject Hell.

Finally, why did I present the first example as an example of Subobject Hell? In the proof of Ado's theorem, the place where Subobject Hell caused the most trouble was actually the part involving internal semidirect sums of Lie algebras that I just introduced. However, this Subobject Hell problem was so severe that, at some point in the proof, I rewrote the lemmas about internal semidirect sums in terms of external semidirect sums. So, when I looked for a representative example of Subobject Hell among the proofs that remained, I picked the `LieModule.exists_basis_isUpperTriangular_of_isAlgClosed` lemma. As you now know, the problem with this lemma was something other than Subobject Hell.

It was a somewhat complicated example, so this got long. Thank you for taking the time to read this far!

::::

::::html details

:::html summary
Previous content (no need to read it!)
:::

In this post, I (Miyahara Kō) write about a possible improvement to Mathlib that I noticed while formalizing Ado's theorem.

The phenomenon described here is the one that troubled me the most during the formalization.

It is easier to explain with a concrete example, so let us consider the following theorem in practice. It was actually formalized in this repository. ([link](../docs/Ado/ForMathlib/LieTheoremCorollary.html) — sorry if it is broken)

*A concrete example*

Don't worry if you don't understand this section. It is enough to understand the formalization issue at the end.

I didn't understand it myself until I formalized it, after all.

> *Corollary of Lie's theorem*

  A finite-dimensional module $`V` over a solvable Lie algebra $`L` over an algebraically closed field of characteristic zero can be made upper triangular by choosing a suitable basis.

The proof uses Lie's theorem below.

> *Lie's theorem*

  For a nontrivial finite-dimensional module $`V` over a solvable Lie algebra $`L` over an algebraically closed field of characteristic zero, there exists a nonzero vector $`\lambda` in $`V` that is a common eigenvector for the actions of all elements of $`L` on $`V`.

The corollary can be proved by applying this theorem inductively to $`V`, $`V / \langle \lambda_0 \rangle`, $`V / \langle \lambda_0, \lambda_1 \rangle`, and so on.

Now, anyone who has used a proof assistant to some extent will know that inductive arguments like this are a common stumbling block in formalization. Let us carry the actual proof partway through.

```
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

Now we want to lift the basis `b₀` of `V ⧸ V₀` to `V` and combine it with the basis `bᵥ` of `V₀` to construct a basis of `V`, but constructing it directly is tedious.

Just to confirm: `V₀` is a submodule of the module `V` over the Lie algebra `L`, that is, a `LieSubmodule K L V`, which is a special case of a submodule in the ordinary sense, `Submodule K V`.

```
recall LieSubmodule (R L M) [CommRing R] [LieRing L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] /- extends Submodule R M -/ : Type*

-- There is also a coercion.
example (W : LieSubmodule K L V) : Submodule K V := ↑W
```

Conveniently, Mathlib has a definition that builds a new basis by combining a basis of a submodule with a basis of the quotient, exactly as in the example above. It even comes with many simp lemmas.

```
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

```
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

```
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

In fact, the problem is that `↥V₀` and `↥(↑V₀ : Submodule K V)` cannot be unified. In other words, it is caused by the coercion from modules over a Lie algebra (`LieSubmodule`) to ordinary modules (`Submodule`) appearing inside a type.

*Subobject hell*

Let us tentatively call this kind of problem, where coercions between `SetLike` objects appear inside types and cause trouble, *Subobject hell*.

This problem was my biggest headache in proving Ado's theorem. When working with Lie algebras, the coercions `LieSubmodule K L V ⊆ Submodule K V` and `LieIdeal K L ⊆ LieSubalgebra K L ⊆ Submodule K V` come up constantly, and it is not unusual for them to appear inside types.

During the formalization, I made a small attempt to solve Subobject hell using Lean metaprogramming knowledge, but it remains unsolved to this day. Now that the formalization is finished, it might be a good time to tackle this problem seriously.

*Workaround*

In the end, I worked around it by copy-pasting the definitions, as follows.

```
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
    (sumLieQuot bW bQ).repr v (Sum.inr j) = bQ.repr (LieSubmodule.Quotient.mk' W v) j

end Module.Basis
```

```
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

*Closing remarks*

Besides Subobject hell, I found many other possible improvements to Mathlib, and I would like to introduce them in blog posts like this one.

Personally, I think many of these improvements are metaprogramming problems, so I'm considering contributing metaprogramming-related work to Mathlib, deepening my knowledge of metaprogramming, and starting to review PRs with the t-meta label. (These are just plans, though.)

Also, this post is written in Verso, and you can see its source [here](https://github.com/Komyyy/ado/tree/master/AdoPage).

::::

Currently writing a new, corrected post...

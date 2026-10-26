/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog
import AdoPage.Categories
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Cases
import Ado.ForMathlib.LieSolvable
import Ado.ForMathlib.LieBaseChange
import Ado.ForMathlib.MatrixTriangular
import Ado.ForMathlib.LieSemiDirectSum

open Verso Genre Blog AdoPage

set_option linter.unusedVariables false
set_option maxHeartbeats 300000
set_option maxRecDepth 10240

#doc (Post) "Subobject Hell" =>

%%%
authors := ["Miyahara Kō"]
date := {year := 2026, month := 10, day := 8}
categories := [japanese, proposal]
%%%

# 訂正

以前書いた内容ですが、重大な誤りが見つかり、意味不明になってしまっていたので、以前の内容は忘れて構いません！

::::html details

:::html summary
誤りの内容
:::

```leanInit fixHell
```

以前の内容では、[こちらの証明](../docs/Ado/ForMathlib/LieTheoremCorollary.html)を失敗する例として提示していました。

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
    -- ここで失敗する予定だった
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

そしてこの失敗の原因を、{lean fixHell2}`↥V₀` と {lean fixHell2}`↥(↑V₀ : Submodule K V)` を統合できない事による、つまり、Lie 代数上の加群(`LieSubmodule`)から通常の加群(`Submodule`)への型強制が、型に現れる事によって起こった問題であると解説し、その現象を*Subobject Hell*と名付けました。

しかし本当の原因は別で、以前は以下の間違った向きのsimp補題を作っていた事が原因でした。

```lean fixHell
namespace LieSubmodule.Quotient

variable {R L M : Type*} [CommRing R] [LieRing L] [AddCommGroup M]
variable [Module R M] [LieRingModule L M] [LieAlgebra R L] [LieModule R L M]
variable (N : LieSubmodule R L M)

-- 正:
recall mk_module_bracket (x : L) (m : M) :
    (LieSubmodule.Quotient.mk ⁅x, m⁆ : M ⧸ N) = ⁅x, LieSubmodule.Quotient.mk m⁆ :=
  rfl

-- 誤:
lemma lie_bracket_mk (x : L) (m : M) :
    ⁅x, (LieSubmodule.Quotient.mk m : M ⧸ N)⁆ = LieSubmodule.Quotient.mk ⁅x, m⁆ :=
  rfl
```

何故上記の `lie_bracket_mk` が間違った向きなのかと言うと、{lean fixHell}`(LieSubmodule.Quotient.mk : M → M ⧸ N)` には bundled hom バージョンの {lean fixHell}`(LieSubmodule.Quotient.mk' N : M →ₗ⁅R,L⁆ M ⧸ N)` があり、この hom 型 (`LieModuleHom`) には、以下の simp 補題があります。

```lean fixHell
end LieSubmodule.Quotient

namespace LieModuleHom

variable {R L M N : Type*} [CommRing R] [LieRing L] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] [LieRingModule L M] [LieRingModule L N] [LieAlgebra R L]
variable [LieModule R L M] [LieModule R L N]

recall map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆

end LieModuleHom
```

ですので、`lie_bracket_mk` を simp 補題にすると、合流性が壊れ、不安定な挙動になってしまいます。

以下のコピー定義を作成した時に、事象が解決されたのも、新しい simp 補題が作成された事により、simp 補題の適用順序が変わった為です。

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

実際、`lie_bracket_mk` を削除し、`mk_module_bracket` を新しい simp 補題にしたら、上のコピー定義を使わなくても、最初の証明は通る様になりました。

誤解してほしくないのが、*Subobject Hell*という現象そのものが存在しない訳ではありません。実際、[ForMathlib.LieSemiDirectSum](../docs/Ado/ForMathlib/LieSemiDirectSum.html) という、Lie代数の半直積(分かりやすく言うと、群の半直積のLie代数バージョン)では、内部半直積と外部半直積の同型の定義では、以下の様に、普通にやれば失敗します。

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
      simp -- `Submodule.coe_prodEquivOfIsCompl'` が適用されない
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

この問題の原因は、{lean fixHell3}`↥I` と {lean fixHell3}`↥(↑I : Submodule R L)` の違い、及び{lean fixHell3}`↥L'` と {lean fixHell3}`↥(↑L' : Submodule R L)`が、判別木によって現れる事により起こります。

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

上記の失敗した例では、{lean fixHell3}`(DFunLike.coe : Π {F α : Sort*} {β : α → Sort*} [inst : DFunLike F α β], F → Π (a : α), β a)` の `α` の引数(及び `F` の引数の一部)に、{lean fixHell3}`↥(?N₁ : Submodule R L) × ↥(?N₂ : Submodule R L)` が出ています。ですが、先程の失敗した例では、左辺は {lean fixHell3}`DFunLike.coe (α := ↥I × ↥L') (Submodule.prodEquivOfIsCompl ↑I ↑L' ?_)` の形になっており、{lean fixHell3}`↥I × ↥L'` と {lean fixHell3}`↥(↑I : Submodule R L) × ↥(↑L' : Submodule R L)` が同一視されないため、判別木がマッチせず、simp により書き換えされないと言うのが、Subobject Hell の大体のメカニズムです。

それを踏まえた上で、最初の証明を見てみます。最初の定理の証明が以前失敗した理由は、`sumQuot_inr` と `sumQuot_repr_inr` が適用されないからでした。もしこれが Subobject Hell によるものなら、判別木に `{ x // x ∈ S }`(`@Subtype _ (@Membership.mem _ _ _ _)`) の型が含まれている筈です。

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

ご覧の通り、これらの補題の判別木に `{ x // x ∈ S }` は含まれていません。以上の事から、最初の例が以前失敗していたのは、Subobject Hell によるものではない事が分かります。

最後に、何故最初の例を Subobject Hell の例として紹介したのかというと、実は Ado の定理の証明において、Subobject Hell が一番問題になった箇所は、先程紹介した Lie 代数の内部半直積に関わる箇所でした。しかし、この Subobject Hell 問題が余りに深刻だったため、証明のある時点で、内部半直積に関する補題を、外部半直積を使って書き換えました。ですので、今残っている証明の中から、Subobject Hellの代表的な例を探そうと思って、最初の `LieModule.exists_basis_isUpperTriangular_of_isAlgClosed` 補題の例を使いました。ご存じの通り、この補題の問題は Subobject Hell とは別にありました。

少し複雑な例だったので、長くなってしまいました。ここまでわざわざ見てくれてありがとうございます！

::::

::::html details

:::html summary
以前の内容 (見なくて大丈夫です！)
:::

このページは、著者の宮原皓宇が、Adoの定理を形式化する際に気付いたMathlibの改善点を書き記したものです。

今回紹介する現象は、形式化に辺り、最も私を悩ませたものです。

具体例で示した方が分かりやすいので、実践として、以下の定理を考えます。これは実際にこのリポジトリで形式化されたものです。([リンク](../docs/Ado/ForMathlib/LieTheoremCorollary.html) 切れてたらごめん)

*具体例*

この章は意味が分からなくても全然大丈夫です。最後の形式化上の問題さえ理解すれば大丈夫です。

私も形式化するまでは理解していませんでしたので。

> *Lie の定理の系*

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の有限次元加群 $`V`、は、基底を選んで上三角行列に出来る。

証明には以下の、Lie の定理を使います。

> *Lie の定理*

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の非自明な有限次元加群 $`V` に対し、全ての $`L \to V` 作用に共通する $`V` の非零固有ベクトル $`\lambda` が存在する。

こちらの定理を、 $`V`, $`V / \langle \lambda_0 \rangle`, $`V / \langle \lambda_0, \lambda_1 \rangle` と、帰納的に使っていけば証明できます。

さて、証明支援系をある程度触った事がある人なら、この様な帰納的な議論が形式化で躓きやすいポイントである事が分かると思います。実際の証明を途中まで進めてみましょう。

```
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  -- 最初に、$`V` の次元に対する帰納法を使います。
  generalize hn : finrank K V = n
  induction n generalizing V with
  | zero =>
    -- 自明なケースを処理
    rw [finrank_eq_zero_iff_of_free] at hn
    simp [Subsingleton.eq_zero (α := Matrix (Fin 0) (Fin 0) K)]
  | succ n hin =>
    have hV : 0 < finrank K V := by lia
    rw [finrank_pos_iff] at hV
    -- 次元が正なので非自明、よって固有ベクトル `v` が取れる。
    obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L V
    conv at hχ => equals ∃ v ∈ weightSpace V χ, v ≠ 0 =>
      simp [nontrivial_iff_exists_ne (0 : weightSpace V χ)]
    obtain ⟨v, hvw, hvz⟩ := hχ
    rw [mem_weightSpace] at hvw
    -- `v` は固有ベクトルなので `V₀ := K ∙ v` は `L`-加群。
    let V₀ : LieSubmodule K L V :=
      { toSubmodule := K ∙ v
        lie_mem {x w} hw := by
          conv at hw => equals ∃ k : K, k • v = w => simp [Submodule.mem_span_singleton]
          obtain ⟨k, rfl⟩ := hw
          simp [hvw, smul_smul, SMulMemClass.smul_mem] }
    have hV₀ : finrank K V₀ = 1 := by
      simp [← finrank_toSubmodule, V₀, finrank_span_singleton hvz]
    replace hV₀ : finrank K (V ⧸ V₀) = n := by simp [hn, hV₀]
    -- よって `V ⧸ V₀` も `L`-加群。よって帰納法の仮定により、`V ⧸ V₀`上の上三角基底 `b₀` が取れる。
    have hvq : (LieSubmodule.Quotient.mk v : V ⧸ V₀) = 0 := by simp [V₀]
    specialize hin (V ⧸ V₀) hV₀
    obtain ⟨b₀, hb₀⟩ := hin
    -- `V₀` 上でも自明な基底 `bᵥ` を取っておく。
    let bᵥ : Basis Unit K V₀ :=
      Module.Basis.ofRepr
        ((LinearEquiv.coord K V v hvz).trans (Finsupp.uniqueLinearEquiv K K ()).symm)
    have hbv : (bᵥ () : V) = v := by simp [bᵥ, LinearEquiv.toSpanNonzeroSingleton]
    sorry
```

さて、今から、`V ⧸ V₀` 上の基底 `b₀` を `V` 上に持ち上げて、`V₀` 上の基底 `bᵥ` と組み合わせた基底を構成したいのですが、直接構成するのは面倒です。

ちなみに確認ですが、 `V₀` は Lie 代数 `L` 上の加群 `V` の部分加群、すなわち `LieSubmodule K L V` であり、これは通常の意味での部分加群 `Submodule K V` の、特別の場合です。

```
recall LieSubmodule (R L M) [CommRing R] [LieRing L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] /- extends Submodule R M -/ : Type*

-- 型強制もあります。
example (W : LieSubmodule K L V) : Submodule K V := ↑W
```

都合がいい事に、 Mathlib には、上記の例の様に、商上の基底を組み合わせて新しい基底を作る定義があります。しかも、多数の simp 補題もあります。

```
variable {R L V} [CommRing R] [AddCommGroup V] [Module R V]
variable {W : Submodule R V} {m n}

namespace Module.Basis

recall sumQuot (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) : Basis (m ⊕ n) R V

variable (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

-- 今回使う予定の3つの simp 補題

recall sumQuot_inl (bW : Basis m R W) (bQ : Basis n R (V ⧸ W)) (i) :
    sumQuot bW bQ (Sum.inl i) = bW i

/- 補足: 今回は Lie 加群の商なので、`Submodule.Quotient.mk` より `LieSubmodule.Quotient.mk` が
望ましいのだが、そもそも後者は前者の略語なので、`simp` で使う分には問題ない筈... なのだが...? -/
recall sumQuot_inr (j : n) :
    Submodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j

recall sumQuot_repr_inr (v : V) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j

end Module.Basis
```

早速これを使って定理を証明していきましょう。

```
public lemma LieModule.exists_basis_isUpperTriangular_of_isAlgClosed (K L V)
    [Field K] [CharZero K] [IsAlgClosed K] [LieRing L] [LieAlgebra K L] [IsSolvable L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] :
    ∃ b : Basis (Fin (finrank K V)) K V,
      ∀ x : L, IsUpperTriangular (toMatrix b b (toEnd K L V x)) := by
  THE_PROOF_ABOVE
  -- 先述の定義を使う為に、`Fin (n + 1)` を `Unit ⊕ Fin n` と見なす同型が必要。
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
  -- 先述の `Basis.sumQuot` をここで使用。
  let b := Basis.reindex (Basis.sumQuot bᵥ b₀) e
  existsi b
  intro x
  -- `simp` で終わらせる為の下処理
  simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
  simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
  -- 後はこれで通る筈なのだが...!?
  simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]
```

証明が通りません。何故でしょうか。ゴールを見てみましょう。

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

このゴールなら先程の `sumQuot_inr` 補題が使える筈です。一体何が起こっているのでしょうか。

実はこれは、`↥V₀` と `↥(↑V₀ : Submodule K V)` を統合できない事による、つまり、Lie 代数上の加群(`LieSubmodule`)から通常の加群(`Submodule`)への型強制が、型に現れる事によって起こった問題なのです。

*Subobject hell*

この様に、`SetLike` オブジェクト同士の型強制が型に現れて悪さをする問題を、 *Subobject hell* と暫定的に呼ぶ事にしましょう。

この問題は Ado の定理を証明する上で最大の悩みでした。というのも、Lie 代数を扱う時は、`LieSubmodule K L V ⊆ Submodule K V`, `LieIdeal K L ⊆ LieSubalgebra K L ⊆ Submodule K V` の型強制が頻発し、型に現れる事が珍しくないからです。

形式化の途中で、Lean のメタ知識を使って、この Subobject hell の解決をしようと少しだけ試みたのですが、今まで未解決のままです。形式化も終わりましたし、この問題に本腰を入れるのも良いかもしれません。

*対処法*

最終的に、以下の様に、定義をコピペする事で対処しました。

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
  -- 先述の定義を使う為に、`Fin (n + 1)` を `Unit ⊕ Fin n` と見なす同型が必要。
  let e : Unit ⊕ Fin n ≃ Fin (n + 1) :=
      (Equiv.sumComm _ _).trans <| (Equiv.optionEquivSumPUnit _).symm.trans <| (finSuccEquiv _).symm
  -- `Basis.sumQuot` ではなく `Basis.sumLieQuot` を使用。
  let b := Basis.reindex (Basis.sumLieQuot bᵥ b₀) e
  existsi b
  intro x
  simp_rw [Matrix.IsUpperTriangular, Matrix.BlockTriangular, id_eq, e.surjective.forall]
  simp only [IsUpperTriangular, BlockTriangular, id_eq, toMatrix_apply, toEnd_apply_apply] at hb₀
  simp +contextual [e, b, toMatrix_apply, hbv, hvw, hvq, hb₀]
  -- Q.E.D.
```

この辺り、コマンドで自動化出来ないかなと考えています。

*最後に*

今回の Subobject hell 以外にも、数多くの Mathlib の改善点が見つかったので、この様にブログ形式で紹介していきたいです。

それと個人的に、これらの改善点の多くはメタプログラミングの問題だと考えているので、今後 Mathlib へメタプログラミング関連の貢献をしたり、メタ知識をより深めて、レビューでt-metaタグのPRをレビューし始めようかなと考えています。(あくまで予定ですが)

それと、この記事は Verso で書かれており、ソースは[こちら](https://github.com/Komyyy/ado/tree/master/AdoPage)から見れます。

::::

現在、修正した新しい記事を執筆中...

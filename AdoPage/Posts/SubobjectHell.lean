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

open Verso Genre Blog AdoPage

set_option linter.unusedVariables false

#doc (Post) "Subobject Hell" =>

%%%
authors := ["Miyahara Kō"]
date := {year := 2026, month := 10, day := 8}
categories := [japanese, proposal]
%%%

```leanInit hellExample
```

このページは、著者の宮原皓宇が、Adoの定理を形式化する際に気付いたMathlibの改善点を書き記したものです。

今回紹介する現象は、形式化に辺り、最も私を悩ませたものです。

具体例で示した方が分かりやすいので、実践として、以下の定理を考えます。これは実際にこのリポジトリで形式化されたものです。([リンク](../docs/Ado/ForMathlib/LieTheoremCorollary.html) 切れてたらごめん)

# 具体例

この章は意味が分からなくても全然大丈夫です。最後の形式化上の問題さえ理解すれば大丈夫です。

私も形式化するまでは理解していませんでしたので。

> *Lie の定理の系*

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の有限次元加群 $`V`、は、基底を選んで上三角行列に出来る。

証明には以下の、Lie の定理を使います。

> *Lie の定理*

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の非自明な有限次元加群 $`V` に対し、全ての $`L \to V` 作用に共通する $`V` の非零固有ベクトル $`\lambda` が存在する。

こちらの定理を、 $`V`, $`V / \langle \lambda_0 \rangle`, $`V / \langle \lambda_0, \lambda_1 \rangle` と、帰納的に使っていけば証明できます。

さて、証明支援系をある程度触った事がある人なら、この様な帰納的な議論が形式化で躓きやすいポイントである事が分かると思います。実際の証明を途中まで進めてみましょう。

```lean hellExample -keep
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

さて、今から、{lean hellExample2}`V ⧸ V₀` 上の基底 {lean hellExample2}`b₀` を {lean hellExample2}`V` 上に持ち上げて、{lean hellExample2}`V₀` 上の基底 {lean hellExample2}`bᵥ` と組み合わせた基底を構成したいのですが、直接構成するのは面倒です。

都合がいい事に、 Mathlib には、上記の例の様に、商上の基底を組み合わせて新しい基底を作る定義があります。しかも、多数の simp 補題もあります。

```lean hellExample -keep
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

```lean hellExample -show
open Module LinearMap Matrix TensorProduct LieAlgebra LieSubmodule LieModule SemiDirectSum

attribute [local instance 100] LieRing.ofAssociativeRing

macro "YOU_KNOW_THE_THING" : tactic =>
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
  YOU_KNOW_THE_THING
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

このゴールなら先程の `sumQuot_repr_inr` 補題が使える筈です。一体何が起こっているのでしょうか。

実はこれは、{lean hellExample2}`↥V₀` と {lean hellExample2}`↥(↑V₀ : Submodule K V)` を統合できない事による、つまり、Lie 代数上の加群(`LieSubmodule`)から通常の加群(`Submodule`)への型強制が、型に現れる事によって起こった問題なのです。

# Subobject hell

この様に、`SetLike` オブジェクト同士の型強制が型に現れて悪さをする問題を、 *Subobject hell* と暫定的に呼ぶ事にしましょう。

この問題は Ado の定理を証明する上で最大の悩みでした。というのも、Lie 代数を扱う時は、`LieSubmodule K L V ⊆ Submodule K V`, `LieIdeal K L ⊆ LieSubalgebra K L ⊆ Submodule K V` の型強制が頻発し、型に現れる事が珍しくないからです。

形式化の途中で、Lean のメタ知識を使って、この Subobject hell の解決をしようと少しだけ試みたのですが、今まで未解決のままです。形式化も終わりましたし、この問題に本腰を入れるのも良いかもしれません。

# 対処法

最終的に、以下の様に、定義をコピペする事で対処しました。

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
  YOU_KNOW_THE_THING
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

# 最後に

今回の Subobject hell 以外にも、数多くの Mathlib の改善点が見つかったので、この様にブログ形式で紹介していきたいです。

それと個人的に、これらの改善点の多くはメタプログラミングの問題だと考えているので、今後 Mathlib へメタプログラミング関連の貢献をしたり、メタ知識をより深めて、レビューでt-metaタグのPRをレビューし始めようかなと考えています。(あくまで予定ですが)

それと、この記事は Verso で書かれており、ソースは[こちら](https://github.com/Komyyy/ado/tree/master/AdoPage)から見れます。

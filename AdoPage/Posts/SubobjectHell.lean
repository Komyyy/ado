/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import VersoBlog
import Ado.ForMathlib.LieBaseChange
import Ado.ForMathlib.MatrixTriangular
import Ado.ForMathlib.LieSolvable
open Verso Genre Blog

#doc (Post) "Subobject Hell" =>

%%%
authors := ["Miyahara Kō"]
date := {year := 2026, month := 10, day := 7}
draft := true
%%%

```leanInit hellExample
```

このページは、著者の宮原皓宇が、Adoの定理を形式化する際に気付いたMathlibの改善点を書き記したものです。

今回紹介する現象は、形式化に辺り、最も私の手を煩わせた点です。

具体例で示した方が分かりやすいので、実践として、以下の定理を考えます。これは実際にこのリポジトリで形式化されたものです。([リンク](../../docs/Ado/ForMathlib/LieTheoremCorollary.html) 切れてたらごめん)

# 具体例

この章は意味が分からなくても全然大丈夫です。最後の形式化上の問題さえ理解すれば大丈夫です。

私も形式化するまでは理解していませんでしたので。

> # Lie の定理の系

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の有限次元加群 $`V`、は、基底を選んで上三角行列に出来る。

証明には以下の、Lie の定理を使います。

> # Lie の定理

  標数0の代数的閉体上の可解 Lie 代数 $`L` 上の非自明な有限次元加群 $`V` に対し、全ての $`L \to V` 作用に共通する $`V` の非零固有ベクトル $`\lambda` が存在する。

こちらの定理を、 $`V`, $`V / \langle \lambda_0 \rangle`, $`V / \langle \lambda_0, \lambda_1 \rangle` と、帰納的に使っていけば証明できます。

さて、証明支援系をある程度触った事がある人なら、この様な帰納的な議論が形式化で躓きやすいポイントである事が分かると思います。実際の証明を途中まで進めてみましょう。

```lean hellExample
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

さて、

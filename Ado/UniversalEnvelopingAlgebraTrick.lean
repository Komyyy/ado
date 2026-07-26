/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Ado.Statement
public import Ado.ForMathlib.UniversalEnvelopingAlgebra

/-!
## 普遍包絡代数への包含写像の単射性を示す為のトリック

Ado の定理を示すために普遍包絡代数が元の Lie 代数上の加群としての忠実性を示す必要があり、そのために包含写像の単射性を
示す必要があるのだが、Claude Fable に聞いた所どうやらそれを示すのは Poincaré–Birkhoff–Witt の定理を示すのと
同じぐらい大変らしい。だが、Ado の定理で使う Lie 代数は帰納法の仮定により別の忠実な加群が存在するので、その場合
PBW を使わなくても非常に短い証明が得られる。本来ならば PBW で一般の可換環上の自由な Lie 代数に対して示すべきだが、
ここでは省略して前述のトリックを使う。
-/

public section

open LieAlgebra LieModule

namespace UniversalEnvelopingAlgebra

open Function

variable (K 𝔤 : Type*)
variable [Field K] [LieRing 𝔤] [LieAlgebra K 𝔤]

lemma ι_injective_of_isAdo [IsAdo K 𝔤] : Injective (ι K (L := 𝔤)) := by
  have h := IsFaithful.injective_toEnd (R := K) (L := 𝔤) (M := AdoSpace K 𝔤)
  rw [← ι_comp_lift] at h
  exact h.of_comp

instance [IsAdo K 𝔤] : IsFaithful K 𝔤 (UniversalEnvelopingAlgebra K 𝔤) := by
  rw [isFaithful_iff']
  intro x hx
  specialize hx 1
  rwa [bracket_eq, mul_one, map_eq_zero_iff _ (ι_injective_of_isAdo K 𝔤)] at hx

end UniversalEnvelopingAlgebra

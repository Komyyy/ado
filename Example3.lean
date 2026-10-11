module
public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Submonoid

public section

variable {G : Type*} [CommGroup G]

variable (G) in
theorem Submonoid.oneLE.isMulPointed [PartialOrder G] [IsOrderedMonoid G] :
    (oneLE G).IsMulPointed := by simp_all [IsMulPointed, ge_antisymm_iff]

@[implicit_reducible]
def PartialOrder.mkOfSubmonoid {M : Submonoid G} (hM : M.IsMulPointed) : PartialOrder G where
  le a b := b / a ∈ M
  le_refl a := by simp [one_mem]
  le_trans a b c nab nbc := by simpa using mul_mem nbc nab
  le_antisymm a b nab nba := by
    simpa [div_eq_one, eq_comm] using hM.eq_one_of_mem_of_inv_mem nab (by simpa using nba)

def LE.leExplicit {α} (o : LE α) (x y : α) :=
  o.le x y

notation x:51 "≤[" o "]" y:51 => LE.leExplicit o x y

@[simp]
theorem PartialOrder.mkOfSubmonoid_le_iff {M : Submonoid G} {hM : M.IsMulPointed} {a b : G} :
    a ≤[(mkOfSubmonoid hM).toLE] b ↔ b / a ∈ M := .rfl

theorem IsOrderedMonoid.mkOfSubmonoid {M : Submonoid G} (hM : M.IsMulPointed) :
    letI _ := PartialOrder.mkOfSubmonoid hM
    IsOrderedMonoid G :=
  letI _ := PartialOrder.mkOfSubmonoid hM
  { mul_le_mul_left := fun a b nab c ↦ by simpa using nab }

variable (G) in
noncomputable def CommGroup.submonoidPartialOrderEquiv :
    Equiv {C : Submonoid G // C.IsMulPointed}
          {_o : PartialOrder G // IsOrderedMonoid G} where
  toFun := fun ⟨_, hC⟩ ↦ ⟨.mkOfSubmonoid hC, .mkOfSubmonoid _⟩
  invFun := fun ⟨_, _⟩ ↦ ⟨.oneLE G, Submonoid.oneLE.isMulPointed G⟩
  left_inv := fun ⟨_, _⟩ ↦ by ext; simp
  right_inv := fun ⟨o, ho⟩ ↦ by
    ext x y
    simp

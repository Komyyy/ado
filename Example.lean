module
public import Lean
public import Std

universe u v

def Set (α : Type u) := α → Prop

class SetLike (A : Type u) (B : outParam (Type v)) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B

variable {α}

@[implicit_reducible]
protected def Set.Mem (s : Set α) (a : α) : Prop :=
  s a

instance : Membership α (Set α) :=
  ⟨Set.Mem⟩

attribute [coe] SetLike.coe

variable {A : Type u} {B : outParam (Type v)} [i : SetLike A B]

instance : CoeTC A (Set B) where coe := SetLike.coe

instance : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩

instance : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

structure MySubobject1 (α : Type u) where
  carrier : Set α

instance : SetLike (MySubobject1 α) α where
  coe s := s.carrier

structure MySubobject2 (α : Type u) extends MySubobject1 α

attribute [coe] MySubobject2.toMySubobject1

instance : Coe (MySubobject2 α) (MySubobject1 α) where
  coe x := x.toMySubobject1

instance : SetLike (MySubobject2 α) α where
  coe s := s.carrier

def myDef {X : MySubobject1 α} (_x : X) : Nat :=
  0

@[simp]
theorem myDef_eq {X : MySubobject1 α} (x : X) : myDef x = 0 :=
  rfl

example {Y : MySubobject2 α} (y : Y) : myDef y = 0 := by
  simp

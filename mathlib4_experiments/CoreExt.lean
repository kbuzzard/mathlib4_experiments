/-
Just some random additions to `Core.lean` that look like they would actually belong there.
-/



theorem Iff.isEquivalence              : Equivalence Iff     := ⟨Iff.refl, Iff.symm, Iff.trans⟩
theorem Eq.isEquivalence  {α : Sort u} : Equivalence (@Eq α) := ⟨Eq.refl,  Eq.symm,  Eq.trans⟩



theorem Setoid.of_Eq {α : Sort u} [Setoid α] {a b : α} (h : a = b) : a ≈ b :=
h ▸ Setoid.refl a


class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

class Subset (α : Type u) where
  subset : α → α → Prop

infix:50 " ⊆ " => Subset.subset

namespace List

protected def mem : α → List α → Prop
| a, [] => False
| a, b :: l => a = b ∨ List.mem a l

instance : Mem α (List α) := ⟨List.mem⟩

theorem mem_cons_self (a : α) (l : List α) : a ∈ a :: l :=
Or.inl rfl

@[simp] theorem mem_cons_iff (a y : α) (l : List α) : a ∈ y :: l ↔ (a = y ∨ a ∈ l) := Iff.rfl

protected def subset (l₁ l₂ : List α) := ∀ {a : α}, a ∈ l₁ → a ∈ l₂

instance : Subset (List α) := ⟨List.subset⟩

theorem eq_nil_of_length_eq_zero {l : List α} (hl : length l = 0) : l = [] :=
match l with
| [] => rfl
| x :: m => False.elim $ Nat.succ_ne_zero (m.length) (List.length_cons x m ▸ hl)

end List

def symmetric (r : α → α → Prop) := ∀ {x y}, r x y → r y x

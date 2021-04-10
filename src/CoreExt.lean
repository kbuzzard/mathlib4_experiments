/-
Just some random additions to `Core.lean` that look like they would actually belong there.
-/



theorem Iff.isEquivalence              : Equivalence Iff     := ⟨Iff.refl, Iff.symm, Iff.trans⟩
theorem Eq.isEquivalence  {α : Sort u} : Equivalence (@Eq α) := ⟨Eq.refl,  Eq.symm,  Eq.trans⟩



theorem Setoid.of_Eq {α : Sort u} [Setoid α] {a b : α} (h : a = b) : a ≈ b :=
h ▸ Setoid.refl a

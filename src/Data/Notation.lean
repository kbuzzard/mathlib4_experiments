set_option autoBoundImplicitLocal false

universes u₁ u₂ v



/-
In Lean 3 mathlib, the `≃` notation is defined specifically for `equiv`.
This is a more flexible version using a type class for overloading support.
In the instance defined in `Data.Equiv.Basic`, `α` `β` and `γ` are all `Sort _`.
`γ` needs to be bundled because it cannot be inferred by type class resolution.
-/
class HasEquivalence (α : Sort u₁) (β : Sort u₂) where
{γ : Sort v}
(Equiv : α → β → γ)

infix:25 " ≃ " => HasEquivalence.Equiv

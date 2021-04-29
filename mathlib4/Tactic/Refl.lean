/-

## `refl`

Currently works for iff and =

-/

syntax "refl" : tactic

macro_rules
  | `(tactic| refl) => `(tactic| apply Eq.refl)

macro_rules
  | `(tactic| refl) => `(tactic| apply Iff.refl)

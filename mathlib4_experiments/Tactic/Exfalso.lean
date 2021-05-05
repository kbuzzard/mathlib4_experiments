/-

## `exfalso`

-/

syntax "exfalso" : tactic

macro_rules
  | `(tactic| exfalso) => `(tactic| apply False.elim)

/-
example : False -> p := by
  intro h;
  exfalso;
  skip;
  exact h;
-/
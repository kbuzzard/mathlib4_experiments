/-

## `split`

-/

syntax "split" : tactic

macro_rules
  | `(tactic| split) => `(tactic| apply And.intro)
  | `(tactic| split) => `(tactic| apply Iff.intro)

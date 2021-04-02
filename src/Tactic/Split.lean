/-

## `split`

Currently works for iff and and

-/

syntax "split" : tactic

macro_rules
  | `(tactic| split) => `(tactic| apply Iff.intro)

macro_rules
  | `(tactic| split) => `(tactic| apply And.intro)

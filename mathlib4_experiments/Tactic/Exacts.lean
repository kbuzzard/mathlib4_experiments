macro "exacts" "[" ts:term,* "]" : tactic => do
  let mut s <- `(tactic| done)
  for t in ts.getElems.reverse do
    s <- `(tactic| exact $t; $s)
  s

def foo : Nat := by
  exacts [0]

def bar : Nat × Nat := by
  skip
  apply Prod.mk
  exacts [0,1]

--#print foo -- (0)
--#print bar -- (0, 1)
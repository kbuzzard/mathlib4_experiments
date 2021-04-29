structure Foo where
  x : Nat
  y : Nat

structure Boo where
  w : Nat
  z : Nat

structure Bla extends Foo, Boo where
  bit : Bool

#check Bla.mk -- Foo → Boo → Bool → Bla
#check Bla.mk { x := 10, y := 20 } { w := 30, z := 40 } true
#check { x := 10, y := 20, w := 30, z := 40, bit := true : Bla }
#check { toFoo := { x := 10, y := 20 },
         toBoo := { w := 30, z := 40 },
         bit := true : Bla }

theorem ex :
    Bla.mk { x := x, y := y } { w := w, z := z } b
    =
    { x := x, y := y, w := w, z := z, bit := b } :=
  rfl
#check @ex
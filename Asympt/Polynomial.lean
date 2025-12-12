def toPolyFromDegree (l : List Nat) (d : Nat) : Nat → Nat := λx => match l with
  | List.nil => 0
  | List.cons c t => c * x ^ d + toPolyFromDegree t (d + 1) x

def toPoly (l : List Nat) : Nat → Nat := toPolyFromDegree l 0

def isPoly (f : Nat → Nat) : Prop := ∃l, f = toPoly l

class Poly (f : Nat → Nat) where
  poly : isPoly f

-- Alternative Typeclass
class PolyConcrete (f : Nat → Nat) where
  list : List Nat
  poly : f = toPoly list

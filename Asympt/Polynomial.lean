import Asympt.Defs

def toPolyFromDegree (l : List Nat) (d : Nat) : Nat → Nat := λx => match l with
  | List.nil => 0
  | List.cons c t => c * x ^ d + toPolyFromDegree t (d + 1) x

def toPoly (l : List Nat) : Nat → Nat := toPolyFromDegree l 0

class Poly (f : Nat → Nat) where
  list : List Nat
  poly : f = toPoly list

theorem poly_degree_concrete (f : Nat → Nat) [h : Poly f] : bigO f (λn => n ^ h.list.length) := sorry

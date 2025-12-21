import Asympt.Basic

open List

@[simp] def toPoly (l : List Nat) : Nat → Nat := λx => match l with
  | nil => 0
  | c :: t => c + x * toPoly t x

class Poly (f : Nat → Nat) where
  list : List Nat
  poly : f = toPoly list

theorem to_poly_degree (list : List Nat) : bigO (toPoly list) (λn => n ^ (list.length - 1)) := by
  induction list
  case nil => apply const
  case cons c t ih =>
    -- have: (toPoly t) = O(n ^ (d - 1))
    -- goal: c + n * (toPoly t) = O(n ^ d)
    simp

    sorry

instance const_poly (c : Nat) : Poly (λ_ => c) where
  list := [c]
  poly := by simp

instance add_poly (f g : Nat → Nat) [h₁ : Poly f] [h₂ : Poly g] : Poly (f + g) where
  list := h₁.list + h₂.list
  poly := by
    funext x
    sorry

instance mul_poly (f g : Nat → Nat) [h₁ : Poly f] [h₂ : Poly g] : Poly (f * g) where
  list := h₁.list * h₂.list
  poly := by
    funext x
    sorry

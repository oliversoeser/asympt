/--
This typeclass states that `f` is asymptotically positive.
-/
class APos (f : Nat → Nat) where
  apos : ∃n₀, ∀n ≥ n₀, 0 < f n

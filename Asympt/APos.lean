-- Asymptotically positive functions
class APos (f : Nat → Nat) where
  apos : ∃n₀, ∀n ≥ n₀, 0 < f n

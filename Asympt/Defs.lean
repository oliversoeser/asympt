def bigO (f g : Nat → Nat) : Prop :=
  ∃c > 0, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

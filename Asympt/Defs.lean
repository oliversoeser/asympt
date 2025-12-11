def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

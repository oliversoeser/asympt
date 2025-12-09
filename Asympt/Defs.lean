def bigO (f g : Nat → Nat) : Prop :=
  ∃c > 0, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

def bigOmega (f g : Nat → Nat) : Prop :=
  ∃c > 0, ∃n₀, ∀n ≥ n₀, c * g n ≤ f n

def bigTheta (f g : Nat → Nat) : Prop :=
  ∃c₁ > 0, ∃c₂ > 0, ∃n₀, ∀n ≥ n₀, c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

def littleO (f g : Nat → Nat) : Prop :=
  ∀c > 0, ∃n₀, ∀n ≥ n₀, f n < c * g n

def littleOmega (f g : Nat → Nat) : Prop :=
  ∀c > 0, ∃n₀, ∀n ≥ n₀, c * g n < f n

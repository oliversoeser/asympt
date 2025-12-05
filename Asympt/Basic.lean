def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n, n ≥ n₀ → f n ≤ c * g n

def bigOmega (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n, n ≥ n₀ → c * g n ≤ f n

def bigTheta (f g : Nat → Nat) : Prop :=
  ∃c₁, ∃c₂, ∃n₀, ∀n, n ≥ n₀ → c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n

def littleO (f g : Nat → Nat) : Prop :=
  ∀c, ∃n₀, ∀n, n ≥ n₀ → f n < c * g n

def littleOmega (f g : Nat → Nat) : Prop :=
  ∀c, ∃n₀, ∀n, n ≥ n₀ → c * g n < f n

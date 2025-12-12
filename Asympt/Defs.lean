def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

class BigO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_o : bigO f g

-- Alternative Typeclass
class BigOConcrete (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  c : Nat
  n₀ : Nat
  big_o : ∀n ≥ n₀, f n ≤ c * g n

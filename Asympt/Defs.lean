-- Fundamental Definitions - O and o
def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

def littleO (f g : Nat → Nat) : Prop :=
  ∀c > 0, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

class BigO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_o : bigO f g

-- Alternative Typeclass
class BigOConcrete (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  c : Nat
  n₀ : Nat
  big_o : ∀n ≥ n₀, f n ≤ c * g n

class LittleO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  little_o : littleO f g

-- Derived Definitions - Omegas and Theta
def bigOmega (f g : Nat → Nat) : Prop := bigO g f
def littleOmega (f g : Nat → Nat) : Prop := littleO g f
def bigTheta (f g : Nat → Nat) : Prop := bigO f g ∧ bigOmega f g

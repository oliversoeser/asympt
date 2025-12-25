-- Fundamental Definitions
def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

def littleO (f g : Nat → Nat) : Prop :=
  ∀c > 0, ∃n₀, ∀n ≥ n₀, f n < c * g n

class BigO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_o : bigO f g

class LittleO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  little_o : littleO f g

def bigTheta (f g : Nat → Nat) : Prop := bigO f g ∧ bigO g f

class BigTheta (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_theta : bigTheta f g

-- Omega Abbreviations
@[reducible] def bigOmega (f g : Nat → Nat) : Prop := bigO g f

@[reducible] def littleOmega (f g : Nat → Nat) : Prop := littleO g f

-- Basic Theorems
theorem big_theta_iff (f g : Nat → Nat) : bigTheta f g ↔ bigO f g ∧ bigOmega f g := ⟨id, id⟩

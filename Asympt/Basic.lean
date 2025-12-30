/-! # definitions  -/

/--
O notation. `f=O(g)` means that there is a constant `c`
such that `f` is eventually bounded above by `c * g n`.
-/
def bigO (f g : Nat → Nat) : Prop :=
  ∃c, ∃n₀, ∀n ≥ n₀, f n ≤ c * g n

/--
o notation. `f=o(g)` means that for any positive contants
`c₁, c₂`, `c₁ * f n` is exceeded by `c₂ * g n`.

We use two constants instead of one to make up for the
absence of fractions.
-/
def littleO (f g : Nat → Nat) : Prop :=
  ∀c₁ > 0, ∀c₂ > 0, ∃n₀, ∀n ≥ n₀, c₁ * f n < c₂ * g n

/--
Θ notation. `f=Θ(g)` means that `f=O(g) ∧ g=O(f)`.
-/
def bigTheta (f g : Nat → Nat) : Prop := bigO f g ∧ bigO g f

/--
Ω notation. `f=Ω(g)` means that `g=O(f)`.
-/
@[reducible] def bigOmega (f g : Nat → Nat) : Prop := bigO g f

/--
ω notation. `f=ω(g)` means that `g=o(f)`.
-/
@[reducible] def littleOmega (f g : Nat → Nat) : Prop := littleO g f

/-! # typeclasses  -/

/--
This typeclass states that `f=O(g)`.
-/
class BigO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_o : bigO f g

/--
This typeclass states that `f=o(g)`.
-/
class LittleO (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  little_o : littleO f g

/--
This typeclass states that `f=Θ(g)`.
-/
class BigTheta (f : Nat → Nat) (g : outParam (Nat → Nat)) where
  big_theta : bigTheta f g

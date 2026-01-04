import Asympt.Tactics

namespace Lift

open Lean.Grind

/-! # semiring-valued function lifting -/

section Semiring

universe u v
variable {A : Type u} {B : Type v} [sr : Semiring B]

instance : Add (A → B) where add f g := λx => (f x) + (g x)
instance : Mul (A → B) where mul f g := λx => (f x) * (g x)
instance : SMul Nat (A → B) where smul n f := λx => n • (f x)
instance : HPow (A → B) Nat (A → B) where hPow f n := λx => (f x) ^ n

instance : NatCast (A → B) where natCast n := λ_ => sr.natCast.natCast n
instance {n : Nat} : OfNat (A → B) n where ofNat := λ_ => (sr.ofNat n).ofNat

instance lift_semiring_fun : Semiring (A → B) := by
  constructor
  all_goals (intros; funext; try struct_exact sr)
  · sorry
  · sorry
  · sorry

end Semiring

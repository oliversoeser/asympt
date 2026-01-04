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

instance lift_semiring_fun : Semiring (A → B) where
  add_zero := by intro; funext; exact sr.add_zero _
  add_comm := by intros; funext; exact sr.add_comm _ _
  add_assoc := by intros; funext; exact sr.add_assoc _ _ _
  mul_assoc := by intros; funext; exact sr.mul_assoc _ _ _
  mul_one := by intro; funext; exact sr.mul_one _
  one_mul := by intro; funext; exact sr.one_mul _
  left_distrib := by intros; funext; exact sr.left_distrib _ _ _
  right_distrib := by intros; funext; exact sr.right_distrib _ _ _
  zero_mul := by intro; funext; exact sr.zero_mul _
  mul_zero := by intro; funext; exact sr.mul_zero _
  pow_zero := by intro; funext; exact sr.pow_zero _
  pow_succ := by intros; funext; exact sr.pow_succ _ _
  ofNat_succ := by intros; funext; exact sr.ofNat_succ _
  ofNat_eq_natCast := by intros; funext; exact sr.ofNat_eq_natCast _
  nsmul_eq_natCast_mul := by intros; funext; exact sr.nsmul_eq_natCast_mul _ _


end Semiring

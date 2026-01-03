open Lean.Grind

/-! # semiring-valued function lifting -/

universe u v
variable (A : Type u) (B : Type v) [sb : Semiring B]

-- A → B where [Semiring B]
def F := A → B

instance : Add (F A B) where add f g := λx => (f x) + (g x)

instance : Mul (F A B) where mul f g := λx => (f x) * (g x)

instance : NatCast (F A B) where natCast n := λ_ => sb.natCast.natCast n

instance {n : Nat} : OfNat (F A B) n where ofNat := λ_ => (sb.ofNat n).ofNat

instance : SMul Nat (F A B) where smul n f := λx => n • (f x)

instance : HPow (F A B) Nat (F A B) where hPow f n := λx => (f x) ^ n

instance : Semiring (F A B) where
  add_zero := by intro; funext; exact sb.add_zero _
  add_comm := by intros; funext; exact sb.add_comm _ _
  add_assoc := by intros; funext; exact sb.add_assoc _ _ _
  mul_assoc := by intros; funext; exact sb.mul_assoc _ _ _
  mul_one := by intro; funext; exact sb.mul_one _
  one_mul := by intro; funext; exact sb.one_mul _
  left_distrib := by intros; funext; exact sb.left_distrib _ _ _
  right_distrib := by intros; funext; exact sb.right_distrib _ _ _
  zero_mul := by intro; funext; exact sb.zero_mul _
  mul_zero := by intro; funext; exact sb.mul_zero _
  pow_zero := by intro; funext; exact sb.pow_zero _
  pow_succ := by intros; funext; exact sb.pow_succ _ _
  ofNat_succ := by intros; funext; exact sb.ofNat_succ _
  ofNat_eq_natCast := by intros; funext; exact sb.ofNat_eq_natCast _
  nsmul_eq_natCast_mul := by intros; funext; exact sb.nsmul_eq_natCast_mul _ _

namespace Lift

open Lean.Grind

/-! # function algebra lifting -/

universe u v
variable {A : Type u} {B : Type v} [sr : Semiring B] [csr : CommSemiring B]
  [r : Ring B] [cr : CommRing B] [fld : Field B]

instance : Add (A → B) where add f g := λa => (f a) + (g a)
instance : Mul (A → B) where mul f g := λa => (f a) * (g a)
instance : SMul Nat (A → B) where smul n f := λa => n • (f a)
instance : HPow (A → B) Nat (A → B) where hPow f n := λa => (f a) ^ n

instance : NatCast (A → B) where natCast n := λ_ => sr.natCast.natCast n
instance {n : Nat} : OfNat (A → B) n where ofNat := λ_ => (sr.ofNat n).ofNat

instance semiring_fun : Semiring (A → B) where
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

instance comm_semiring_fun : CommSemiring (A → B) where
  mul_comm f g := sorry

instance : IntCast (A → B) where intCast x := λ_ => r.intCast.intCast x
instance : SMul Int (A → B) where smul x f := λa => x • (f a)

instance ring_fun : Ring (A → B) where
  neg := sorry
  sub := sorry
  neg_add_cancel := sorry
  sub_eq_add_neg := sorry
  neg_zsmul := sorry
  zsmul_natCast_eq_nsmul := sorry
  intCast_ofNat := sorry
  intCast_neg := sorry

instance comm_ring_fun : CommRing (A → B) where

instance : HPow (A → B) Int (A → B) where hPow f x := λa => (f a) ^ x

instance field_fun : Field (A → B) where
  inv := sorry
  div := sorry
  div_eq_mul_inv := sorry
  zero_ne_one := sorry
  inv_zero := sorry
  mul_inv_cancel := sorry
  zpow_zero := sorry
  zpow_succ := sorry
  zpow_neg := sorry

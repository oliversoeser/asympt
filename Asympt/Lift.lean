namespace Lift

open Lean.Grind

/-! # function algebra -/

universe u v
variable {A : Type u} {B : Type v}

instance [Semiring B] : Add (A → B) where add f g := λa => (f a) + (g a)
instance [Semiring B] : Mul (A → B) where mul f g := λa => (f a) * (g a)
instance [Semiring B] : SMul Nat (A → B) where smul n f := λa => n • (f a)
instance [Semiring B] : HPow (A → B) Nat (A → B) where hPow f n := λa => (f a) ^ n

instance [sr : Semiring B] : NatCast (A → B) where natCast n := λ_ => sr.natCast.natCast n
instance {n : Nat} [sr : Semiring B] : OfNat (A → B) n where ofNat := λ_ => (sr.ofNat n).ofNat

instance semiring_fun [sr : Semiring B] : Semiring (A → B) where
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

instance comm_semiring_fun [csr : CommSemiring B] : CommSemiring (A → B) where
  mul_comm := by intros; funext a; exact csr.mul_comm _ _

instance [r : Ring B] : IntCast (A → B) where intCast i := λ_ => r.intCast.intCast i
instance [Ring B] : SMul Int (A → B) where smul i f := λa => i • (f a)
instance [Ring B] : Neg (A → B) where neg f := λa => -(f a)
instance [Ring B] : Sub (A → B) where sub f g := λa => (f a) - (g a)

instance ring_fun [r : Ring B] : Ring (A → B) where
  neg_add_cancel := by intros; funext; exact r.neg_add_cancel _
  sub_eq_add_neg := by intros; funext; exact r.sub_eq_add_neg _ _
  neg_zsmul := by intros; funext; exact r.neg_zsmul _ _
  zsmul_natCast_eq_nsmul := by intros; funext; exact r.zsmul_natCast_eq_nsmul _ _
  intCast_ofNat := by intros; funext; exact r.intCast_ofNat _
  intCast_neg := by intros; funext; exact r.intCast_neg _

instance comm_ring_fun [cr : CommRing B] : CommRing (A → B) where

/-! # ordered function algebra -/

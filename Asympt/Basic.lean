import Asympt.Defs
import Asympt.Notation

open Nat

theorem const_mul_O (c : Nat) (f : Nat → Nat) : bigO (c * f) f := by
  exists (c + 1), by simp, 0
  intro n h
  calc
    _ = c * (f n) := by trivial
    _ ≤ (c + 1) * (f n) := Nat.mul_le_mul (le_succ c) le.refl

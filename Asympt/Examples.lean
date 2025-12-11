import Asympt.Basic

open Nat

example : bigO (λn => 5 * n ^ 3 + 100) (λn => n ^ 3) := by
  exists 6, by simp, 10
  intro n h
  calc
    _ ≤ 5 * n ^ 3 + 10 ^ 3 := by simp
    _ ≤ 5 * n ^ 3 + n ^ 3 := add_le_add le.refl (Nat.pow_le_pow_left h 3)
    _ = 6 * n ^ 3 := (succ_mul 5 (n ^ 3)).symm

example : bigO (λn => 5 * n ^ 3 + 100) (λn => n ^ 4) := by
  exists 6, by simp, 10
  intro n h
  calc
    _ ≤ 5 * n ^ 3 + 10 ^ 4 := by simp
    _ ≤ 5 * n ^ 4 + 10 ^ 4 := add_le_add (Nat.mul_le_mul le.refl (Nat.pow_le_pow_of_le (lt_of_add_left_lt h) (by simp))) le.refl
    _ ≤ 5 * n ^ 4 + n ^ 4 := add_le_add le.refl (Nat.pow_le_pow_left h 4)
    _ = 6 * n ^ 4 := (succ_mul 5 (n ^ 4)).symm

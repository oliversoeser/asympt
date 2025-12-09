import Asympt.Basic

open Nat

example : bigO (λn => 5 * n^3 + 100) (λn => n^3) := by
  exists 6, 10
  intro n h
  simp
  calc
    5 * n ^ 3 + 100 ≤ 5 * n ^ 3 + 1000 := by simp
    5 * n ^ 3 + 1000 ≤ 5 * n ^ 3 + n ^ 3 := add_le_add le.refl (sorry)
    5 * n ^ 3 + n ^ 3 = 6 * n ^ 3 := (succ_mul 5 (n ^ 3)).symm

example : bigOmega (λn => 5 * n^3 + 100) (λn => n^3) := sorry

example : bigTheta (λn => 5 * n^3 + 100) (λn => n^3) := sorry

example : bigO (λn => 5 * n^3 + 100) (λn => n^4) := sorry

example : littleO (λn => 5 * n^3 + 100) (λn => n^4) := sorry

example : bigOmega (λn => 5 * n^3 + 100) (λn => n^2) := sorry

example : littleOmega (λn => 5 * n^3 + 100) (λn => n^2) := sorry

/-
lg n = o(n^5)
n^5 = o(2^n)
lg(4n) = lg n + lg 4 = O(lg n)
lg(n^4) = 4 lg n = O(lg n)
(4n)^3 = 64n^3 = Θ(n^3)
-/

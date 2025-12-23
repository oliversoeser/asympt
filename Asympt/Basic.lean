import Asympt.Defs
import Asympt.Notation
import Asympt.APos

open Nat Std

-- Big O defines a preorder

theorem refl (f : Nat → Nat) : bigO f f := by
  exists 1, 0
  intro n h
  simp

theorem trans (f g h : Nat → Nat) (h₁ : bigO f g) (h₂ : bigO g h) : bigO f h := by
  obtain ⟨c₁,n₁,hle₁⟩ := h₁
  obtain ⟨c₂,n₂,hle₂⟩ := h₂
  exists c₁ * c₂, max n₁ n₂
  intro n h₃
  calc
    _ ≤ c₁ * g n := hle₁ n (Nat.le_trans (le_max.mpr (by simp)) h₃)
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul le.refl (hle₂ n (Nat.le_trans (le_max.mpr (by simp)) h₃))
    _ = c₁ * c₂ * h n := (Nat.mul_assoc c₁ c₂ (h n)).symm

instance : LE (Nat → Nat) := ⟨bigO⟩

instance : IsPreorder (Nat → Nat) where
  le_refl := refl
  le_trans := trans

-- Basic equations

-- c = O(1)
theorem const (c : Nat) : bigO (λ_ => c) (λ_ => 1) := by
  exists c
  simp

-- c * f = O(f)
theorem const_mul (c : Nat) (f : Nat → Nat) : bigO (c * f) f := by
  exists c, 0
  intro n h
  exact le.refl

-- Equations for asymptotically positive functions

-- c + f = O(f)
theorem const_add (c : Nat) (f : Nat → Nat) [h : APos f] : bigO (c + f) f := by
  let ⟨n₀, h'⟩ := h.apos
  exists c + 1, n₀
  intro n hn
  have pos : 1 ≤ f n := h' n hn
  have a : c + f n ≤ c * f n + f n := Nat.add_le_add_right (Nat.le_mul_of_pos_right c pos) (f n)
  have b : c * f n + f n = (c + 1) * f n := (succ_mul c (f n)).symm
  exact le_trans a (Nat.le_of_eq b)

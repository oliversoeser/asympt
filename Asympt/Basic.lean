import Asympt.Defs
import Asympt.Notation

open Nat Std

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

theorem const_mul (c : Nat) (f : Nat → Nat) : bigO (c * f) f := by
  exists c, 0
  intro n h
  exact le.refl

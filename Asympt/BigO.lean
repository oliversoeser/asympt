import Asympt.Notation

open Std

namespace BigO

/-! # preorder -/

theorem refl (f : Nat → Nat) : f=O(f) := by
  exists 1, 0
  intro n h
  simp

theorem trans {f g h : Nat → Nat} (h₁ : f=O(g)) (h₂ : g=O(h)) : f=O(h) := by
  obtain ⟨c₁,n₁,hle₁⟩ := h₁
  obtain ⟨c₂,n₂,hle₂⟩ := h₂
  exists c₁ * c₂, max n₁ n₂
  intro n h₃
  calc
    _ ≤ c₁ * g n := hle₁ n (Nat.le_trans (le_max.mpr (by simp)) h₃)
    _ ≤ c₁ * (c₂ * h n) := Nat.mul_le_mul Nat.le.refl (hle₂ n (Nat.le_trans (le_max.mpr (by simp)) h₃))
    _ = c₁ * c₂ * h n := (Nat.mul_assoc c₁ c₂ (h n)).symm

instance le : LE (Nat → Nat) := ⟨bigO⟩

instance : Refl bigO := ⟨refl⟩
instance : Trans bigO bigO bigO := ⟨trans⟩

instance preorder : IsPreorder (Nat → Nat) where
  le_refl := refl
  le_trans := @trans

/-! # algebra -/



end BigO

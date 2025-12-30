import Asympt.BigO

open Std

namespace LittleO

theorem big_o_of_little_o {f g : Nat → Nat} (h : f=o(g)) : f=O(g) := by
  have ⟨n₀,h⟩ := h 1 Nat.one_pos 1 Nat.one_pos
  exists 1, n₀
  intro n hn
  simp_all
  exact le_of_lt (h n hn)

instance : Subrelation littleO bigO := big_o_of_little_o

/-! # strict partial order -/

theorem irrefl (f : Nat → Nat) : f≠o(f) := by
  intro h
  unfold littleO at h
  have ⟨n₀,h⟩ := h 1 Nat.one_pos 1 Nat.one_pos
  have h := h n₀
  simp at h

theorem asymm (f g : Nat → Nat) (h : f=o(g)) : g≠o(f) := by
  intro h'
  have ⟨n₁,h⟩ := h 1 Nat.one_pos 1 Nat.one_pos
  have ⟨n₂,h'⟩ := h' 1 Nat.one_pos 1 Nat.one_pos
  let n₀ := max n₁ n₂
  have h := h n₀ (max_le_iff.mp (le_refl n₀)).1
  have h' := h' n₀ (max_le_iff.mp (le_refl n₀)).2
  simp_all
  exact Nat.lt_irrefl (f n₀) (lt_trans h h')

theorem trans {f g h : Nat → Nat} (h₁ : f=o(g)) (h₂ : g=o(h)) : f=o(h) := by
  intro c₁ hc₁ c₂ hc₂
  have ⟨n₁,h₁⟩ := h₁ c₁ hc₁ c₂ hc₂
  have ⟨n₂,h₂⟩ := h₂ 1 Nat.one_pos 1 Nat.one_pos
  exists (max n₁ n₂)
  intro n hn
  have h₁ := h₁ n (max_le_iff.mp hn).1
  have h₂ := h₂ n (max_le_iff.mp hn).2
  simp at h₂
  exact Nat.lt_trans h₁ (Nat.mul_lt_mul_of_pos_left h₂ hc₂)

instance : Irrefl littleO := ⟨irrefl⟩
instance : Asymm littleO := ⟨asymm⟩
instance : Trans littleO littleO littleO := ⟨trans⟩

end LittleO

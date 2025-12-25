import Asympt.BigO

open Std

namespace LittleO

theorem irrefl (f : Nat → Nat) : ¬littleO f f := by
  intro h
  unfold littleO at h
  have ⟨n₀,h⟩ := h 1 Nat.one_pos
  have h := h n₀
  simp at h

theorem asymm (f g : Nat → Nat) (h : littleO f g) : ¬littleO g f := by
  intro h'
  have ⟨n₁,h⟩ := h 1 Nat.one_pos
  have ⟨n₂,h'⟩ := h' 1 Nat.one_pos
  let n₀ := max n₁ n₂
  have h := h n₀ (max_le_iff.mp (le_refl n₀)).1
  have h' := h' n₀ (max_le_iff.mp (le_refl n₀)).2
  simp_all
  exact Nat.lt_irrefl (f n₀) (lt_trans h h')

theorem trans {f g h : Nat → Nat} (h₁ : littleO f g) (h₂ : littleO g h) : littleO f h := by
  intro c hc
  have ⟨n₁,h₁⟩ := h₁ c hc
  have ⟨n₂,h₂⟩ := h₂ 1 Nat.one_pos
  exists (max n₁ n₂)
  intro n hn
  have h₁ := h₁ n (max_le_iff.mp hn).1
  have h₂ := h₂ n (max_le_iff.mp hn).2
  simp at h₂
  exact Nat.lt_trans h₁ (Nat.mul_lt_mul_of_pos_left h₂ hc)

instance lt : LT (Nat → Nat) := ⟨littleO⟩

instance lawful_lt : LawfulOrderLT (Nat → Nat) := ⟨sorry⟩

end LittleO

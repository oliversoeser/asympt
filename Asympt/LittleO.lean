import Asympt.BigO

open Std

namespace LittleO

theorem irrefl (f : Nat → Nat) : f≠o(f) := by
  intro h
  unfold littleO at h
  have ⟨n₀,h⟩ := h 1 Nat.one_pos
  have h := h n₀
  simp at h

theorem asymm (f g : Nat → Nat) (h : f=o(g)) : g≠o(f) := by
  intro h'
  have ⟨n₁,h⟩ := h 1 Nat.one_pos
  have ⟨n₂,h'⟩ := h' 1 Nat.one_pos
  let n₀ := max n₁ n₂
  have h := h n₀ (max_le_iff.mp (le_refl n₀)).1
  have h' := h' n₀ (max_le_iff.mp (le_refl n₀)).2
  simp_all
  exact Nat.lt_irrefl (f n₀) (lt_trans h h')

theorem trans {f g h : Nat → Nat} (h₁ : f=o(g)) (h₂ : g=o(h)) : f=o(h) := by
  intro c hc
  have ⟨n₁,h₁⟩ := h₁ c hc
  have ⟨n₂,h₂⟩ := h₂ 1 Nat.one_pos
  exists (max n₁ n₂)
  intro n hn
  have h₁ := h₁ n (max_le_iff.mp hn).1
  have h₂ := h₂ n (max_le_iff.mp hn).2
  simp at h₂
  exact Nat.lt_trans h₁ (Nat.mul_lt_mul_of_pos_left h₂ hc)

theorem big_o_of_little_o {f g : Nat → Nat} (h : f=o(g)) : f=O(g) := by
  have ⟨n₀,h⟩ := h 1 Nat.one_pos
  exists 1, n₀
  intro n hn
  exact le_of_lt (h n hn)

theorem little_o_iff (f g : Nat → Nat) : f=o(g) ↔ f=O(g) ∧ g≠O(f) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact big_o_of_little_o h
    · intro h'
      sorry
  · intro ⟨h₁,h₂⟩
    sorry

instance lt : LT (Nat → Nat) := ⟨littleO⟩

instance lawful_lt : LawfulOrderLT (Nat → Nat) := ⟨little_o_iff⟩

end LittleO

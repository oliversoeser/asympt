import Asympt.BigO

open Std

namespace LittleO

instance : LT (Nat → Nat) := ⟨littleO⟩

instance : LawfulOrderLT (Nat → Nat) := ⟨λa b => ⟨by
  intro h
  unfold BigO.instLEForallNat
  unfold instLTForallNat at h
  simp_all
  and_intros
  · exists 1
    exact h 1 Nat.one_pos
  · intro ⟨c,n₁,h₁⟩
    have ⟨n₂,h₂⟩ := h 1 (by simp)
    let n := max n₁ n₂
    have h₁ := h₁ n (Nat.le_max_left n₁ n₂)
    have h₂ := h₂ n (Nat.le_max_right n₁ n₂)
    sorry, by
  intro ⟨h₁,h₂⟩
  unfold instLTForallNat
  unfold BigO.instLEForallNat at h₁ h₂
  simp_all
  sorry
⟩⟩

end LittleO

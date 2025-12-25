import Asympt.BigO

open Std

namespace LittleO

theorem irrefl (f : Nat → Nat) : ¬littleO f f := sorry

instance lt : LT (Nat → Nat) := ⟨littleO⟩

instance lawful_lt : LawfulOrderLT (Nat → Nat) := ⟨by
  intro a b
  apply Iff.intro
  · intro h
    unfold BigO.le
    unfold lt at h
    simp_all
    and_intros
    · exists 1
      exact h 1 Nat.one_pos
    · sorry
  · intro ⟨h₁,h₂⟩
    unfold lt
    unfold BigO.le at h₁ h₂
    simp_all
    sorry
⟩

end LittleO

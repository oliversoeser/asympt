import Asympt.BigO

open Std

namespace LittleO

theorem irrefl (f : Nat → Nat) : ¬littleO f f := by
  intro h
  unfold littleO at h
  sorry

instance lt : LT (Nat → Nat) := ⟨littleO⟩

instance lawful_lt : LawfulOrderLT (Nat → Nat) := ⟨sorry⟩

end LittleO

import Asympt.BigO

open Std

namespace BigTheta

theorem big_theta_iff (f g : Nat → Nat) : f=Θ(g) ↔ f=O(g) ∧ f=Ω(g) := ⟨id, id⟩

instance : Subrelation bigTheta bigO := λh => h.1

/-! # equivalence relation  -/

theorem refl (f : Nat → Nat) : f=Θ(f) := ⟨BigO.refl f, BigO.refl f⟩

theorem symm {f g : Nat → Nat} (h : f=Θ(g)) : g=Θ(f) := ⟨h.2, h.1⟩

theorem trans {f g h : Nat → Nat} (h₁ : f=Θ(g)) (h₂ : g=Θ(h)) : f=Θ(h) :=
  ⟨BigO.trans h₁.1 h₂.1, BigO.trans h₂.2 h₁.2⟩

instance : Refl bigTheta := ⟨refl⟩
instance : Symm bigTheta := ⟨@symm⟩
instance : Trans bigTheta bigTheta bigTheta := ⟨trans⟩

instance equiv : Equivalence bigTheta := ⟨refl, symm, trans⟩

def Quot : Type := Quotient ⟨bigTheta, equiv⟩

/-! # equivalence class algebra -/

-- TODO

end BigTheta

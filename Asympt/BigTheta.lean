import Asympt.BigO

namespace BigTheta

theorem big_theta_iff (f g : Nat → Nat) : f=Θ(g) ↔ f=O(g) ∧ f=Ω(g) := ⟨id, id⟩

-- Big Theta is an equivalence relation

theorem refl (f : Nat → Nat) : f=Θ(f) := ⟨BigO.refl f, BigO.refl f⟩

theorem symm {f g : Nat → Nat} (h : f=Θ(g)) : g=Θ(f) := ⟨h.2, h.1⟩

theorem trans {f g h : Nat → Nat} (h₁ : f=Θ(g)) (h₂ : g=Θ(h)) : f=Θ(h) :=
  ⟨BigO.trans f g h h₁.1 h₂.1, BigO.trans h g f h₂.2 h₁.2⟩

instance equiv : Equivalence bigTheta := ⟨refl, symm, trans⟩

-- Functions (Nat → Nat) are a setoid under Big Theta
instance setoid : Setoid (Nat → Nat) := ⟨bigTheta, equiv⟩

end BigTheta

import Asympt.BigO

namespace BigTheta

-- Big Theta is an equivalence relation

theorem refl (f : Nat → Nat) : bigTheta f f := ⟨BigO.refl f, BigO.refl f⟩

theorem symm {f g : Nat → Nat} (h : bigTheta f g) : bigTheta g f := ⟨h.2, h.1⟩

theorem trans {f g h : Nat → Nat} (h₁ : bigTheta f g) (h₂ : bigTheta g h) : bigTheta f h :=
  ⟨BigO.trans f g h h₁.1 h₂.1, BigO.trans h g f h₂.2 h₁.2⟩

instance : Equivalence bigTheta where
  refl := refl
  symm := symm
  trans := trans

end BigTheta

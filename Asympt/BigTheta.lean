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

instance : Setoid (Nat → Nat) := ⟨bigTheta, equiv⟩

/--
The type of equivalence classes of functions `Nat → Nat` under Big Θ.
-/
def FunC : Type := Quotient ⟨bigTheta, equiv⟩

/-! # equivalence class algebra -/

instance : Zero FunC := ⟨.mk' (λ_ => 0)⟩

instance : One FunC := ⟨.mk' (λ_ => 1)⟩

def add (f g : Nat → Nat) : Nat → Nat := λ n => f n + g n

def add_theta {f₁ g₁ f₂ g₂ : Nat → Nat} (hf : f₁=Θ(f₂)) (hg : g₁=Θ(g₂)) : (add f₁ g₁)=Θ(add f₂ g₂) := by
  unfold bigTheta
  apply And.intro
  · sorry
  · sorry

def addC (f g : Nat → Nat) : FunC := .mk' (add f g)

theorem addC_theta (f₁ g₁ f₂ g₂ : Nat → Nat) (hf : f₁=Θ(f₂)) (hg : g₁=Θ(g₂)) : addC f₁ g₁ = addC f₂ g₂ :=
  Quotient.sound (add_theta hf hg)

instance : Add FunC := ⟨λ f g => Quotient.lift₂ addC addC_theta f g⟩

end BigTheta

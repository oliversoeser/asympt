instance : HMul Nat (Nat → Nat) (Nat → Nat) where
  hMul c f := λn => c * f n

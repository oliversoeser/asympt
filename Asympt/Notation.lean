instance : HAdd Nat (Nat → Nat) (Nat → Nat) where
  hAdd c f := λn => c + f n

instance : HAdd (Nat → Nat) Nat (Nat → Nat) where
  hAdd f c := λn => f n + c

instance : HSub Nat (Nat → Nat) (Nat → Nat) where
  hSub c f := λn => c - f n

instance : HSub (Nat → Nat) Nat (Nat → Nat) where
  hSub f c := λn => f n - c

instance : HMul Nat (Nat → Nat) (Nat → Nat) where
  hMul c f := λn => c * f n

instance : HMul (Nat → Nat) Nat (Nat → Nat) where
  hMul f c := λn => f n * c

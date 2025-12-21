-- Function Addition
instance : HAdd Nat (Nat → Nat) (Nat → Nat) where
  hAdd c f := λn => c + f n

instance : HAdd (Nat → Nat) Nat (Nat → Nat) where
  hAdd f c := λn => f n + c

instance : Add (Nat → Nat) where
  add f g := λn => f n + g n

-- Function Subtraction
instance : HSub Nat (Nat → Nat) (Nat → Nat) where
  hSub c f := λn => c - f n

instance : HSub (Nat → Nat) Nat (Nat → Nat) where
  hSub f c := λn => f n - c

instance : Sub (Nat → Nat) where
  sub f g := λn => f n - g n

-- Function Multiplication
instance : HMul Nat (Nat → Nat) (Nat → Nat) where
  hMul c f := λn => c * f n

instance : HMul (Nat → Nat) Nat (Nat → Nat) where
  hMul f c := λn => f n * c

instance : Mul (Nat → Nat) where
  mul f g := λn => f n * g n

-- Function Exponentiation
instance : HPow (Nat → Nat) Nat (Nat → Nat) where
  hPow f c := λn => (f n) ^ c

-- List Addition
open List

def add_list : List Nat → List Nat → List Nat
  | h₁ :: t₁, h₂ :: t₂ => (h₁ + h₂) :: add_list t₁ t₂
  | l, [] => l
  | [], l => l

instance : Add (List Nat) := ⟨add_list⟩

-- List Convolution
def conv_list : List Nat → List Nat → List Nat
  | [], _ => []
  | h :: t, l => (map (λn => n * h) l) + (0 :: conv_list t l)

instance : Mul (List Nat) := ⟨conv_list⟩

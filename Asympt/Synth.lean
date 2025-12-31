import Batteries

inductive CExpr
  | n
  | zero
  | one
  | lg (x : CExpr)
  | add (x y : CExpr)
  | sub (x y : CExpr)
  | mul (x y : CExpr)
  | div (x y : CExpr)
  deriving Repr, DecidableEq

open List CExpr

def eval (e : CExpr) (x : Nat) : Nat := match e with
  | n => x
  | zero => 0
  | one => 1
  | lg a => Nat.log2 (eval a x)
  | add a b => eval a x + eval b x
  | sub a b => eval a x - eval b x
  | mul a b => eval a x * eval b x
  | div a b => eval a x / eval b x

def norm (e : CExpr) : CExpr := match e with
  | lg zero => zero
  | lg one => zero
  | lg (mul x y) => add (lg x) (lg y)
  | lg (div x y) => sub (lg x) (lg y)
  | add x zero => x
  | add zero x => x
  | sub x zero => x
  | mul x one => x
  | mul one x => x
  | mul _ zero => zero
  | mul zero _ => zero
  | div x one => x
  | div zero _ => zero
  | _ => e

def initial : List CExpr := [n, zero, one]

def evolve (l : List CExpr) : List CExpr :=
  (map (λe => lg e) l) ++
  (map (λ(e₁,e₂) => add e₁ e₂) (l.product l)) ++
  (map (λ(e₁,e₂) => sub e₁ e₂) (l.product l)) ++
  (map (λ(e₁,e₂) => mul e₁ e₂) (l.product l)) ++
  (map (λ(e₁,e₂) => div e₁ e₂) (l.product l))

def dedup := List.pwFilter λ(e₁ e₂ : CExpr) => e₁ ≠ e₂

def next (l : List CExpr) : List CExpr := dedup (l ++ map norm (evolve l))

def upto' (i : Nat) (n : Nat) : List Nat :=
  if (i < n) then i :: (upto' (i+1) n) else [i]

def upto (n : Nat) : List Nat := upto' 0 n

def samples (f : Nat → Nat) (n : Nat) : List (Nat × Nat) :=
  map (λx => (x, f x)) (upto n)

def check (f : Nat → Nat) (n : Nat) (e : CExpr) : Bool :=
  foldl and true (map (λ(x, y) => eval e x == y) (samples f n))

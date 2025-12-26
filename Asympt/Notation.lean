import Asympt.Basic

syntax term "=O(" term ")" : term
syntax term "=o(" term ")" : term
syntax term "=Ω(" term ")" : term
syntax term "=ω(" term ")" : term
syntax term "=Θ(" term ")" : term

macro_rules
  | `($f:term=O($g:term)) => `(bigO $f $g)
  | `($f:term=o($g:term)) => `(littleO $f $g)
  | `($f:term=Ω($g:term)) => `(bigOmega $f $g)
  | `($f:term=ω($g:term)) => `(littleOmega $f $g)
  | `($f:term=Θ($g:term)) => `(bigTheta $f $g)

syntax term "≠O(" term ")" : term
syntax term "≠o(" term ")" : term
syntax term "≠Ω(" term ")" : term
syntax term "≠ω(" term ")" : term
syntax term "≠Θ(" term ")" : term

macro_rules
  | `($f:term≠O($g:term)) => `(¬bigO $f $g)
  | `($f:term≠o($g:term)) => `(¬littleO $f $g)
  | `($f:term≠Ω($g:term)) => `(¬bigOmega $f $g)
  | `($f:term≠ω($g:term)) => `(¬littleOmega $f $g)
  | `($f:term≠Θ($g:term)) => `(¬bigTheta $f $g)

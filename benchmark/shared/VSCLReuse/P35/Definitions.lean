import Mathlib

namespace VSCLReuse

abbrev P35Vector (k : ℕ) := Fin k → ℝ
abbrev P35Matrix (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

def p35StrictLower {k : ℕ} (M : P35Matrix k) : Prop :=
  ∀ i j, i ≤ j → M i j = 0

def p35StrictUpper {k : ℕ} (M : P35Matrix k) : Prop :=
  ∀ i j, j ≤ i → M i j = 0

noncomputable def p35Outer {k : ℕ}
    (u v : P35Vector k) : P35Matrix k :=
  Matrix.vecMulVec u v

def p35LastBasis (k : ℕ) : P35Vector (k + 1) :=
  fun i => if i = Fin.last k then 1 else 0

end VSCLReuse

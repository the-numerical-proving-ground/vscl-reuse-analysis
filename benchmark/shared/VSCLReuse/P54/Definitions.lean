import Mathlib

namespace VSCLReuse

/-! Paper-scoped source-order model for Langlois--Louvet, ARITH 2007, Lemma 1.
    The paper's equation (3) states both forward and inverse relative rounding
    laws; retaining the latter is necessary for its inequality (8). -/
structure P54FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  inverse_add : ∀ x y : ℝ, ∃ ε : ℝ,
    |ε| ≤ u ∧ x + y = fl_add x y * (1 + ε)
  inverse_mul : ∀ x y : ℝ, ∃ ε : ℝ,
    |ε| ≤ u ∧ x * y = fl_mul x y * (1 + ε)

noncomputable def p54Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

def P54GammaValid (u : ℝ) (k : ℕ) : Prop := (k : ℝ) * u < 1

noncomputable def p54PolyDesc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => a * x ^ rest.length + p54PolyDesc x rest

noncomputable def p54AbsDesc (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => |a| * |x| ^ rest.length + p54AbsDesc x rest

noncomputable def p54Horner (fp : P54FPModel) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | a :: rest => rest.foldl (fun y b => fp.fl_add (fp.fl_mul x y) b) a

noncomputable def p54SumCoeffs (a b : List ℝ) : List ℝ :=
  List.zipWith (· + ·) a b

noncomputable def p54RoundedSumCoeffs (fp : P54FPModel)
    (a b : List ℝ) : List ℝ :=
  List.zipWith fp.fl_add a b

/-- The complete pair of displayed inequalities (7) and (8), with the
    paper's degree n represented by coefficient lists of length n+1. -/
def P54Lemma1Statement (fp : P54FPModel) (x : ℝ)
    (n : ℕ) (a b : List ℝ) : Prop :=
  a.length = n + 1 → b.length = n + 1 →
  P54GammaValid fp.u (2 * n + 1) →
  |p54PolyDesc x (p54SumCoeffs a b) -
      p54Horner fp x (p54RoundedSumCoeffs fp a b)| ≤
        p54Gamma fp.u (2 * n + 1) *
          p54AbsDesc x (p54SumCoeffs a b) ∧
  p54AbsDesc x (p54SumCoeffs a b) ≤
    (1 + fp.u) ^ (2 * n + 1) *
      p54Horner fp |x|
        ((p54RoundedSumCoeffs fp a b).map abs)

end VSCLReuse

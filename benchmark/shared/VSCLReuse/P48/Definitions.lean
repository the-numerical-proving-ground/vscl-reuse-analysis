import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-- The high-precision accumulation and final low-precision cast of MP Setting 2.3. -/
structure P48FPModel where
  uHigh : ℝ
  uHigh_nonneg : 0 ≤ uHigh
  flHighAdd : ℝ → ℝ → ℝ
  flHighAdd_zero : ∀ x : ℝ, flHighAdd 0 x = x
  modelHighAdd : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ uHigh ∧ flHighAdd x y = (x + y) * (1 + δ)
  uLow : ℝ
  uLow_nonneg : 0 ≤ uLow
  uHigh_le_low : uHigh ≤ uLow
  castDown : ℝ → ℝ
  castDown_model : ∀ x : ℝ, ∃ δ : ℝ,
    |δ| ≤ uLow ∧ castDown x = x * (1 + δ)

noncomputable def p48Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P48GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

/-- Exact products summed with high-precision additions. -/
noncomputable def p48HighDot (fp : P48FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.flHighAdd acc (x i * y i)) 0

/-- MP Setting 2.3: exact products, high-precision sum, low-precision cast. -/
noncomputable def p48MixedDot (fp : P48FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  fp.castDown (p48HighDot fp n x y)

end VSCLReuse

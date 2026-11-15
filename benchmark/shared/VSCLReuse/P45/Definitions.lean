import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Graillat–Jézéquel–Mary–Molina, two-bucket one-row adaptive SpMV. -/

structure P45FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

noncomputable def p45Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P45GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p45RecursiveSum (fp : P45FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p45BlockDot (fp : P45FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p45AdaptiveRow (fp₁ fp₂ : P45FPModel) (n : ℕ)
    (a₁ x₁ a₂ x₂ : Fin n → ℝ) : ℝ :=
  p45RecursiveSum fp₁ 2 (Fin.cons
    (p45BlockDot fp₁ n a₁ x₁)
    (fun _ => p45BlockDot fp₂ n a₂ x₂))

/-- Algorithm 3.1 for a variable number of buckets in one sparse row. -/
noncomputable def p45AdaptiveRowMany (q n : ℕ) (outer : P45FPModel)
    (bucket : Fin q → P45FPModel)
    (a x : Fin q → Fin n → ℝ) : ℝ :=
  p45RecursiveSum outer q
    (fun k => p45BlockDot (bucket k) n (a k) (x k))

end VSCLReuse

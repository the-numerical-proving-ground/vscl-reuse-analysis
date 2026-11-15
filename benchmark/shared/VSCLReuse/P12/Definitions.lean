import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

namespace VSCLReuse

open scoped BigOperators

/-- The standard relative-error model used in equations (2.1)--(2.2). -/
structure P12FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P12Matrix (n : ℕ) := Fin n → Fin n → ℝ

/-- Exact matrix multiplication in the paper's real-arithmetic analysis. -/
noncomputable def p12MatMul {n : ℕ}
    (A B : P12Matrix n) : P12Matrix n :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Componentwise absolute value of a matrix. -/
noncomputable def p12AbsMatrix {n : ℕ}
    (A : P12Matrix n) : P12Matrix n :=
  fun i j => |A i j|

/-- The accumulated rounding-error constant from equation (2.2). -/
noncomputable def p12Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

/-- The usual guard under which `p12Gamma` is valid. -/
def P12GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

/-- Sequentially accumulated floating-point dot product. -/
noncomputable def p12RoundedDotProduct (fp : P12FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Matrix multiplication computed entry by entry with rounded dot products. -/
noncomputable def p12RoundedMatMul (fp : P12FPModel) {n : ℕ}
    (A B : P12Matrix n) : P12Matrix n :=
  fun i j => p12RoundedDotProduct fp n (A i) (fun k => B k j)

/-- Starting from `X`, perform `k` further exact multiplications by `X`. -/
noncomputable def p12PowerSteps {n : ℕ} (X : P12Matrix n) :
    ℕ → P12Matrix n
  | 0 => X
  | k + 1 => p12MatMul (p12PowerSteps X k) X

/-- Starting from `X`, perform `k` further rounded multiplications by `X`. -/
noncomputable def p12RoundedPowerSteps (fp : P12FPModel) {n : ℕ}
    (X : P12Matrix n) : ℕ → P12Matrix n
  | 0 => X
  | k + 1 => p12RoundedMatMul fp (p12RoundedPowerSteps fp X k) X

end VSCLReuse

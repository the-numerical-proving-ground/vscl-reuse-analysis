import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Paper-local two-precision residual computation from Carson and Higham, Section 2. -/

structure P40FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

abbrev P40Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p40Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P40GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p40MatMul {m n p : ℕ}
    (A : P40Matrix m n) (B : P40Matrix n p) : P40Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p40RoundedDotProduct (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p40RoundedMatMul (fp : P40FPModel) {m n p : ℕ}
    (A : P40Matrix m n) (B : P40Matrix n p) : P40Matrix m p :=
  fun i j => p40RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p40RoundedMatVec (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => p40RoundedDotProduct fp n (A i) x

noncomputable def p40HighResidual (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_sub (b i) (p40RoundedMatVec fp n A x i)

noncomputable def p40StoredResidual (fpHi fpLo : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fpLo.fl_mul (p40HighResidual fpHi n A x b i) 1

end VSCLReuse

import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-- The standard relative-error model used for the triangular row solves in
    equations (3.8) and (3.25). -/
structure P15FPModel where
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

abbrev P15Matrix (m n : ℕ) := Fin m → Fin n → ℝ

/-- The accumulated rounding-error constant used in equation (3.25). -/
noncomputable def p15Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P15GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p15Transpose {m n : ℕ}
    (A : P15Matrix m n) : P15Matrix n m :=
  fun i j => A j i

noncomputable def p15MatMul {m n p : ℕ}
    (A : P15Matrix m n) (B : P15Matrix n p) : P15Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p15Residual {m n : ℕ}
    (Q : P15Matrix m n) (R : P15Matrix n n)
    (X : P15Matrix m n) : P15Matrix m n :=
  fun i j => p15MatMul Q R i j - X i j

noncomputable def p15VecNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, x j ^ 2

noncomputable def p15VecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p15VecNormSq x)

noncomputable def p15FrobNormSq {m n : ℕ}
    (A : P15Matrix m n) : ℝ :=
  ∑ i : Fin m, p15VecNormSq (A i)

noncomputable def p15FrobNorm {m n : ℕ}
    (A : P15Matrix m n) : ℝ :=
  Real.sqrt (p15FrobNormSq A)

/-- Auxiliary recurrence for the rounded forward substitution applied to
    `Rᵀ qᵢ = xᵢ`. -/
noncomputable def p15ForwardSubSteps (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      p15ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p15ForwardSub (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p15ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

/-- The matrix `Q̂` produced by solving every row system `q̂ᵢᵀ R̂ = xᵢᵀ`. -/
noncomputable def p15RoundedQ (fp : P15FPModel) {m n : ℕ}
    (X : P15Matrix m n) (R : P15Matrix n n) : P15Matrix m n :=
  fun i => p15ForwardSub fp n (p15Transpose R) (X i)

/-- Equations (3.25)--(3.28), expressed as the precise implication needed
    after the row-solve backward error has been obtained. -/
def P15RowPerturbationsControlled (fp : P15FPModel) {m n : ℕ}
    (X : P15Matrix m n) (R : P15Matrix n n) (xNorm : ℝ) : Prop :=
  let Q := p15RoundedQ fp X R
  ∀ (i : Fin m) (deltaL : P15Matrix n n),
    (∀ k j, |deltaL k j| ≤ p15Gamma fp.u n * |R j k|) →
    (∀ k, ∑ j : Fin n,
      (p15Transpose R k j + deltaL k j) * Q i j = X i k) →
    p15VecNorm (p15Residual Q R X i) ≤
      ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
        p15VecNorm (Q i)

end VSCLReuse

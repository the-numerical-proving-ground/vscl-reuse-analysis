import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Blanchard–Higham–Mary, Algorithm 3.1: recursive block sums with a
power-of-two pairwise sum of the block results. -/

structure P42FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)

noncomputable def p42Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P42GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p42RecursiveSum (fp : P42FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

private lemma p42LeftLt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ]
  omega

private lemma p42RightLt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val + 2 ^ r < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ]
  omega

noncomputable def p42PairwiseSum (fp : P42FPModel) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, v => v ⟨0, by norm_num⟩
  | r + 1, v => fp.fl_add
      (p42PairwiseSum fp r (fun i => v ⟨i.val, p42LeftLt r i⟩))
      (p42PairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, p42RightLt r i⟩))

noncomputable def p42FABsum (fp : P42FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ) : ℝ :=
  p42PairwiseSum fp r (fun i => p42RecursiveSum fp b (x i))

/-- Section 2.2, equation (2.3): recursive local sums, then recursive accumulation
of the block totals. -/
noncomputable def p42BlockedRecursiveSum (fp : P42FPModel) (q b : ℕ)
    (x : Fin q → Fin b → ℝ) : ℝ :=
  p42RecursiveSum fp q (fun i => p42RecursiveSum fp b (x i))

end VSCLReuse

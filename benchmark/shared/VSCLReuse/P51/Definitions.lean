import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Private candidate model for Plonka–Schumacher–Tasche, Lemma 3.2. -/
structure P51FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = x * y * (1 + δ)

noncomputable def p51Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

def P51GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

noncomputable def p51Dot (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) : ℝ :=
  match k with
  | 0 => 0
  | k' + 1 =>
      Fin.foldl k' (fun acc t => fp.fl_add acc
        (fp.fl_mul (a t.succ) (x t.succ)))
        (fp.fl_mul (a 0) (x 0))

noncomputable def p51Sign (a : ℝ) : ℝ :=
  if a = 0 then 0 else a / |a|

/-- An ordered enumeration of exactly the nonzero columns in each source row. -/
structure P51SparseSchedule {m n : ℕ} (A : Fin m → Fin n → ℝ) (l : ℕ) where
  count : Fin m → ℕ
  count_le : ∀ i, count i ≤ l
  col : ∀ i, Fin (count i) → Fin n
  col_injective : ∀ i, Function.Injective (col i)
  col_nonzero : ∀ i t, A i (col i t) ≠ 0
  covers : ∀ i j, A i j ≠ 0 → ∃ t, col i t = j

noncomputable def p51SparseMatVec (fp : P51FPModel) {m n l : ℕ}
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P51SparseSchedule A l) : Fin m → ℝ :=
  fun i => p51Dot fp (schedule.count i)
    (fun t => Ahat i (schedule.col i t))
    (fun t => x (schedule.col i t))

end VSCLReuse

import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Paper-local exact objects for Proposition 6.2.  A lower-triangular
Cholesky factor determines the diagonal entries and determinant through its
row energies and squared diagonal entries. -/

/-- The square of a Cholesky diagonal entry. -/
noncomputable def p22DiagSquare {n : ℕ} (L : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  (L i i) ^ 2

/-- The diagonal entry of `L * Lᵀ`, written as a lower-triangular row energy. -/
noncomputable def p22RowEnergy {n : ℕ} (L : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  p22DiagSquare L i +
    ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val), (L i k) ^ 2

/-- The Hadamard measure in Cholesky coordinates. -/
noncomputable def p22HadamardMeasure {n : ℕ} (L : Fin n → Fin n → ℝ) : ℝ :=
  (∏ i, p22DiagSquare L i) / ∏ i, p22RowEnergy L i

/-- A lower Cholesky factor is diagonal when every entry below its diagonal vanishes. -/
def p22IsDiagonalCholesky {n : ℕ} (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ i k, k.val < i.val → L i k = 0

/-- Row scaling of a lower Cholesky factor by a diagonal matrix. -/
noncomputable def p22ScaleRows {n : ℕ} (s : Fin n → ℝ)
    (L : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i k ↦ s i * L i k

end VSCLReuse

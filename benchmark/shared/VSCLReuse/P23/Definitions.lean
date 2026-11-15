import Mathlib

namespace VSCLReuse

open scoped BigOperators NNReal

/-- Entrywise complex absolute value, regarded as a nonnegative-real matrix. -/
noncomputable def p23AbsMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℝ≥0 :=
  fun i j ↦ ‖A i j‖₊

/-- The paper's strictly upper-triangular condition. -/
def p23StrictUpper {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, j.val ≤ i.val → N i j = 0

/-- The truncated binomial majorant in Lemma 2.1.  The condition `r < n`
is equivalent to summing through `min(k,n-1)`. -/
noncomputable def p23PowerMajorant {n : ℕ} (k : ℕ) (δ : ℝ≥0)
    (N : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℝ≥0 :=
  fun i j ↦
    ∑ r ∈ Finset.range (k + 1),
      if r < n then
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (p23AbsMatrix N ^ r) i j
      else 0

end VSCLReuse

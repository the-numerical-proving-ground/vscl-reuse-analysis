import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  sorry

end VSCLReuse

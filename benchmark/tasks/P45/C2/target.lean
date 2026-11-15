import VSCLReuse.P45.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  sorry

end VSCLReuse

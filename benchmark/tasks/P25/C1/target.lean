import VSCLReuse.P25.Definitions

namespace VSCLReuse

open Filter

/-- P25-C1: the R-quadratic residual-ratio core of Theorem 2.3. -/
theorem p25_c1_choice_two_r_quadratic_core
    (residual : ℕ → ℝ) (B : ℝ)
    (hpos : ∀ k, 0 < residual k) (hB : 0 < B)
    (hstep : ∀ k,
      residual (k + 2) ≤
        ((p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)) *
          residual (k + 1))
    (hsmall :
      2 * p25ResidualRatio residual 0 + 2 * B * residual 0 ≤ 1) :
    let D := 1 / (2 * p25ResidualRatio residual 0)
    1 < D ∧
      p25ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k,
        0 < p25ScaledResidualRatio residual D k ∧
        p25ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0) := by
  -- PROOF_START P25-C1-H001
  sorry

end VSCLReuse

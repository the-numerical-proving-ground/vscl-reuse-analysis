import Mathlib

namespace VSCLReuse

/-- The ratio of two consecutive residual norms used in the proof of Theorem 2.3. -/
noncomputable def p25ResidualRatio (residual : ℕ → ℝ) (k : ℕ) : ℝ :=
  residual (k + 1) / residual k

/-- The scaled residual ratio introduced in the R-order part of Theorem 2.3. -/
noncomputable def p25ScaledResidualRatio (residual : ℕ → ℝ) (D : ℝ) (k : ℕ) : ℝ :=
  D * p25ResidualRatio residual k

end VSCLReuse

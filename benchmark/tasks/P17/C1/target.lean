import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

/-- P17-C1: the square-matrix error-transport core of Lemma 4.1. -/
theorem p17_c1_lemma4_1_core {n : ℕ} (data : P17Lemma41CoreData n) :
    ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ ≤
        2 * p17CoreCoefficient data.eps data.d * data.xScale ∧
    ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
        (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
  -- PROOF_START P17-C1-H001
  sorry

end VSCLReuse

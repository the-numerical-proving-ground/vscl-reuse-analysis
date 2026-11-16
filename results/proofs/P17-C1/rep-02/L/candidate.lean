import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

private lemma p17Sym_norm_le {n : ℕ} (A : P17ComplexMatrix n) : ‖p17Sym A‖ ≤ ‖A‖ := by
  calc
    ‖p17Sym A‖ = (1 / 2 : ℝ) * ‖A + star A‖ := by
      simp [p17Sym, norm_smul]
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖star A‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖A‖ := by rw [norm_star]; ring

private lemma p17Sym_sub {n : ℕ} (A B : P17ComplexMatrix n) :
    p17Sym (A - B) = p17Sym A - p17Sym B := by
  calc
    p17Sym (A - B) = (2 : ℂ)⁻¹ • ((A + star A) - (B + star B)) := by
      rw [p17Sym, star_sub]
      congr 1
      abel
    _ = p17Sym A - p17Sym B := by simp [p17Sym, smul_sub]

private lemma p17Sym_selfadjoint {n : ℕ} (A : P17ComplexMatrix n)
    (hA : star A = A) : p17Sym A = A := by
  rw [p17Sym, hA]
  ext i j
  simp [Matrix.smul_apply]
  ring

/-- P17-C1: the square-matrix error-transport core of Lemma 4.1. -/
theorem p17_c1_lemma4_1_core {n : ℕ} (data : P17Lemma41CoreData n) :
    ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ ≤
        2 * p17CoreCoefficient data.eps data.d * data.xScale ∧
    ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
        (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
  -- PROOF_START P17-C1-H001
  have hRecoverX : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by simp only [Matrix.mul_assoc]
      _ = data.P * data.Sigma * star data.Q := by
        rw [data.q_unitary_left, Matrix.mul_one,
          Matrix.mul_assoc data.P data.fSigma data.recoveryDiagonal,
          data.singular_recovery]
  have hRecoverH : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.Q * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by simp only [Matrix.mul_assoc]
      _ = data.Q * data.Sigma * star data.Q := by
        rw [data.q_unitary_left, Matrix.mul_one,
          Matrix.mul_assoc data.Q data.fSigma data.recoveryDiagonal,
          data.singular_recovery]
  have hForward : data.fXbar - data.U * data.fHbar = data.U * data.EH - data.EY := by
    have hY : data.fXbar + data.EY = data.U * (data.fHbar + data.EH) := by
      rw [← data.y_forward, data.y_polar, data.hy_perturbed]
    rw [Matrix.mul_add] at hY
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - data.U * data.fHbar - data.EY := by abel
      _ = data.U * data.EH - data.EY := by rw [hY]; abel
  have hTransport : data.Xbar - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z := by
    rw [← hForward, Matrix.sub_mul, hRecoverX, Matrix.mul_assoc, hRecoverH]
  have hForwardBound : ‖data.U * data.EH - data.EY‖ ≤
      2 * data.eps * data.fScale := by
    calc
      ‖data.U * data.EH - data.EY‖ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ :=
        norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ 2 * data.eps * data.fScale := by
        linarith [data.eh_bound, data.ey_bound]
  have hBarBound : ‖data.Xbar - data.U * data.Hbar‖ ≤
      (2 * data.eps * data.d) * data.xScale := by
    calc
      ‖data.Xbar - data.U * data.Hbar‖ =
          ‖(data.U * data.EH - data.EY) * data.Z‖ := by rw [hTransport]
      _ ≤ ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ := by
        exact mul_le_mul_of_nonneg_right hForwardBound (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) := by
        exact mul_le_mul_of_nonneg_left data.z_scaled_bound
          (mul_nonneg (by norm_num) data.eps_nonneg)
      _ = (2 * data.eps * data.d) * data.xScale := by ring
  have hXperturb : ‖data.X - data.Xbar‖ ≤ data.eps * data.xScale := by
    have hEq : data.X - data.Xbar = -data.EX := by rw [data.xbar_eq]; abel
    rw [hEq, norm_neg]
    exact data.ex_bound
  have hXBound : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖data.X - data.U * data.Hbar‖ =
          ‖(data.X - data.Xbar) + (data.Xbar - data.U * data.Hbar)‖ := by
        congr 1
        abel
      _ ≤ ‖data.X - data.Xbar‖ + ‖data.Xbar - data.U * data.Hbar‖ :=
        norm_add_le _ _
      _ ≤ data.eps * data.xScale + (2 * data.eps * data.d) * data.xScale :=
        add_le_add hXperturb hBarBound
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        dsimp [p17CoreCoefficient]
        ring
  have hUstarEq : star data.U * data.X - data.Hbar =
      star data.U * (data.X - data.U * data.Hbar) := by
    simp [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left]
  have hUstarBound : ‖star data.U * data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hUstarEq, data.Ustar_left_isometry]
    exact hXBound
  have hEstimateEq : p17HermitianEstimate data.U data.X - data.Hbar =
      p17Sym (star data.U * data.X - data.Hbar) := by
    rw [p17HermitianEstimate, p17Sym_sub,
      p17Sym_selfadjoint data.Hbar data.hbar_selfadjoint]
  have hEstimateBound : ‖p17HermitianEstimate data.U data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hEstimateEq]
    exact (p17Sym_norm_le _).trans hUstarBound
  constructor
  · calc
      ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ =
          ‖(data.X - data.U * data.Hbar) +
            data.U * (data.Hbar - p17HermitianEstimate data.U data.X)‖ := by
          congr 1
          rw [Matrix.mul_sub]
          abel
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * (data.Hbar - p17HermitianEstimate data.U data.X)‖ :=
          norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ := by
          rw [data.U_left_isometry]
          congr 1
          exact norm_sub_rev _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          p17CoreCoefficient data.eps data.d * data.xScale :=
          add_le_add hXBound hEstimateBound
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := by
        have hEq : p17HermitianEstimate data.U data.X - data.H =
            (p17HermitianEstimate data.U data.X - data.Hbar) +
              (data.Hbar - data.H) := by abel
        rw [hEq]
        exact norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
          add_le_add hEstimateBound data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by ring

end VSCLReuse

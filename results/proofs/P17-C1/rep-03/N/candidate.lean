import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

private lemma p17_recover_mul {n : ℕ} (P Q A D : P17ComplexMatrix n)
    (hQ : star Q * Q = 1) :
    (P * A * star Q) * (Q * D * star Q) = P * (A * D) * star Q := by
  calc
    (P * A * star Q) * (Q * D * star Q) =
        P * A * (star Q * Q) * D * star Q := by simp only [Matrix.mul_assoc]
    _ = P * (A * D) * star Q := by rw [hQ]; simp [Matrix.mul_assoc]

private lemma p17_sym_sub_norm_le {n : ℕ} (A B : P17ComplexMatrix n)
    (hB : star B = B) : ‖p17Sym A - B‖ ≤ ‖A - B‖ := by
  have hsym : p17Sym A - B = (2 : ℂ)⁻¹ • ((A - B) + star (A - B)) := by
    simp only [p17Sym, star_sub, hB]
    module
  rw [hsym, norm_smul]
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  calc
    (1 / 2 : ℝ) * ‖(A - B) + star (A - B)‖ ≤
        (1 / 2 : ℝ) * (‖A - B‖ + ‖star (A - B)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A - B‖ := by rw [norm_star]; ring

/-- P17-C1: the square-matrix error-transport core of Lemma 4.1. -/
theorem p17_c1_lemma4_1_core {n : ℕ} (data : P17Lemma41CoreData n) :
    ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ ≤
        2 * p17CoreCoefficient data.eps data.d * data.xScale ∧
    ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
        (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
  -- PROOF_START P17-C1-H001
  have hfx : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd,
      p17_recover_mul data.P data.Q data.fSigma data.recoveryDiagonal data.q_unitary_left,
      data.singular_recovery]
    exact data.xbar_svd.symm
  have hfh : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd,
      p17_recover_mul data.Q data.Q data.fSigma data.recoveryDiagonal data.q_unitary_left,
      data.singular_recovery]
    exact data.hbar_svd.symm
  have hdiff : data.fXbar - data.U * data.fHbar =
      data.U * data.EH - data.EY := by
    have hy : data.fXbar + data.EY = data.U * data.fHbar + data.U * data.EH := by
      calc
        data.fXbar + data.EY = data.Yhat := data.y_forward.symm
        _ = data.U * data.HY := data.y_polar
        _ = data.U * data.fHbar + data.U * data.EH := by
          rw [data.hy_perturbed, mul_add]
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - (data.U * data.fHbar + data.EY) := by abel
      _ = (data.U * data.fHbar + data.U * data.EH) -
          (data.U * data.fHbar + data.EY) := by rw [hy]
      _ = data.U * data.EH - data.EY := by abel
  have htransport : data.Xbar - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by rw [hfx, hfh]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
        simp [sub_mul, Matrix.mul_assoc]
      _ = (data.U * data.EH - data.EY) * data.Z := by rw [hdiff]
  have herror : ‖data.U * data.EH - data.EY‖ ≤ 2 * data.eps * data.fScale := by
    calc
      ‖data.U * data.EH - data.EY‖ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ :=
        norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ 2 * data.eps * data.fScale := by
        have heh := data.eh_bound
        have hey := data.ey_bound
        linarith
  have hbar_error : ‖data.Xbar - data.U * data.Hbar‖ ≤
      2 * data.d * data.eps * data.xScale := by
    rw [htransport]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right herror (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound (by linarith [data.eps_nonneg])
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have hXeq : data.X - data.U * data.Hbar =
      (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    abel
  have hX : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hXeq]
    calc
      ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ ≤
          ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale + data.eps * data.xScale :=
        add_le_add hbar_error data.ex_bound
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        unfold p17CoreCoefficient
        ring
  have hUXeq : star data.U * (data.X - data.U * data.Hbar) =
      star data.U * data.X - data.Hbar := by
    rw [mul_sub, ← Matrix.mul_assoc, data.unitary_left, one_mul]
  have hUX : ‖star data.U * data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [← hUXeq, data.Ustar_left_isometry]
    exact hX
  have hhat : ‖p17HermitianEstimate data.U data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    exact (p17_sym_sub_norm_le (star data.U * data.X) data.Hbar
      data.hbar_selfadjoint).trans hUX
  constructor
  · have heq : data.X - data.U * p17HermitianEstimate data.U data.X =
        (data.X - data.U * data.Hbar) -
          data.U * (p17HermitianEstimate data.U data.X - data.Hbar) := by
      simp [mul_sub]
    rw [heq]
    calc
      ‖(data.X - data.U * data.Hbar) -
          data.U * (p17HermitianEstimate data.U data.X - data.Hbar)‖ ≤
          ‖data.X - data.U * data.Hbar‖ +
            ‖data.U * (p17HermitianEstimate data.U data.X - data.Hbar)‖ :=
        norm_sub_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ := by
        rw [data.U_left_isometry]
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          p17CoreCoefficient data.eps data.d * data.xScale := add_le_add hX hhat
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := by
        have heq : p17HermitianEstimate data.U data.X - data.H =
            (p17HermitianEstimate data.U data.X - data.Hbar) +
              (data.Hbar - data.H) := by abel
        rw [heq]
        exact norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale := add_le_add hhat data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by ring

end VSCLReuse

import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

private lemma p17_sym_norm_le {n : ℕ} (A : P17ComplexMatrix n) :
    ‖p17Sym A‖ ≤ ‖A‖ := by
  rw [p17Sym, norm_smul]
  have h := norm_add_le A (star A)
  simp only [norm_inv, Complex.norm_ofNat] at *
  simp only [norm_star] at h
  norm_num at *
  calc
    (1 / 2 : ℝ) * ‖A + star A‖ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖A‖) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ‖A‖ := by ring

private lemma p17_sym_sub_selfadjoint {n : ℕ} (A H : P17ComplexMatrix n)
    (hH : star H = H) : p17Sym A - H = p17Sym (A - H) := by
  have hhalf : (2 : ℂ)⁻¹ • (H + H) = H := by
    rw [← two_smul ℂ H, smul_smul]
    simp
  unfold p17Sym
  rw [star_sub, hH]
  calc
    (2 : ℂ)⁻¹ • (A + star A) - H =
        (2 : ℂ)⁻¹ • (A + star A) - (2 : ℂ)⁻¹ • (H + H) := by rw [hhalf]
    _ = (2 : ℂ)⁻¹ • ((A - H) + (star A - H)) := by
      rw [← smul_sub]
      congr 1
      abel

/-- P17-C1: the square-matrix error-transport core of Lemma 4.1. -/
theorem p17_c1_lemma4_1_core {n : ℕ} (data : P17Lemma41CoreData n) :
    ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ ≤
        2 * p17CoreCoefficient data.eps data.d * data.xScale ∧
    ‖p17HermitianEstimate data.U data.X - data.H‖ ≤
        (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
  -- PROOF_START P17-C1-H001
  have hrecoverX : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          (data.P * data.fSigma * (star data.Q * data.Q)) *
            data.recoveryDiagonal * star data.Q := by simp only [mul_assoc]
      _ = data.P * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp [mul_assoc, data.singular_recovery]
  have hrecoverH : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          (data.Q * data.fSigma * (star data.Q * data.Q)) *
            data.recoveryDiagonal * star data.Q := by simp only [mul_assoc]
      _ = data.Q * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp [mul_assoc, data.singular_recovery]
  have hfxbar : data.fXbar =
      data.U * data.fHbar + data.U * data.EH - data.EY := by
    have h : data.fXbar + data.EY =
        data.U * (data.fHbar + data.EH) := by
      rw [← data.y_forward, ← data.hy_perturbed, data.y_polar]
    calc
      data.fXbar = (data.fXbar + data.EY) - data.EY := by abel
      _ = data.U * data.fHbar + data.U * data.EH - data.EY := by
        rw [h, mul_add]
  have hxbar : data.Xbar - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hrecoverX, hrecoverH]
      _ = (data.U * data.EH - data.EY) * data.Z := by
        rw [hfxbar]
        noncomm_ring
  have hx : data.X - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z - data.EX := by
    rw [← hxbar, data.xbar_eq]
    abel
  have hforward : ‖data.U * data.EH - data.EY‖ ≤
      2 * data.eps * data.fScale := by
    calc
      ‖data.U * data.EH - data.EY‖ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ :=
        norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ 2 * data.eps * data.fScale := by
        nlinarith [data.eh_bound, data.ey_bound]
  have htransport : ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
      2 * data.eps * data.d * data.xScale := by
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ :=
            Matrix.frobenius_norm_mul _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right hforward (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound (by nlinarith [data.eps_nonneg])
      _ = 2 * data.eps * data.d * data.xScale := by ring
  have hcore : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hx]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z - data.EX‖ ≤
          ‖(data.U * data.EH - data.EY) * data.Z‖ + ‖data.EX‖ :=
            norm_sub_le _ _
      _ ≤ 2 * data.eps * data.d * data.xScale + data.eps * data.xScale :=
        add_le_add htransport data.ex_bound
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        unfold p17CoreCoefficient
        ring
  have hstarcore : ‖star data.U * data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    have heq : star data.U * data.X - data.Hbar =
        star data.U * (data.X - data.U * data.Hbar) := by
      rw [mul_sub, ← mul_assoc, data.unitary_left, one_mul]
    rw [heq, data.Ustar_left_isometry]
    exact hcore
  have hestimate : ‖p17HermitianEstimate data.U data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [p17HermitianEstimate,
      p17_sym_sub_selfadjoint _ _ data.hbar_selfadjoint]
    exact (p17_sym_norm_le _).trans hstarcore
  constructor
  · have heq : data.X - data.U * p17HermitianEstimate data.U data.X =
        (data.X - data.U * data.Hbar) +
          data.U * (data.Hbar - p17HermitianEstimate data.U data.X) := by
      noncomm_ring
    rw [heq]
    calc
      ‖(data.X - data.U * data.Hbar) +
          data.U * (data.Hbar - p17HermitianEstimate data.U data.X)‖ ≤
          ‖data.X - data.U * data.Hbar‖ +
            ‖data.U * (data.Hbar - p17HermitianEstimate data.U data.X)‖ :=
              norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
            ‖p17HermitianEstimate data.U data.X - data.Hbar‖ := by
              rw [data.U_left_isometry]
              congr 1
              exact norm_sub_rev _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
            p17CoreCoefficient data.eps data.d * data.xScale :=
              add_le_add hcore hestimate
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · calc
      ‖p17HermitianEstimate data.U data.X - data.H‖ =
          ‖(p17HermitianEstimate data.U data.X - data.Hbar) +
            (data.Hbar - data.H)‖ := by congr 1; abel
      _ ≤ ‖p17HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
            data.eps * data.xScale :=
              add_le_add hestimate data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
        ring

end VSCLReuse

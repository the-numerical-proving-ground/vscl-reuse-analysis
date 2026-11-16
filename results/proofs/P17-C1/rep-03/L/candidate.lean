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
  have hfx : data.fXbar * data.Z = data.Xbar := by
    rw [data.fxbar_svd, data.z_svd, data.xbar_svd]
    calc
      (data.P * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star data.Q) data.Q]
            simp [data.q_unitary_left]
      _ = data.P * data.Sigma * star data.Q := by rw [data.singular_recovery]
  have hfh : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.Q * (data.fSigma * data.recoveryDiagonal) * star data.Q := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (star data.Q) data.Q]
            simp [data.q_unitary_left]
      _ = data.Q * data.Sigma * star data.Q := by rw [data.singular_recovery]
  have htransport : data.Xbar - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z := by
    have hy : data.fXbar = data.U * data.fHbar + data.U * data.EH - data.EY := by
      calc
        data.fXbar = data.Yhat - data.EY := by rw [data.y_forward]; abel
        _ = data.U * data.HY - data.EY := by rw [data.y_polar]
        _ = data.U * data.fHbar + data.U * data.EH - data.EY := by
          rw [data.hy_perturbed]
          noncomm_ring
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
            rw [hfx, hfh]
      _ = (data.U * data.EH - data.EY) * data.Z := by
        rw [hy]
        noncomm_ring
  have hresid : data.X - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z - data.EX := by
    rw [data.xbar_eq] at htransport
    calc
      data.X - data.U * data.Hbar =
          (data.X + data.EX - data.U * data.Hbar) - data.EX := by
            abel
      _ = (data.U * data.EH - data.EY) * data.Z - data.EX := by rw [htransport]
  have herror : ‖data.U * data.EH - data.EY‖ ≤ 2 * data.eps * data.fScale := by
    calc
      ‖data.U * data.EH - data.EY‖ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ :=
        norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ data.eps * data.fScale + data.eps * data.fScale :=
        add_le_add data.eh_bound data.ey_bound
      _ = 2 * data.eps * data.fScale := by ring
  have hproduct : ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
      2 * data.d * data.eps * data.xScale := by
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right herror (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound
          (mul_nonneg (by norm_num) data.eps_nonneg)
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have hcore : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hresid]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z - data.EX‖ ≤
          ‖(data.U * data.EH - data.EY) * data.Z‖ + ‖data.EX‖ :=
        norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale + data.eps * data.xScale :=
        add_le_add hproduct data.ex_bound
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        unfold p17CoreCoefficient
        ring
  have hstar : star data.U * data.X - data.Hbar =
      star data.U * (data.X - data.U * data.Hbar) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left, one_mul]
  have hstar_bound : ‖star data.U * data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hstar, data.Ustar_left_isometry]
    exact hcore
  have hsym_norm (A : P17ComplexMatrix n) : ‖p17Sym A‖ ≤ ‖A‖ := by
    calc
      ‖p17Sym A‖ = ‖(2 : ℂ)⁻¹ • (A + star A)‖ := rfl
      _ = ‖(2 : ℂ)⁻¹‖ * ‖A + star A‖ := norm_smul _ _
      _ ≤ ‖(2 : ℂ)⁻¹‖ * (‖A‖ + ‖star A‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖A‖ := by rw [norm_star]; norm_num; ring
  have hsym_self : p17Sym data.Hbar = data.Hbar := by
    unfold p17Sym
    rw [data.hbar_selfadjoint]
    simp [← two_smul ℂ data.Hbar]
  have hsym_sub (A B : P17ComplexMatrix n) :
      p17Sym (A - B) = p17Sym A - p17Sym B := by
    unfold p17Sym
    rw [star_sub]
    module
  have hhat_diff : p17HermitianEstimate data.U data.X - data.Hbar =
      p17Sym (star data.U * data.X - data.Hbar) := by
    rw [hsym_sub, hsym_self]
    rfl
  have hhat_bound : ‖p17HermitianEstimate data.U data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hhat_diff]
    exact (hsym_norm _).trans hstar_bound
  constructor
  · have hfirst_id :
        data.X - data.U * p17HermitianEstimate data.U data.X =
          (data.X - data.U * data.Hbar) -
            data.U * (p17HermitianEstimate data.U data.X - data.Hbar) := by
        rw [Matrix.mul_sub]
        abel
    rw [hfirst_id]
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
          p17CoreCoefficient data.eps data.d * data.xScale :=
        add_le_add hcore hhat_bound
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · have hsecond_id :
        p17HermitianEstimate data.U data.X - data.H =
          (p17HermitianEstimate data.U data.X - data.Hbar) +
            (data.Hbar - data.H) := by abel
    rw [hsecond_id]
    calc
      ‖(p17HermitianEstimate data.U data.X - data.Hbar) +
          (data.Hbar - data.H)‖ ≤
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ +
            ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
        add_le_add hhat_bound data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by
        ring

end VSCLReuse

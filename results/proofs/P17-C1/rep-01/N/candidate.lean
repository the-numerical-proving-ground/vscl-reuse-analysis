import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

private lemma p17Sym_add {n : ℕ} (A B : P17ComplexMatrix n) :
    p17Sym (A + B) = p17Sym A + p17Sym B := by
  ext i j
  simp only [p17Sym, Matrix.smul_apply, Matrix.add_apply, Matrix.star_apply, star_add,
    smul_add]
  abel

private lemma p17Sym_selfadjoint {n : ℕ} (A : P17ComplexMatrix n)
    (hA : star A = A) : p17Sym A = A := by
  rw [p17Sym, hA, ← two_smul ℂ A, smul_smul]
  simp

private lemma p17Sym_norm_le {n : ℕ} (A : P17ComplexMatrix n) :
    ‖p17Sym A‖ ≤ ‖A‖ := by
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  calc
    ‖p17Sym A‖ = (1 / 2 : ℝ) * ‖A + star A‖ := by
      rw [p17Sym, norm_smul, hhalf]
    _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖star A‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖A‖ := by rw [norm_star]; ring

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
          data.recoveryDiagonal * star data.Q := by noncomm_ring
      _ = data.P * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp only [Matrix.mul_one]
        rw [Matrix.mul_assoc data.P data.fSigma data.recoveryDiagonal,
          data.singular_recovery]
  have hRecoverH : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      (data.Q * data.fSigma * star data.Q) *
          (data.Q * data.recoveryDiagonal * star data.Q) =
        data.Q * data.fSigma * (star data.Q * data.Q) *
          data.recoveryDiagonal * star data.Q := by noncomm_ring
      _ = data.Q * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp only [Matrix.mul_one]
        rw [Matrix.mul_assoc data.Q data.fSigma data.recoveryDiagonal,
          data.singular_recovery]
  have htransport : data.fXbar - data.U * data.fHbar =
      data.U * data.EH - data.EY := by
    have hy : data.fXbar + data.EY = data.U * data.fHbar + data.U * data.EH := by
      calc
        data.fXbar + data.EY = data.Yhat := data.y_forward.symm
        _ = data.U * data.HY := data.y_polar
        _ = data.U * data.fHbar + data.U * data.EH := by
          rw [data.hy_perturbed, Matrix.mul_add]
    calc
      data.fXbar - data.U * data.fHbar =
          (data.fXbar + data.EY) - data.EY - data.U * data.fHbar := by abel
      _ = (data.U * data.fHbar + data.U * data.EH) - data.EY -
          data.U * data.fHbar := by rw [hy]
      _ = data.U * data.EH - data.EY := by abel
  have htransport_bound : ‖data.fXbar - data.U * data.fHbar‖ ≤
      2 * data.eps * data.fScale := by
    calc
      ‖data.fXbar - data.U * data.fHbar‖ = ‖data.U * data.EH - data.EY‖ :=
        congrArg norm htransport
      _ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ := norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ data.eps * data.fScale + data.eps * data.fScale :=
        add_le_add data.eh_bound data.ey_bound
      _ = 2 * data.eps * data.fScale := by ring
  have hRecover : data.Xbar - data.U * data.Hbar =
      (data.fXbar - data.U * data.fHbar) * data.Z := by
    calc
      data.Xbar - data.U * data.Hbar =
          data.fXbar * data.Z - data.U * (data.fHbar * data.Z) := by
        rw [hRecoverX, hRecoverH]
      _ = (data.fXbar - data.U * data.fHbar) * data.Z := by
        rw [Matrix.sub_mul, Matrix.mul_assoc]
  have hbar_bound : ‖data.Xbar - data.U * data.Hbar‖ ≤
      2 * data.d * data.eps * data.xScale := by
    rw [hRecover]
    calc
      ‖(data.fXbar - data.U * data.fHbar) * data.Z‖ ≤
          ‖data.fXbar - data.U * data.fHbar‖ * ‖data.Z‖ :=
        Matrix.frobenius_norm_mul _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right htransport_bound (norm_nonneg _)
      _ = (2 * data.eps) * (data.fScale * ‖data.Z‖) := by ring
      _ ≤ (2 * data.eps) * (data.d * data.xScale) :=
        mul_le_mul_of_nonneg_left data.z_scaled_bound (by nlinarith [data.eps_nonneg])
      _ = 2 * data.d * data.eps * data.xScale := by ring
  have hX_rewrite : data.X - data.U * data.Hbar =
      (data.Xbar - data.U * data.Hbar) - data.EX := by
    rw [data.xbar_eq]
    abel
  have hX_bound : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    calc
      ‖data.X - data.U * data.Hbar‖ =
          ‖(data.Xbar - data.U * data.Hbar) - data.EX‖ :=
        congrArg norm hX_rewrite
      _ ≤ ‖data.Xbar - data.U * data.Hbar‖ + ‖data.EX‖ := norm_sub_le _ _
      _ ≤ 2 * data.d * data.eps * data.xScale + data.eps * data.xScale :=
        add_le_add hbar_bound data.ex_bound
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        unfold p17CoreCoefficient
        ring
  have hW : star data.U * data.X - data.Hbar =
      star data.U * (data.X - data.U * data.Hbar) := by
    calc
      star data.U * data.X - data.Hbar =
          star data.U * data.X - (star data.U * data.U) * data.Hbar := by
        rw [data.unitary_left, one_mul]
      _ = star data.U * (data.X - data.U * data.Hbar) := by
        rw [Matrix.mul_sub, Matrix.mul_assoc]
  have hW_bound : ‖star data.U * data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    rw [hW, data.Ustar_left_isometry]
    exact hX_bound
  have hHhat : p17HermitianEstimate data.U data.X =
      data.Hbar + p17Sym (star data.U * data.X - data.Hbar) := by
    have hdecomp : star data.U * data.X =
        data.Hbar + (star data.U * data.X - data.Hbar) := by abel
    calc
      p17HermitianEstimate data.U data.X = p17Sym (star data.U * data.X) := rfl
      _ = p17Sym (data.Hbar + (star data.U * data.X - data.Hbar)) :=
        congrArg p17Sym hdecomp
      _ = p17Sym data.Hbar + p17Sym (star data.U * data.X - data.Hbar) :=
        p17Sym_add _ _
      _ = data.Hbar + p17Sym (star data.U * data.X - data.Hbar) := by
        rw [p17Sym_selfadjoint _ data.hbar_selfadjoint]
  have hSymW_bound : ‖p17Sym (star data.U * data.X - data.Hbar)‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale :=
    (p17Sym_norm_le _).trans hW_bound
  constructor
  · have hresid : data.X - data.U * p17HermitianEstimate data.U data.X =
        (data.X - data.U * data.Hbar) -
          data.U * p17Sym (star data.U * data.X - data.Hbar) := by
      rw [hHhat, Matrix.mul_add]
      abel
    calc
      ‖data.X - data.U * p17HermitianEstimate data.U data.X‖ =
          ‖(data.X - data.U * data.Hbar) -
            data.U * p17Sym (star data.U * data.X - data.Hbar)‖ :=
        congrArg norm hresid
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * p17Sym (star data.U * data.X - data.Hbar)‖ := norm_sub_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p17Sym (star data.U * data.X - data.Hbar)‖ := by
        rw [data.U_left_isometry]
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          p17CoreCoefficient data.eps data.d * data.xScale :=
        add_le_add hX_bound hSymW_bound
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · have hfactor : p17HermitianEstimate data.U data.X - data.H =
        p17Sym (star data.U * data.X - data.Hbar) + (data.Hbar - data.H) := by
      rw [hHhat]
      abel
    calc
      ‖p17HermitianEstimate data.U data.X - data.H‖ =
          ‖p17Sym (star data.U * data.X - data.Hbar) +
            (data.Hbar - data.H)‖ := congrArg norm hfactor
      _ ≤ ‖p17Sym (star data.U * data.X - data.Hbar)‖ +
          ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
        add_le_add hSymW_bound data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by ring

end VSCLReuse

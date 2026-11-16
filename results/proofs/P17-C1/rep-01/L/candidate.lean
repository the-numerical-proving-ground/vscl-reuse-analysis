import VSCLReuse.P17.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius

private lemma p17_sym_sub_selfadjoint_bound {n : ℕ}
    (A B : P17ComplexMatrix n) (hB : star B = B) :
    ‖p17Sym A - B‖ ≤ ‖A - B‖ := by
  have heq : p17Sym A - B = (2 : ℂ)⁻¹ • ((A - B) + star (A - B)) := by
    rw [p17Sym, star_sub, hB]
    ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  rw [heq, norm_smul]
  have hstar : ‖star (A - B)‖ = ‖A - B‖ := norm_star _
  have htri := norm_add_le (A - B) (star (A - B))
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  nlinarith

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
      data.P * data.fSigma * star data.Q *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.P * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by simp only [Matrix.mul_assoc]
      _ = data.P * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp [data.singular_recovery, Matrix.mul_assoc]
  have hrecoverH : data.fHbar * data.Z = data.Hbar := by
    rw [data.fhbar_svd, data.z_svd, data.hbar_svd]
    calc
      data.Q * data.fSigma * star data.Q *
          (data.Q * data.recoveryDiagonal * star data.Q) =
          data.Q * data.fSigma * (star data.Q * data.Q) *
            data.recoveryDiagonal * star data.Q := by simp only [Matrix.mul_assoc]
      _ = data.Q * data.Sigma * star data.Q := by
        rw [data.q_unitary_left]
        simp [data.singular_recovery, Matrix.mul_assoc]
  have htransport : data.Xbar - data.U * data.Hbar =
      (data.U * data.EH - data.EY) * data.Z := by
    have hY : data.fXbar + data.EY = data.U * (data.fHbar + data.EH) := by
      rw [← data.y_forward, ← data.hy_perturbed, ← data.y_polar]
    rw [← hrecoverX, ← hrecoverH]
    calc
      data.fXbar * data.Z - data.U * (data.fHbar * data.Z) =
          (data.fXbar - data.U * data.fHbar) * data.Z := by
            simp [Matrix.sub_mul, Matrix.mul_assoc]
      _ = (data.U * data.EH - data.EY) * data.Z := by
        congr 1
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa [Matrix.mul_add, add_assoc, add_comm, add_left_comm] using hY
  have hEY : ‖data.U * data.EH - data.EY‖ ≤
      2 * data.eps * data.fScale := by
    calc
      _ ≤ ‖data.U * data.EH‖ + ‖data.EY‖ := norm_sub_le _ _
      _ = ‖data.EH‖ + ‖data.EY‖ := by rw [data.U_left_isometry]
      _ ≤ data.eps * data.fScale + data.eps * data.fScale :=
        add_le_add data.eh_bound data.ey_bound
      _ = 2 * data.eps * data.fScale := by ring
  have hXbar : ‖data.Xbar - data.U * data.Hbar‖ ≤
      2 * data.eps * data.d * data.xScale := by
    rw [htransport]
    calc
      ‖(data.U * data.EH - data.EY) * data.Z‖ ≤
          ‖data.U * data.EH - data.EY‖ * ‖data.Z‖ := norm_mul_le _ _
      _ ≤ (2 * data.eps * data.fScale) * ‖data.Z‖ :=
        mul_le_mul_of_nonneg_right hEY (norm_nonneg _)
      _ ≤ 2 * data.eps * data.d * data.xScale := by
        have hh := mul_le_mul_of_nonneg_left data.z_scaled_bound
          (show 0 ≤ 2 * data.eps from
            mul_nonneg (by norm_num) data.eps_nonneg)
        nlinarith
  have hX : ‖data.X - data.U * data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    have heq : data.X - data.U * data.Hbar =
        -data.EX + (data.Xbar - data.U * data.Hbar) := by
      rw [data.xbar_eq]
      abel
    rw [heq]
    calc
      ‖-data.EX + (data.Xbar - data.U * data.Hbar)‖ ≤
          ‖-data.EX‖ + ‖data.Xbar - data.U * data.Hbar‖ := norm_add_le _ _
      _ = ‖data.EX‖ + ‖data.Xbar - data.U * data.Hbar‖ := by rw [norm_neg]
      _ ≤ data.eps * data.xScale + 2 * data.eps * data.d * data.xScale :=
        add_le_add data.ex_bound hXbar
      _ = p17CoreCoefficient data.eps data.d * data.xScale := by
        unfold p17CoreCoefficient
        ring
  have hUX : star data.U * data.X - data.Hbar =
      star data.U * (data.X - data.U * data.Hbar) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, data.unitary_left]
    simp
  have hHbar : ‖p17HermitianEstimate data.U data.X - data.Hbar‖ ≤
      p17CoreCoefficient data.eps data.d * data.xScale := by
    calc
      _ ≤ ‖star data.U * data.X - data.Hbar‖ :=
        p17_sym_sub_selfadjoint_bound _ _ data.hbar_selfadjoint
      _ = ‖data.X - data.U * data.Hbar‖ := by
        rw [hUX, data.Ustar_left_isometry]
      _ ≤ _ := hX
  refine ⟨?_, ?_⟩
  · have heq : data.X - data.U * p17HermitianEstimate data.U data.X =
        (data.X - data.U * data.Hbar) +
          data.U * (data.Hbar - p17HermitianEstimate data.U data.X) := by
      simp [Matrix.mul_sub]
    rw [heq]
    calc
      _ ≤ ‖data.X - data.U * data.Hbar‖ +
          ‖data.U * (data.Hbar - p17HermitianEstimate data.U data.X)‖ :=
        norm_add_le _ _
      _ = ‖data.X - data.U * data.Hbar‖ +
          ‖p17HermitianEstimate data.U data.X - data.Hbar‖ := by
        rw [data.U_left_isometry]
        exact congrArg (fun t : ℝ => ‖data.X - data.U * data.Hbar‖ + t)
          (norm_sub_rev data.Hbar (p17HermitianEstimate data.U data.X))
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          p17CoreCoefficient data.eps data.d * data.xScale :=
        add_le_add hX hHbar
      _ = 2 * p17CoreCoefficient data.eps data.d * data.xScale := by ring
  · have heq : p17HermitianEstimate data.U data.X - data.H =
        (p17HermitianEstimate data.U data.X - data.Hbar) +
          (data.Hbar - data.H) := by abel
    rw [heq]
    calc
      _ ≤ ‖p17HermitianEstimate data.U data.X - data.Hbar‖ +
          ‖data.Hbar - data.H‖ := norm_add_le _ _
      _ ≤ p17CoreCoefficient data.eps data.d * data.xScale +
          data.eps * data.xScale :=
        add_le_add hHbar data.hermitian_polar_bound
      _ = (p17CoreCoefficient data.eps data.d + data.eps) * data.xScale := by ring

end VSCLReuse

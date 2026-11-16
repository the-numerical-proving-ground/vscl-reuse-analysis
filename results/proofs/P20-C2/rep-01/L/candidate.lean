import VSCLReuse.P20.Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace VSCLReuse

/-- Extend the paper-local model with exact square root for use with the
generic floating-point residual theorem. -/
noncomputable def p20AsFPModel (fp : P20FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

/-- P20-C2: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p20_c2_sparse_residual_error
    (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P20GammaValid fp.u (s + 1)) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      p20ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P20-C2-H001
  let F := p20AsFPModel fp
  have hv : NumStability.gammaValid F (s + 1) := hvalid
  cases s with
  | zero =>
      obtain ⟨δ, hδ, hround⟩ := fp.model_sub b 0
      have hγ : fp.u ≤ p20Gamma fp.u 1 := by
        exact NumStability.u_le_gamma F (by decide) hv
      have hbound : |b * (1 + δ) - b| ≤ p20Gamma fp.u 1 * |b| := by
        have heq : b * (1 + δ) - b = b * δ := by ring
        rw [heq, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (le_trans hδ hγ) (abs_nonneg b)
      simpa [p20RoundedResidual, p20RoundedSparseRowProduct,
        p20ExactResidual, p20ResidualErrorMajorant, hround] using hbound
  | succ n =>
      have hn : NumStability.gammaValid F (n + 1) :=
        NumStability.gammaValid_mono F (by omega) hv
      have h := NumStability.conventional_residual_error F (n + 1)
        (fun _ => a) x (fun _ => b) hn hv (0 : Fin (n + 1))
      simpa [NumStability.fl_residual, NumStability.fl_matVec,
        NumStability.fl_dotProduct, p20RoundedResidual,
        p20RoundedSparseRowProduct, p20ExactResidual,
        p20ResidualErrorMajorant, F, p20AsFPModel,
        NumStability.gamma, p20Gamma] using h

end VSCLReuse

import VSCLReuse.P45.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p45AsFPModel (fp : P45FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  have hvalid : NumStability.gammaValid (p45AsFPModel fp) n := by
    simpa only [NumStability.gammaValid, p45AsFPModel, P45GammaValid] using hv
  have h := NumStability.dotProduct_error_bound (p45AsFPModel fp) n a x hvalid
  simpa only [NumStability.fl_dotProduct, p45BlockDot, p45AsFPModel,
    NumStability.gamma, p45Gamma, ← abs_mul] using h

end VSCLReuse

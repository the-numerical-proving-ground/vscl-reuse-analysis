import VSCLReuse.P45.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  let fp' : NumStability.FPModel :=
    { u := fp.u
      u_nonneg := fp.u_nonneg
      fl_add := fp.fl_add
      fl_sub := fun a b => a - b
      fl_mul := fp.fl_mul
      fl_div := fun a b => a / b
      fl_sqrt := Real.sqrt
      fl_add_zero := fp.fl_add_zero
      model_add := fp.model_add
      model_sub := by
        intro a b
        exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
      model_mul := fp.model_mul
      model_div := by
        intro a b _
        exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
      model_sqrt := by
        intro a _
        exact ⟨0, by simpa using fp.u_nonneg, by simp⟩ }
  have hdot : p45BlockDot fp n a x = NumStability.fl_dotProduct fp' n a x := by
    cases n <;> rfl
  have hvalid : NumStability.gammaValid fp' n := hv
  have h := NumStability.dotProduct_error_bound fp' n a x hvalid
  rw [← hdot] at h
  change |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
    p45Gamma fp.u n * ∑ j : Fin n, |a j| * |x j| at h
  simpa only [abs_mul] using h

end VSCLReuse

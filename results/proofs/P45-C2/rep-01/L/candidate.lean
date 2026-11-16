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
  let model : NumStability.FPModel := {
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
      exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
    model_mul := fp.model_mul
    model_div := by
      intro x y _
      exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
    model_sqrt := by
      intro x _
      exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  }
  have hvalid : NumStability.gammaValid model n := hv
  have hbound := NumStability.dotProduct_error_bound model n a x hvalid
  have hdot : NumStability.fl_dotProduct model n a x = p45BlockDot fp n a x := by
    cases n <;> rfl
  have hgamma : NumStability.gamma model n = p45Gamma fp.u n := rfl
  rw [hdot, hgamma] at hbound
  convert hbound using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact abs_mul (a j) (x j)

end VSCLReuse

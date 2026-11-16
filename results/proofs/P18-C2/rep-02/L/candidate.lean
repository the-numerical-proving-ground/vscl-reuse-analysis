import VSCLReuse.P18.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p18AsFPModel (fp : P18FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

/-- P18-C2: the first-step Schur-complement error calculation in Appendix B. -/
theorem p18_c2_first_schur_error
    (fp : P18FPModel) (m r : ℕ)
    (A22 : P18Matrix m m) (L11 : P18Matrix m r)
    (A12 : P18Matrix r m)
    (hvalid : P18GammaValid fp.u r) :
    ∀ i j,
      |p18RoundedSchur fp A22 L11 A12 i j -
          p18ExactSchur A22 L11 A12 i j| ≤
        p18SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P18-C2-H001
  intro i j
  have hvalid' : NumStability.gammaValid (p18AsFPModel fp) r := by
    simpa [NumStability.gammaValid, p18AsFPModel, P18GammaValid] using hvalid
  have hdot := NumStability.dotProduct_error_bound
    (p18AsFPModel fp) r (L11 i) (fun k => A12 k j) hvalid'
  have hdot' :
      |p18RoundedMatMul fp L11 A12 i j - p18MatMul L11 A12 i j| ≤
        p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    simpa [p18RoundedMatMul, p18RoundedDotProduct, p18MatMul,
      p18Gamma, NumStability.fl_dotProduct, NumStability.gamma,
      p18AsFPModel] using hdot
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j)
  have hlocal :
      |fp.fl_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j) -
          (A22 i j - p18RoundedMatMul fp L11 A12 i j)| ≤
        fp.u * |A22 i j - p18RoundedMatMul fp L11 A12 i j| := by
    rw [hsub]
    have heq :
        (A22 i j - p18RoundedMatMul fp L11 A12 i j) * (1 + δ) -
            (A22 i j - p18RoundedMatMul fp L11 A12 i j) =
          (A22 i j - p18RoundedMatMul fp L11 A12 i j) * δ := by ring
    rw [heq, abs_mul]
    calc
      |A22 i j - p18RoundedMatMul fp L11 A12 i j| * |δ| ≤
          |A22 i j - p18RoundedMatMul fp L11 A12 i j| * fp.u :=
        mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
      _ = fp.u * |A22 i j - p18RoundedMatMul fp L11 A12 i j| := by ring
  change
    |fp.fl_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j) -
        (A22 i j - p18MatMul L11 A12 i j)| ≤
      fp.u * |A22 i j - p18RoundedMatMul fp L11 A12 i j| +
        p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  calc
    |fp.fl_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j) -
        (A22 i j - p18MatMul L11 A12 i j)| =
      |(fp.fl_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j) -
          (A22 i j - p18RoundedMatMul fp L11 A12 i j)) +
        (p18MatMul L11 A12 i j - p18RoundedMatMul fp L11 A12 i j)| := by
          congr 1; ring
    _ ≤ |fp.fl_sub (A22 i j) (p18RoundedMatMul fp L11 A12 i j) -
          (A22 i j - p18RoundedMatMul fp L11 A12 i j)| +
        |p18MatMul L11 A12 i j - p18RoundedMatMul fp L11 A12 i j| :=
          abs_add_le _ _
    _ ≤ fp.u * |A22 i j - p18RoundedMatMul fp L11 A12 i j| +
        p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| :=
          add_le_add hlocal (by simpa only [abs_sub_comm] using hdot')

end VSCLReuse

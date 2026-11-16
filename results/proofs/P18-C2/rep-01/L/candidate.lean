import VSCLReuse.P18.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p18ToFPModel (fp : P18FPModel) : NumStability.FPModel where
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
  let a := A22 i j
  let q := p18RoundedMatMul fp L11 A12 i j
  let p := p18MatMul L11 A12 i j
  let s := ∑ k : Fin r, |L11 i k| * |A12 k j|
  have hdot : |q - p| ≤ p18Gamma fp.u r * s := by
    have hv : NumStability.gammaValid (p18ToFPModel fp) r := hvalid
    have h := NumStability.dotProduct_error_bound
      (p18ToFPModel fp) r (L11 i) (fun k => A12 k j) hv
    simpa [a, q, p, s, p18ToFPModel, NumStability.fl_dotProduct,
      NumStability.gamma, p18Gamma, p18RoundedMatMul, p18RoundedDotProduct,
      p18MatMul] using h
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub a q
  change |fp.fl_sub a q - (a - p)| ≤ fp.u * |a - q| + p18Gamma fp.u r * s
  rw [hsub]
  have hid : (a - q) * (1 + δ) - (a - p) = (a - q) * δ + (p - q) := by ring
  rw [hid]
  calc
    |(a - q) * δ + (p - q)| ≤ |(a - q) * δ| + |p - q| := abs_add_le _ _
    _ = |a - q| * |δ| + |q - p| := by rw [abs_mul, abs_sub_comm p q]
    _ ≤ |a - q| * fp.u + p18Gamma fp.u r * s :=
      add_le_add (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)) hdot
    _ = fp.u * |a - q| + p18Gamma fp.u r * s := by ring

end VSCLReuse

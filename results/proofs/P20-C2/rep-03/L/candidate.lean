import VSCLReuse.P20.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p20ToFPModel (fp : P20FPModel) : NumStability.FPModel where
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
  let F := p20ToFPModel fp
  let T := ∑ j : Fin s, a j * x j
  let S := ∑ j : Fin s, |a j| * |x j|
  let y := p20RoundedSparseRowProduct fp s a x
  let g := NumStability.gamma F s
  let G := NumStability.gamma F (s + 1)
  have hvalidF : NumStability.gammaValid F (s + 1) := by
    simpa [NumStability.gammaValid, P20GammaValid, F, p20ToFPModel] using hvalid
  have hsvalid : NumStability.gammaValid F s :=
    NumStability.gammaValid_mono F (Nat.le_succ s) hvalidF
  have hprod : |y - T| ≤ g * S := by
    simpa [y, T, S, g, F, p20ToFPModel, p20RoundedSparseRowProduct,
      NumStability.fl_dotProduct] using
      NumStability.dotProduct_error_bound F s a x hsvalid
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hT : |T| ≤ S := by
    calc
      |T| ≤ ∑ j : Fin s, |a j * x j| := by
        simpa [T] using (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin s => a j * x j))
      _ = S := by simp [S, abs_mul]
  have hg : 0 ≤ g := NumStability.gamma_nonneg F hsvalid
  have huG : fp.u ≤ G := by
    simpa [F, p20ToFPModel, G] using
      (NumStability.u_le_gamma F (Nat.succ_pos s) hvalidF)
  have hcoeff : g + fp.u + fp.u * g ≤ G := by
    have h1valid : NumStability.gammaValid F 1 :=
      NumStability.gammaValid_mono F (by omega : 1 ≤ s + 1) hvalidF
    have hu1 : fp.u ≤ NumStability.gamma F 1 := by
      simpa [F, p20ToFPModel] using
        (NumStability.u_le_gamma F (by omega : 0 < 1) h1valid)
    have hsum : NumStability.gamma F 1 + g + NumStability.gamma F 1 * g ≤ G := by
      have h := NumStability.gamma_sum_le F 1 s (by simpa [Nat.add_comm] using hvalidF)
      simpa [g, G, Nat.add_comm] using h
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hg]
  have hy : |y| ≤ (1 + g) * S := by
    calc
      |y| = |T + (y - T)| := by ring
      _ ≤ |T| + |y - T| := abs_add_le _ _
      _ ≤ S + g * S := by linarith
      _ = (1 + g) * S := by ring
  have hby : |b - y| ≤ |b| + (1 + g) * S := by
    calc
      |b - y| ≤ |b| + |y| := by simpa using (abs_sub_le b 0 y)
      _ ≤ |b| + (1 + g) * S := by linarith
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub b y
  have herr : p20RoundedResidual fp s a x b - p20ExactResidual s a x b =
      (b - y) * δ + (T - y) := by
    simp only [p20RoundedResidual, p20ExactResidual, y, T]
    rw [hsub]
    ring
  rw [herr]
  have hmain : |(b - y) * δ + (T - y)| ≤
      fp.u * (|b| + (1 + g) * S) + g * S := by
    calc
      |(b - y) * δ + (T - y)| ≤ |(b - y) * δ| + |T - y| := abs_add_le _ _
      _ = |δ| * |b - y| + |y - T| := by
        rw [abs_mul, mul_comm |b - y| |δ|, abs_sub_comm T y]
      _ ≤ fp.u * (|b| + (1 + g) * S) + g * S := by
        have hδstep := mul_le_mul_of_nonneg_right hδ (abs_nonneg (b - y))
        have hbstep := mul_le_mul_of_nonneg_left hby fp.u_nonneg
        nlinarith [hprod]
  have hfinal : fp.u * (|b| + (1 + g) * S) + g * S ≤ G * (|b| + S) := by
    have hbpart := mul_le_mul_of_nonneg_right huG (abs_nonneg b)
    have hspart := mul_le_mul_of_nonneg_right hcoeff hS
    nlinarith
  calc
    |(b - y) * δ + (T - y)| ≤ G * (|b| + S) := le_trans hmain hfinal
    _ = p20ResidualErrorMajorant fp s a x b := by
      simp [p20ResidualErrorMajorant, G, F, p20ToFPModel, S, p20Gamma,
        NumStability.gamma]

end VSCLReuse

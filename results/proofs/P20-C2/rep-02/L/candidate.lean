import VSCLReuse.P20.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

/-- P20-C2: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p20_c2_sparse_residual_error
    (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P20GammaValid fp.u (s + 1)) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      p20ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P20-C2-H001
  let nfp : NumStability.FPModel := {
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
      intro y _
      refine ⟨0, ?_, ?_⟩
      · simpa using fp.u_nonneg
      · ring
  }
  have hn : NumStability.gammaValid nfp (s + 1) := hvalid
  have hs : NumStability.gammaValid nfp s :=
    NumStability.gammaValid_mono nfp (Nat.le_succ s) hn
  have hprod : p20RoundedSparseRowProduct fp s a x =
      NumStability.fl_dotProduct nfp s a x := by
    cases s <;> rfl
  obtain ⟨η, hη, hdot⟩ :=
    NumStability.dotProduct_backward_error nfp s a x hs
  obtain ⟨δ, hδ, hsub⟩ :=
    fp.model_sub b (p20RoundedSparseRowProduct fp s a x)
  have h1 : NumStability.gammaValid nfp 1 :=
    NumStability.gammaValid_mono nfp (by omega : 1 ≤ s + 1) hn
  have hδgamma : |δ| ≤ NumStability.gamma nfp 1 :=
    le_trans hδ (NumStability.u_le_gamma nfp (by omega : 0 < 1) h1)
  have hcombined (j : Fin s) :
      ∃ ε : ℝ, |ε| ≤ NumStability.gamma nfp (s + 1) ∧
        (1 + η j) * (1 + δ) = 1 + ε := by
    simpa [Nat.add_comm] using
      NumStability.gamma_mul nfp s 1 (η j) δ (hη j) hδgamma hn
  let ε : Fin s → ℝ := fun j => Classical.choose (hcombined j)
  have hε (j : Fin s) :
      |ε j| ≤ NumStability.gamma nfp (s + 1) ∧
        (1 + η j) * (1 + δ) = 1 + ε j :=
    Classical.choose_spec (hcombined j)
  have hrounded : p20RoundedResidual fp s a x b =
      b * (1 + δ) - ∑ j : Fin s, a j * x j * (1 + ε j) := by
    unfold p20RoundedResidual
    rw [hsub, hprod, hdot, sub_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, (hε j).2]
  have herr : p20RoundedResidual fp s a x b - p20ExactResidual s a x b =
      b * δ - ∑ j : Fin s, a j * x j * ε j := by
    rw [hrounded]
    unfold p20ExactResidual
    simp_rw [mul_add]
    simp only [mul_one]
    rw [Finset.sum_add_distrib]
    ring
  have hg : 0 ≤ NumStability.gamma nfp (s + 1) :=
    NumStability.gamma_nonneg nfp hn
  have hb : |b * δ| ≤ NumStability.gamma nfp (s + 1) * |b| := by
    rw [abs_mul]
    have hle : |δ| ≤ NumStability.gamma nfp (s + 1) :=
      le_trans hδgamma (NumStability.gamma_mono nfp (by omega : 1 ≤ s + 1) hn)
    nlinarith [mul_le_mul_of_nonneg_left hle (abs_nonneg b)]
  have hterms :
      |∑ j : Fin s, a j * x j * ε j| ≤
        NumStability.gamma nfp (s + 1) * ∑ j : Fin s, |a j| * |x j| := by
    calc
      |∑ j : Fin s, a j * x j * ε j|
          ≤ ∑ j : Fin s, |a j * x j * ε j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin s, (|a j| * |x j|) * |ε j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul]
      _ ≤ ∑ j : Fin s, (|a j| * |x j|) * NumStability.gamma nfp (s + 1) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hε j).1
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = NumStability.gamma nfp (s + 1) * ∑ j : Fin s, |a j| * |x j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [herr]
  calc
    |b * δ - ∑ j : Fin s, a j * x j * ε j|
        ≤ |b * δ| + |∑ j : Fin s, a j * x j * ε j| := by
          simpa [sub_eq_add_neg] using
            abs_add_le (b * δ) (-(∑ j : Fin s, a j * x j * ε j))
    _ ≤ NumStability.gamma nfp (s + 1) * |b| +
        NumStability.gamma nfp (s + 1) * ∑ j : Fin s, |a j| * |x j| :=
          add_le_add hb hterms
    _ = p20ResidualErrorMajorant fp s a x b := by
      unfold p20ResidualErrorMajorant p20Gamma
      dsimp [NumStability.gamma, nfp]
      ring

end VSCLReuse

import VSCLReuse.P40.Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p40AsFPModel (fp : P40FPModel) : NumStability.FPModel where
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
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private theorem p40HighResidual_bound (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fp.u (n + 1)) (i : Fin n) :
    |p40HighResidual fp n A x b i -
      (b i - ∑ j : Fin n, A i j * x j)| ≤
      p40Gamma fp.u (n + 1) *
        (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  let fp' := p40AsFPModel fp
  have hn1 : NumStability.gammaValid fp' (n + 1) := by
    simpa [NumStability.gammaValid, fp', p40AsFPModel, P40GammaValid] using hvalid
  have hn : NumStability.gammaValid fp' n :=
    NumStability.gammaValid_mono fp' (Nat.le_succ n) hn1
  have h := NumStability.conventional_residual_error fp' n A x b hn hn1 i
  simpa [fp', p40AsFPModel, NumStability.fl_residual,
    NumStability.fl_matVec, NumStability.fl_dotProduct,
    p40HighResidual, p40RoundedMatVec, p40RoundedDotProduct,
    NumStability.gamma, p40Gamma] using h

/-- Equation (2.3): the two-precision computed residual bound. -/
theorem p40_c2_two_precision_residual
    (fpHi fpLo : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fpHi.u (n + 1))
    (_hprecision : fpHi.u ≤ fpLo.u) :
    ∀ i : Fin n,
      |p40StoredResidual fpHi fpLo n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      fpLo.u * |b i - ∑ j : Fin n, A i j * x j| +
        (1 + fpLo.u) * p40Gamma fpHi.u (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  -- PROOF_START P40-C2-H001
  intro i
  let R : ℝ := b i - ∑ j : Fin n, A i j * x j
  let H : ℝ := p40HighResidual fpHi n A x b i
  let W : ℝ := |b i| + ∑ j : Fin n, |A i j| * |x j|
  let G : ℝ := p40Gamma fpHi.u (n + 1)
  have hHi : |H - R| ≤ G * W :=
    p40HighResidual_bound fpHi n A x b hvalid i
  obtain ⟨δ, hδ, hfl⟩ := fpLo.model_mul H 1
  have hstored : p40StoredResidual fpHi fpLo n A x b i = H * (1 + δ) := by
    simpa [p40StoredResidual, H] using hfl
  have hLo : |p40StoredResidual fpHi fpLo n A x b i - H| ≤
      fpLo.u * |H| := by
    rw [hstored]
    have heq : H * (1 + δ) - H = H * δ := by ring
    rw [heq, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg H)
  have hH : |H| ≤ |R| + G * W := by
    calc
      |H| = |R + (H - R)| := by congr 1; ring
      _ ≤ |R| + |H - R| := abs_add_le _ _
      _ ≤ |R| + G * W := add_le_add_right hHi _
  have htri : |p40StoredResidual fpHi fpLo n A x b i - R| ≤
      |p40StoredResidual fpHi fpLo n A x b i - H| + |H - R| := by
    have heq : p40StoredResidual fpHi fpLo n A x b i - R =
        (p40StoredResidual fpHi fpLo n A x b i - H) + (H - R) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hmul := mul_le_mul_of_nonneg_left hH fpLo.u_nonneg
  have hresult :
      |p40StoredResidual fpHi fpLo n A x b i - R| ≤
        fpLo.u * |R| + (1 + fpLo.u) * G * W := by
    calc
      |p40StoredResidual fpHi fpLo n A x b i - R|
          ≤ |p40StoredResidual fpHi fpLo n A x b i - H| + |H - R| := htri
      _ ≤ fpLo.u * |H| + G * W := add_le_add hLo hHi
      _ ≤ fpLo.u * (|R| + G * W) + G * W := add_le_add_left hmul _
      _ = fpLo.u * |R| + (1 + fpLo.u) * G * W := by ring
  exact hresult

end VSCLReuse

import VSCLReuse.P40.Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace VSCLReuse

open scoped BigOperators

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
  let hi : NumStability.FPModel := {
    u := fpHi.u
    u_nonneg := fpHi.u_nonneg
    fl_add := fpHi.fl_add
    fl_sub := fpHi.fl_sub
    fl_mul := fpHi.fl_mul
    fl_div := fpHi.fl_div
    fl_sqrt := Real.sqrt
    fl_add_zero := fpHi.fl_add_zero
    model_add := fpHi.model_add
    model_sub := fpHi.model_sub
    model_mul := fpHi.model_mul
    model_div := fpHi.model_div
    model_sqrt := by
      intro x hx
      refine ⟨0, ?_, ?_⟩
      · simpa using fpHi.u_nonneg
      · ring }
  have hv : NumStability.gammaValid hi (n + 1) := hvalid
  have hvn : NumStability.gammaValid hi n :=
    NumStability.gammaValid_mono hi (Nat.le_succ n) hv
  have hHi := NumStability.conventional_residual_error hi n A x b hvn hv
  intro i
  have hHigh :
      |p40HighResidual fpHi n A x b i -
          (b i - ∑ j : Fin n, A i j * x j)| ≤
        p40Gamma fpHi.u (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
    simpa only [hi, p40HighResidual, p40RoundedMatVec,
      p40RoundedDotProduct, NumStability.fl_residual,
      NumStability.fl_matVec, NumStability.fl_dotProduct,
      p40Gamma, NumStability.gamma] using hHi i
  obtain ⟨δ, hδ, hδeq⟩ := fpLo.model_mul (p40HighResidual fpHi n A x b i) 1
  have hStored : p40StoredResidual fpHi fpLo n A x b i =
      p40HighResidual fpHi n A x b i * (1 + δ) := by
    simpa [p40StoredResidual] using hδeq
  have hLo :
      |p40StoredResidual fpHi fpLo n A x b i -
          p40HighResidual fpHi n A x b i| ≤
        fpLo.u * |p40HighResidual fpHi n A x b i| := by
    rw [hStored]
    have heq : p40HighResidual fpHi n A x b i * (1 + δ) -
        p40HighResidual fpHi n A x b i =
        p40HighResidual fpHi n A x b i * δ := by ring
    rw [heq, abs_mul]
    nlinarith [abs_nonneg (p40HighResidual fpHi n A x b i)]
  have hAbs : |p40HighResidual fpHi n A x b i| ≤
      |b i - ∑ j : Fin n, A i j * x j| +
      |p40HighResidual fpHi n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| := by
    have h := abs_add_le
      (p40HighResidual fpHi n A x b i -
        (b i - ∑ j : Fin n, A i j * x j))
      (b i - ∑ j : Fin n, A i j * x j)
    convert h using 1 <;> ring_nf
  have hTri := abs_add_le
    (p40StoredResidual fpHi fpLo n A x b i -
      p40HighResidual fpHi n A x b i)
    (p40HighResidual fpHi n A x b i -
      (b i - ∑ j : Fin n, A i j * x j))
  have hTri' :
      |p40StoredResidual fpHi fpLo n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      |p40StoredResidual fpHi fpLo n A x b i -
        p40HighResidual fpHi n A x b i| +
      |p40HighResidual fpHi n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| := by
    convert hTri using 1; ring_nf
  nlinarith [mul_le_mul_of_nonneg_left hAbs fpLo.u_nonneg,
    mul_le_mul_of_nonneg_left hHigh fpLo.u_nonneg]

end VSCLReuse

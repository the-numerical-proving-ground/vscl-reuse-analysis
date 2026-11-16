import VSCLReuse.P40.Definitions
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p40ToFPModel (fp : P40FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

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
  let exact : ℝ := b i - ∑ j : Fin n, A i j * x j
  let s : ℝ := p40HighResidual fpHi n A x b i
  let r : ℝ := p40StoredResidual fpHi fpLo n A x b i
  let γ : ℝ := p40Gamma fpHi.u (n + 1)
  let M : ℝ := |b i| + ∑ j : Fin n, |A i j| * |x j|
  have hhi : |s - exact| ≤ γ * M := by
    let fp := p40ToFPModel fpHi
    have hn1 : NumStability.gammaValid fp (n + 1) := hvalid
    have hn : NumStability.gammaValid fp n :=
      NumStability.gammaValid_mono fp (Nat.le_succ n) hn1
    have h := NumStability.conventional_residual_error fp n A x b hn hn1 i
    simpa [s, exact, γ, M, fp, p40ToFPModel,
      p40HighResidual, p40RoundedMatVec,
      NumStability.fl_residual, NumStability.fl_matVec,
      p40RoundedDotProduct, NumStability.fl_dotProduct,
      p40Gamma, NumStability.gamma] using h
  obtain ⟨δ, hδ, hmul⟩ := fpLo.model_mul s 1
  have hr : r = s * (1 + δ) := by
    simpa [r, s, p40StoredResidual] using hmul
  have hlow : |r - s| ≤ fpLo.u * |s| := by
    rw [hr]
    have heq : s * (1 + δ) - s = s * δ := by ring
    rw [heq, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg s)
  have hs : |s| ≤ |exact| + |s - exact| := by
    have heq : s = (s - exact) + exact := by ring
    rw [heq]
    simpa [add_comm] using abs_add_le (s - exact) exact
  have htri : |r - exact| ≤ |r - s| + |s - exact| := by
    have heq : r - exact = (r - s) + (s - exact) := by ring
    rw [heq]
    exact abs_add_le _ _
  calc
    |r - exact| ≤ |r - s| + |s - exact| := htri
    _ ≤ fpLo.u * |s| + |s - exact| := add_le_add hlow le_rfl
    _ ≤ fpLo.u * (|exact| + |s - exact|) + |s - exact| := by
      exact add_le_add (mul_le_mul_of_nonneg_left hs fpLo.u_nonneg) le_rfl
    _ ≤ fpLo.u * |exact| + (1 + fpLo.u) * (γ * M) := by
      have hnonneg : 0 ≤ 1 + fpLo.u := by linarith [fpLo.u_nonneg]
      nlinarith [mul_le_mul_of_nonneg_left hhi hnonneg]
    _ = fpLo.u * |exact| + (1 + fpLo.u) * γ * M := by ring

end VSCLReuse

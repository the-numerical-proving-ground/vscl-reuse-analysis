import VSCLReuse.P48.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p48HighModel (fp : P48FPModel) : NumStability.FPModel :=
  { NumStability.FPModel.exactWithUnitRoundoff fp.uHigh fp.uHigh_nonneg with
    fl_add := fp.flHighAdd
    fl_add_zero := fp.flHighAdd_zero
    model_add := fp.modelHighAdd }

theorem p48_c2_mixed_dot_backward_bound
    (fp : P48FPModel) (n : ℕ) (x y : Fin (n + 1) → ℝ)
    (hvalid : P48GammaValid fp.uHigh n) :
    let c := (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1
    ∃ dx dy : Fin (n + 1) → ℝ,
      (∀ i, |dx i| ≤ c * |x i|) ∧
      (∀ i, |dy i| ≤ c * |y i|) ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), (x i + dx i) * y i ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), x i * (y i + dy i) := by
  -- PROOF_START P48-C2-H001
  let highFp := p48HighModel fp
  have hvalid' : NumStability.gammaValid highFp ((n + 1) - 1) := by
    simpa [NumStability.gammaValid, highFp, p48HighModel, P48GammaValid] using hvalid
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.recursiveSum_backward_error highFp (n + 1)
      (fun i => x i * y i) hvalid'
  have hθ' : ∀ i, |θ i| ≤ p48Gamma fp.uHigh n := by
    simpa [NumStability.gamma, p48Gamma, highFp, p48HighModel] using hθ
  have hsum' : p48HighDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) := by
    simpa [NumStability.fl_recursiveSum, p48HighDot, highFp, p48HighModel] using hsum
  obtain ⟨δ, hδ, hcast⟩ := fp.castDown_model (p48HighDot fp (n + 1) x y)
  have hgamma : 0 ≤ p48Gamma fp.uHigh n := by
    simpa [NumStability.gamma, p48Gamma, highFp, p48HighModel] using
      (NumStability.gamma_nonneg highFp hvalid')
  let e : Fin (n + 1) → ℝ := fun i => (1 + θ i) * (1 + δ) - 1
  have he : ∀ i, |e i| ≤ (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1 := by
    intro i
    have hp : |θ i| * |δ| ≤ p48Gamma fp.uHigh n * fp.uLow :=
      mul_le_mul (hθ' i) hδ (abs_nonneg δ) hgamma
    have ha : |e i| ≤ |θ i| + |δ| + |θ i| * |δ| := by
      have heq : e i = (θ i + δ) + θ i * δ := by dsimp [e]; ring
      rw [heq]
      calc
        |θ i + δ + θ i * δ| ≤ |θ i + δ| + |θ i * δ| := abs_add_le _ _
        _ ≤ |θ i| + |δ| + |θ i| * |δ| := by
          rw [abs_mul]
          linarith [abs_add_le (θ i) δ]
    nlinarith [hθ' i, hδ, hp]
  have hmixed : p48MixedDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) * (1 + δ) := by
    calc
      p48MixedDot fp (n + 1) x y =
          (∑ i : Fin (n + 1), (x i * y i) * (1 + θ i)) * (1 + δ) := by
            rw [p48MixedDot, hcast, hsum']
      _ = ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) * (1 + δ) := by
            rw [Finset.sum_mul]
  refine ⟨(fun i => x i * e i), (fun i => y i * e i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [abs_mul]
    calc
      |x i| * |e i| ≤ |x i| * ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) :=
        mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) * |x i| := by ring
  · intro i
    rw [abs_mul]
    calc
      |y i| * |e i| ≤ |y i| * ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) :=
        mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) * |y i| := by ring
  · rw [hmixed]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [e]
    ring
  · rw [hmixed]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [e]
    ring

end VSCLReuse

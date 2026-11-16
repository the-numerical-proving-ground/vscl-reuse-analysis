import VSCLReuse.P48.Definitions
import NumStability.Analysis.Summation.ErrorBounds

namespace VSCLReuse

open scoped BigOperators

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
  let hp : NumStability.FPModel :=
    { NumStability.FPModel.exactWithUnitRoundoff fp.uHigh fp.uHigh_nonneg with
      fl_add := fp.flHighAdd
      fl_add_zero := fp.flHighAdd_zero
      model_add := fp.modelHighAdd }
  have hgamma : NumStability.gamma hp n = p48Gamma fp.uHigh n := by
    rfl
  have hvalid' : NumStability.gammaValid hp n := by
    exact hvalid
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.fl_sum_error_tight hp (n + 1) (by omega)
      (fun i => x i * y i) (by simpa using hvalid')
  have hsum' : p48HighDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) := by
    exact hsum
  obtain ⟨δ, hδ, hcast⟩ := fp.castDown_model (p48HighDot fp (n + 1) x y)
  let η : Fin (n + 1) → ℝ := fun i => (1 + θ i) * (1 + δ) - 1
  have hγnonneg : 0 ≤ p48Gamma fp.uHigh n := by
    rw [← hgamma]
    exact NumStability.gamma_nonneg hp hvalid'
  have hη : ∀ i, |η i| ≤ (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1 := by
    intro i
    have hθi : |θ i| ≤ p48Gamma fp.uHigh n := by
      rw [← hgamma]
      simpa using hθ i
    have hmul : |θ i| * |δ| ≤ p48Gamma fp.uHigh n * fp.uLow :=
      mul_le_mul hθi hδ (abs_nonneg _) hγnonneg
    have htri : |θ i + δ + θ i * δ| ≤ |θ i| + |δ| + |θ i * δ| := by
      calc
        |θ i + δ + θ i * δ| ≤ |θ i + δ| + |θ i * δ| := abs_add_le _ _
        _ ≤ (|θ i| + |δ|) + |θ i * δ| := by gcongr; exact abs_add_le _ _
    change |(1 + θ i) * (1 + δ) - 1| ≤ _
    have hr : (1 + θ i) * (1 + δ) - 1 = θ i + δ + θ i * δ := by ring
    rw [hr]
    calc
      |θ i + δ + θ i * δ| ≤ |θ i| + |δ| + |θ i * δ| := htri
      _ = |θ i| + |δ| + |θ i| * |δ| := by rw [abs_mul]
      _ ≤ p48Gamma fp.uHigh n + fp.uLow + p48Gamma fp.uHigh n * fp.uLow := by
        gcongr
      _ = (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1 := by ring
  have hrepr : p48MixedDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + η i) := by
    change fp.castDown (p48HighDot fp (n + 1) x y) = _
    rw [hcast, hsum', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [η]
    ring
  refine ⟨(fun i => x i * η i), (fun i => y i * η i), ?_, ?_, ?_, ?_⟩
  · intro i
    change |x i * η i| ≤ ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) * |x i|
    rw [abs_mul]
    calc
      |x i| * |η i| ≤ |x i| * ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) :=
        mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
      _ = _ := by ring
  · intro i
    change |y i * η i| ≤ ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) * |y i|
    rw [abs_mul]
    calc
      |y i| * |η i| ≤ |y i| * ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) :=
        mul_le_mul_of_nonneg_left (hη i) (abs_nonneg _)
      _ = _ := by ring
  · rw [hrepr]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [hrepr]
    apply Finset.sum_congr rfl
    intro i _
    ring

end VSCLReuse

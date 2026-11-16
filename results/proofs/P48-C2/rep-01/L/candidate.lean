import VSCLReuse.P48.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p48HighFPModel (fp : P48FPModel) : NumStability.FPModel where
  u := fp.uHigh
  u_nonneg := fp.uHigh_nonneg
  fl_add := fp.flHighAdd
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.flHighAdd_zero
  model_add := fp.modelHighAdd
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.uHigh_nonneg, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by simpa using fp.uHigh_nonneg, by ring⟩
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.uHigh_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.uHigh_nonneg, by ring⟩

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
  let high := p48HighFPModel fp
  have hvalid' : NumStability.gammaValid high n := hvalid
  obtain ⟨θ, hθ, hsum⟩ := NumStability.recursiveSum_backward_error
    high (n + 1) (fun i => x i * y i) (by simpa using hvalid')
  have hθ' : ∀ i, |θ i| ≤ p48Gamma fp.uHigh n := by
    intro i
    simpa [NumStability.gamma, p48Gamma, high, p48HighFPModel] using hθ i
  have hhigh : p48HighDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * (1 + θ i) := by
    simpa [p48HighDot, NumStability.fl_recursiveSum, high, p48HighFPModel]
      using hsum
  obtain ⟨δ, hδ, hcast⟩ := fp.castDown_model (p48HighDot fp (n + 1) x y)
  let g := p48Gamma fp.uHigh n
  let c := (1 + fp.uLow) * (1 + g) - 1
  let e : Fin (n + 1) → ℝ := fun i => (1 + θ i) * (1 + δ) - 1
  have hg : 0 ≤ g := by
    have hn : (0 : ℝ) ≤ (n : ℝ) * fp.uHigh :=
      mul_nonneg (Nat.cast_nonneg _) fp.uHigh_nonneg
    exact div_nonneg hn (le_of_lt (sub_pos.mpr hvalid))
  have he : ∀ i, |e i| ≤ c := by
    intro i
    have hprod : |θ i * δ| ≤ g * fp.uLow := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hθ' i) (abs_nonneg δ)).trans
        (mul_le_mul_of_nonneg_left hδ hg)
    calc
      |e i| = |θ i + δ + θ i * δ| := by
        congr 1
        dsimp [e]
        ring
      _ ≤ |θ i| + |δ| + |θ i * δ| := by
        exact (abs_add_le (θ i + δ) (θ i * δ)).trans
          (add_le_add (abs_add_le (θ i) δ) le_rfl)
      _ ≤ g + fp.uLow + g * fp.uLow := by
        exact add_le_add (add_le_add (hθ' i) hδ) hprod
      _ = c := by dsimp [c, g]; ring
  have hmain : p48MixedDot fp (n + 1) x y =
      ∑ i : Fin (n + 1), (x i * y i) * ((1 + θ i) * (1 + δ)) := by
    calc
      p48MixedDot fp (n + 1) x y =
          (∑ i : Fin (n + 1), (x i * y i) * (1 + θ i)) * (1 + δ) := by
            rw [p48MixedDot, hcast, hhigh]
      _ = ∑ i : Fin (n + 1), (x i * y i) * ((1 + θ i) * (1 + δ)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  refine ⟨(fun i => x i * e i), (fun i => y i * e i), ?_, ?_, ?_, ?_⟩
  · intro i
    calc
      |x i * e i| = |x i| * |e i| := abs_mul _ _
      _ ≤ |x i| * c := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = c * |x i| := mul_comm _ _
  · intro i
    calc
      |y i * e i| = |y i| * |e i| := abs_mul _ _
      _ ≤ |y i| * c := mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
      _ = c * |y i| := mul_comm _ _
  · rw [hmain]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [e]
    ring
  · rw [hmain]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [e]
    ring

end VSCLReuse

import VSCLReuse.P13.Definitions

namespace VSCLReuse

open scoped BigOperators Topology
open Filter

/-- P13-C1: the cycle-reindexed linear majorant constructed in Lemma 21. -/
theorem p13_c1_lemma21_linear_convergence
    (data : P13Lemma21Data) :
    (∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k))) ∧
      (∀ n,
        data.relativeEven n ≤
            p13LinearMajorant data.toP13WidthSequence n ∧
          data.relativeOdd n ≤
            p13LinearMajorant data.toP13WidthSequence n) ∧
      (∀ n, 0 ≤ p13LinearMajorant data.toP13WidthSequence n) ∧
      (∀ n, p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n) ∧
      Tendsto (p13LinearMajorant data.toP13WidthSequence) atTop (nhds 0) := by
  -- PROOF_START P13-C1-H001
  have hsum (n : ℕ) : Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
    filter_upwards [] with k
    have h0 : 0 ≤ 2 * data.width (n + 1 + k) :=
      mul_nonneg (by norm_num) (data.width_nonneg _)
    have h1 : 0 ≤ 2 * data.width (n + 1 + (k + 1)) :=
      mul_nonneg (by norm_num) (data.width_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg h0]
    have h := data.width_half (n + 1 + k)
    have heq : n + 1 + (k + 1) = (n + 1 + k) + 1 := by omega
    rw [heq]
    nlinarith
  have htail_nonneg (n : ℕ) : 0 ≤ p13WidthTail data.toP13WidthSequence n := by
    change 0 ≤ ∑' k : ℕ, 2 * data.width (n + 1 + k)
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
  have htail_half (n : ℕ) :
      p13WidthTail data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13WidthTail data.toP13WidthSequence n := by
    change (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
      (1 / 2 : ℝ) * (∑' k : ℕ, 2 * data.width (n + 1 + k))
    calc
      (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
          ∑' k : ℕ, (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by
            apply Summable.tsum_le_tsum
            · intro k
              have h := data.width_half (n + 1 + k)
              have heq : (n + 1) + 1 + k = (n + 1 + k) + 1 := by omega
              rw [heq]
              nlinarith
            · exact hsum (n + 1)
            · exact (hsum n).mul_left (1 / 2 : ℝ)
      _ = (1 / 2 : ℝ) * (∑' k : ℕ, 2 * data.width (n + 1 + k)) := by
        rw [tsum_mul_left]
  have hmajor_nonneg (n : ℕ) :
      0 ≤ p13LinearMajorant data.toP13WidthSequence n := by
    have h := Real.exp_le_exp.mpr (htail_nonneg n)
    rw [Real.exp_zero] at h
    dsimp [p13LinearMajorant]
    linarith
  have hmajor_half (n : ℕ) :
      p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n := by
    let x := p13WidthTail data.toP13WidthSequence n
    have hExp :
        Real.exp (p13WidthTail data.toP13WidthSequence (n + 1)) ≤
          Real.exp (x / 2) := by
      apply Real.exp_le_exp.mpr
      dsimp [x]
      convert htail_half n using 1; ring
    have hSq : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hQuad : 2 * (Real.exp (x / 2) - 1) ≤ Real.exp x - 1 := by
      rw [← hSq]
      nlinarith [sq_nonneg (Real.exp (x / 2) - 1)]
    dsimp [p13LinearMajorant]
    change Real.exp (p13WidthTail data.toP13WidthSequence (n + 1)) - 1 ≤
      (1 / 2 : ℝ) * (Real.exp x - 1)
    linarith
  have htail_tendsto :
      Tendsto (fun n => p13WidthTail data.toP13WidthSequence n) atTop (nhds 0) := by
    change Tendsto (fun n => ∑' k : ℕ, 2 * data.width (n + 1 + k)) atTop (nhds 0)
    convert (tendsto_sum_nat_add (f := fun m : ℕ => 2 * data.width (m + 1))) using 1
    funext n
    apply tsum_congr
    intro k
    congr 1
    congr 1
    omega
  have hmajor_tendsto :
      Tendsto (p13LinearMajorant data.toP13WidthSequence) atTop (nhds 0) := by
    have h := (Real.continuous_exp.tendsto 0).comp htail_tendsto
    have h' := h.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
    simpa only [p13LinearMajorant, Real.exp_zero, sub_self] using h'
  refine ⟨hsum, ?_, hmajor_nonneg, hmajor_half, hmajor_tendsto⟩
  intro n
  constructor
  · exact data.relative_even_tail n
  · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)

end VSCLReuse

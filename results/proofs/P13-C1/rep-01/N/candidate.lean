import VSCLReuse.P13.Definitions

namespace VSCLReuse

open scoped BigOperators Topology
open Filter

private theorem p13_width_geometric_bound (run : P13WidthSequence) (n k : ℕ) :
    run.width (n + k) ≤ run.width n * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        run.width (n + (k + 1)) = run.width ((n + k) + 1) := by congr 1
        _ ≤ (1 / 2 : ℝ) * run.width (n + k) := run.width_half _
        _ ≤ (1 / 2 : ℝ) * (run.width n * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = run.width n * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

private theorem p13_width_tail_summable (run : P13WidthSequence) (n : ℕ) :
    Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))
    (fun k => ?_)
    (summable_geometric_two.mul_left (2 * run.width (n + 1)))
  calc
    2 * run.width (n + 1 + k) ≤
        2 * (run.width (n + 1) * (1 / 2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (p13_width_geometric_bound run (n + 1) k)
        (by norm_num)
    _ = (2 * run.width (n + 1)) * (1 / 2 : ℝ) ^ k := by ring

private theorem p13_width_tail_half (run : P13WidthSequence) (n : ℕ) :
    p13WidthTail run (n + 1) ≤ (1 / 2 : ℝ) * p13WidthTail run n := by
  unfold p13WidthTail
  rw [← tsum_mul_left]
  apply (p13_width_tail_summable run (n + 1)).tsum_le_tsum
    (fun k => ?_) ((p13_width_tail_summable run n).mul_left (1 / 2 : ℝ))
  have h := run.width_half (n + 1 + k)
  have heq : n + 1 + 1 + k = (n + 1 + k) + 1 := by omega
  rw [heq]
  nlinarith

private theorem p13_majorant_half (run : P13WidthSequence) (n : ℕ) :
    p13LinearMajorant run (n + 1) ≤
      (1 / 2 : ℝ) * p13LinearMajorant run n := by
  have ht := p13_width_tail_half run n
  have hnonneg : 0 ≤ p13WidthTail run n := by
    unfold p13WidthTail
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))
  have he : Real.exp (p13WidthTail run (n + 1)) ≤
      Real.exp ((1 / 2 : ℝ) * p13WidthTail run n) :=
    Real.exp_le_exp.mpr ht
  have hy : 1 ≤ Real.exp ((1 / 2 : ℝ) * p13WidthTail run n) := by
    apply Real.one_le_exp_iff.mpr
    positivity
  have hsq : Real.exp (p13WidthTail run n) =
      (Real.exp ((1 / 2 : ℝ) * p13WidthTail run n)) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  unfold p13LinearMajorant
  rw [hsq]
  nlinarith [sq_nonneg (Real.exp ((1 / 2 : ℝ) * p13WidthTail run n) - 1)]

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
  have hsummable : ∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    intro n
    exact p13_width_tail_summable data.toP13WidthSequence n
  have hrelative : ∀ n,
      data.relativeEven n ≤ p13LinearMajorant data.toP13WidthSequence n ∧
      data.relativeOdd n ≤ p13LinearMajorant data.toP13WidthSequence n := by
    intro n
    constructor
    · exact data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)
  have hnonneg : ∀ n, 0 ≤ p13LinearMajorant data.toP13WidthSequence n := by
    intro n
    unfold p13LinearMajorant p13WidthTail
    have ht : 0 ≤ ∑' k : ℕ, 2 * data.width (n + 1 + k) :=
      tsum_nonneg (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  have hhalf : ∀ n, p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
      (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n :=
    p13_majorant_half data.toP13WidthSequence
  have hbound : ∀ n,
      p13LinearMajorant data.toP13WidthSequence n ≤
        p13LinearMajorant data.toP13WidthSequence 0 * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
              (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n := hhalf n
          _ ≤ (1 / 2 : ℝ) *
              (p13LinearMajorant data.toP13WidthSequence 0 * (1 / 2 : ℝ) ^ n) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = p13LinearMajorant data.toP13WidthSequence 0 * (1 / 2 : ℝ) ^ (n + 1) := by
              rw [pow_succ]
              ring
  have hgeo : Tendsto
      (fun n : ℕ => p13LinearMajorant data.toP13WidthSequence 0 * (1 / 2 : ℝ) ^ n)
      atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (p13LinearMajorant data.toP13WidthSequence 0)
  exact ⟨hsummable, hrelative, hnonneg, hhalf,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo hnonneg hbound⟩

end VSCLReuse

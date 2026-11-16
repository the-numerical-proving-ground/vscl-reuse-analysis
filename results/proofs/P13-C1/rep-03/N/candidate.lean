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
  let run : P13WidthSequence := data.toP13WidthSequence
  have hwidth_pow (m k : ℕ) :
      data.width (m + k) ≤ (1 / 2 : ℝ) ^ k * data.width m := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          data.width (m + (k + 1)) = data.width ((m + k) + 1) := by
            simp [Nat.add_assoc]
          _ ≤ (1 / 2 : ℝ) * data.width (m + k) := data.width_half _
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * data.width m) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * data.width m := by
            rw [pow_succ]
            ring
  have hsum (n : ℕ) : Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
      (fun k => ?_)
      (summable_geometric_two.mul_right (2 * data.width (n + 1)))
    calc
      2 * data.width (n + 1 + k) ≤
          2 * ((1 / 2 : ℝ) ^ k * data.width (n + 1)) :=
        mul_le_mul_of_nonneg_left (hwidth_pow (n + 1) k) (by norm_num)
      _ = (1 / 2 : ℝ) ^ k * (2 * data.width (n + 1)) := by ring
  have htail_nonneg (n : ℕ) : 0 ≤ p13WidthTail run n := by
    unfold p13WidthTail
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
  have htail_half (n : ℕ) :
      p13WidthTail run (n + 1) ≤ (1 / 2 : ℝ) * p13WidthTail run n := by
    change (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
      (1 / 2 : ℝ) * (∑' k : ℕ, 2 * data.width (n + 1 + k))
    calc
      (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
          ∑' k : ℕ, (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by
        apply Summable.tsum_le_tsum
        · intro k
          calc
            2 * data.width ((n + 1) + 1 + k) =
                2 * data.width ((n + 1 + k) + 1) := by
              simp [Nat.add_left_comm, Nat.add_comm]
            _ ≤ 2 * ((1 / 2 : ℝ) * data.width (n + 1 + k)) :=
              mul_le_mul_of_nonneg_left (data.width_half _) (by norm_num)
            _ = (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by ring
        · exact hsum (n + 1)
        · exact (hsum n).mul_left _
      _ = (1 / 2 : ℝ) * (∑' k : ℕ, 2 * data.width (n + 1 + k)) := by
        rw [tsum_mul_left]
  have hmajorant_nonneg (n : ℕ) : 0 ≤ p13LinearMajorant run n := by
    unfold p13LinearMajorant
    linarith [Real.one_le_exp (htail_nonneg n)]
  have hmajorant_half (n : ℕ) :
      p13LinearMajorant run (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant run n := by
    have htwice : 2 * p13WidthTail run (n + 1) ≤ p13WidthTail run n := by
      linarith [htail_half n]
    have hsq : (Real.exp (p13WidthTail run (n + 1))) ^ 2 ≤
        Real.exp (p13WidthTail run n) := by
      calc
        (Real.exp (p13WidthTail run (n + 1))) ^ 2 =
            Real.exp (2 * p13WidthTail run (n + 1)) := by
          simpa using (Real.exp_nat_mul (p13WidthTail run (n + 1)) 2).symm
        _ ≤ Real.exp (p13WidthTail run n) := Real.exp_le_exp.mpr htwice
    unfold p13LinearMajorant
    nlinarith [sq_nonneg (Real.exp (p13WidthTail run (n + 1)) - 1)]
  have hmajorant_geo (n : ℕ) :
      p13LinearMajorant run n ≤
        (1 / 2 : ℝ) ^ n * p13LinearMajorant run 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p13LinearMajorant run (n + 1) ≤
              (1 / 2 : ℝ) * p13LinearMajorant run n := hmajorant_half n
          _ ≤ (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ n * p13LinearMajorant run 0) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) * p13LinearMajorant run 0 := by
            rw [pow_succ]
            ring
  have hgeo_lim : Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) ^ n * p13LinearMajorant run 0)
      atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (p13LinearMajorant run 0)
  refine ⟨hsum, ?_, hmajorant_nonneg, hmajorant_half, ?_⟩
  · intro n
    constructor
    · exact data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)
  · exact squeeze_zero hmajorant_nonneg hmajorant_geo hgeo_lim

end VSCLReuse

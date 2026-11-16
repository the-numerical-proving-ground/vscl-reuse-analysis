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
  have hwidth_bound : ∀ k : ℕ,
      data.width k ≤ data.width 0 * (1 / 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          data.width (k + 1) ≤ (1 / 2 : ℝ) * data.width k := data.width_half k
          _ ≤ (1 / 2 : ℝ) * (data.width 0 * (1 / 2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = data.width 0 * (1 / 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have hfull : Summable (fun k : ℕ => 2 * data.width k) := by
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by norm_num) (data.width_nonneg k))
      (fun k => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (2 * data.width 0))
    calc
      2 * data.width k ≤ 2 * (data.width 0 * (1 / 2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (hwidth_bound k) (by norm_num)
      _ = (2 * data.width 0) * (1 / 2 : ℝ) ^ k := by ring
  have hs : ∀ n : ℕ, Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    intro n
    simpa only [add_comm, add_left_comm, add_assoc] using
      ((summable_nat_add_iff (n + 1)).2 hfull)
  have htail_nonneg : ∀ n : ℕ, 0 ≤ p13WidthTail data.toP13WidthSequence n := by
    intro n
    unfold p13WidthTail
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
  have htail_half : ∀ n : ℕ,
      p13WidthTail data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13WidthTail data.toP13WidthSequence n := by
    intro n
    unfold p13WidthTail
    have hle :
        (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
          ∑' k : ℕ, (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by
      apply (hs (n + 1)).tsum_le_tsum
      · intro k
        have h := data.width_half (n + 1 + k)
        have heq : (n + 1) + 1 + k = (n + 1 + k) + 1 := by omega
        rw [heq]
        calc
          2 * data.width ((n + 1 + k) + 1) ≤
              2 * ((1 / 2 : ℝ) * data.width (n + 1 + k)) :=
                mul_le_mul_of_nonneg_left h (by norm_num)
          _ = (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by ring
      · exact (hs n).mul_left (1 / 2 : ℝ)
    simpa only [tsum_mul_left] using hle
  have hmajorant_nonneg : ∀ n : ℕ,
      0 ≤ p13LinearMajorant data.toP13WidthSequence n := by
    intro n
    unfold p13LinearMajorant
    have h := Real.add_one_le_exp (p13WidthTail data.toP13WidthSequence n)
    linarith [htail_nonneg n]
  have hmajorant_half : ∀ n : ℕ,
      p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n := by
    intro n
    have harg :
        p13WidthTail data.toP13WidthSequence (n + 1) +
          p13WidthTail data.toP13WidthSequence (n + 1) ≤
            p13WidthTail data.toP13WidthSequence n := by
      linarith [htail_half n]
    have hexp :
        (Real.exp (p13WidthTail data.toP13WidthSequence (n + 1))) ^ 2 ≤
          Real.exp (p13WidthTail data.toP13WidthSequence n) := by
      calc
        (Real.exp (p13WidthTail data.toP13WidthSequence (n + 1))) ^ 2 =
            Real.exp (p13WidthTail data.toP13WidthSequence (n + 1) +
              p13WidthTail data.toP13WidthSequence (n + 1)) := by
                rw [Real.exp_add]; ring
        _ ≤ _ := Real.exp_le_exp.mpr harg
    have hone : 1 ≤ Real.exp (p13WidthTail data.toP13WidthSequence (n + 1)) := by
      linarith [Real.add_one_le_exp
        (p13WidthTail data.toP13WidthSequence (n + 1)), htail_nonneg (n + 1)]
    unfold p13LinearMajorant
    nlinarith [sq_nonneg
      (Real.exp (p13WidthTail data.toP13WidthSequence (n + 1)) - 1)]
  have hbound : ∀ n : ℕ,
      p13LinearMajorant data.toP13WidthSequence n ≤
        (1 / 2 : ℝ) ^ n * p13LinearMajorant data.toP13WidthSequence 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
              (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n :=
                hmajorant_half n
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n *
              p13LinearMajorant data.toP13WidthSequence 0) :=
                mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) *
              p13LinearMajorant data.toP13WidthSequence 0 := by rw [pow_succ]; ring
  have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n *
      p13LinearMajorant data.toP13WidthSequence 0) atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          (p13LinearMajorant data.toP13WidthSequence 0))
  refine ⟨hs, ?_, hmajorant_nonneg, hmajorant_half, ?_⟩
  · intro n
    constructor
    · exact data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)
  · exact squeeze_zero hmajorant_nonneg hbound hgeom

end VSCLReuse

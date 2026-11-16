import VSCLReuse.P13.Definitions

namespace VSCLReuse

open scoped BigOperators Topology
open Filter

private lemma p13_width_le_geometric (run : P13WidthSequence) (n : ℕ) :
    run.width n ≤ (1 / 2 : ℝ) ^ n * run.width 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        run.width (n + 1) ≤ (1 / 2 : ℝ) * run.width n := run.width_half n
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n * run.width 0) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) * run.width 0 := by
          rw [pow_succ]
          ring

private lemma p13_width_summable (run : P13WidthSequence) :
    Summable run.width := by
  have h : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n * run.width 0) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
  exact h.of_nonneg_of_le run.width_nonneg (p13_width_le_geometric run)

private lemma p13_tail_summable (run : P13WidthSequence) (n : ℕ) :
    Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
  have h : Summable (fun k : ℕ => 2 * run.width (k + (n + 1))) :=
    (summable_nat_add_iff (f := fun k : ℕ => 2 * run.width k) (n + 1)).2
      ((p13_width_summable run).mul_left 2)
  simpa only [add_comm] using h

private lemma p13_tail_nonneg (run : P13WidthSequence) (n : ℕ) :
    0 ≤ p13WidthTail run n := by
  unfold p13WidthTail
  exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))

private lemma p13_tail_half (run : P13WidthSequence) (n : ℕ) :
    p13WidthTail run (n + 1) ≤ (1 / 2 : ℝ) * p13WidthTail run n := by
  unfold p13WidthTail
  calc
    (∑' k : ℕ, 2 * run.width (n + 1 + 1 + k)) ≤
        ∑' k : ℕ, (1 / 2 : ℝ) * (2 * run.width (n + 1 + k)) := by
      apply Summable.tsum_le_tsum
      · intro k
        have h := run.width_half (n + 1 + k)
        have heq : n + 1 + 1 + k = (n + 1 + k) + 1 := by omega
        rw [heq]
        nlinarith
      · simpa only [Nat.add_assoc] using p13_tail_summable run (n + 1)
      · exact (p13_tail_summable run n).mul_left (1 / 2)
    _ = (1 / 2 : ℝ) * ∑' k : ℕ, 2 * run.width (n + 1 + k) :=
      tsum_mul_left

private lemma p13_majorant_nonneg (run : P13WidthSequence) (n : ℕ) :
    0 ≤ p13LinearMajorant run n := by
  unfold p13LinearMajorant
  have h := Real.one_le_exp (p13_tail_nonneg run n)
  linarith

private lemma p13_majorant_half (run : P13WidthSequence) (n : ℕ) :
    p13LinearMajorant run (n + 1) ≤
      (1 / 2 : ℝ) * p13LinearMajorant run n := by
  have ht := p13_tail_half run n
  have he : Real.exp (2 * p13WidthTail run (n + 1)) ≤
      Real.exp (p13WidthTail run n) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [show 2 * p13WidthTail run (n + 1) =
    p13WidthTail run (n + 1) + p13WidthTail run (n + 1) by ring,
    Real.exp_add] at he
  have hs : 0 ≤ (Real.exp (p13WidthTail run (n + 1)) - 1) ^ 2 :=
    sq_nonneg _
  unfold p13LinearMajorant
  nlinarith

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
  have hsum := p13_tail_summable data.toP13WidthSequence
  have hnonneg := p13_majorant_nonneg data.toP13WidthSequence
  have hhalf := p13_majorant_half data.toP13WidthSequence
  refine ⟨hsum, ?_, hnonneg, hhalf, ?_⟩
  · intro n
    constructor
    · simpa only [p13LinearMajorant, p13WidthTail] using data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans
        (by simpa only [p13LinearMajorant, p13WidthTail] using data.relative_even_tail n)
  · have hbound : ∀ n : ℕ,
        p13LinearMajorant data.toP13WidthSequence n ≤
          (1 / 2 : ℝ) ^ n * p13LinearMajorant data.toP13WidthSequence 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc
            p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
                (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n :=
              hhalf n
            _ ≤ (1 / 2 : ℝ) *
                ((1 / 2 : ℝ) ^ n * p13LinearMajorant data.toP13WidthSequence 0) :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
            _ = (1 / 2 : ℝ) ^ (n + 1) *
                p13LinearMajorant data.toP13WidthSequence 0 := by
              rw [pow_succ]
              ring
    have hgeom : Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) ^ n *
          p13LinearMajorant data.toP13WidthSequence 0) atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          (p13LinearMajorant data.toP13WidthSequence 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hgeom hnonneg hbound

end VSCLReuse

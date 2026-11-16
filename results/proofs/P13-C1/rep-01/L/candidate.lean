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
  have hbound (m k : ℕ) :
      run.width (m + k) ≤ (1 / 2 : ℝ) ^ k * run.width m := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        run.width (m + (k + 1)) = run.width ((m + k) + 1) := by congr 1
        _ ≤ (1 / 2 : ℝ) * run.width (m + k) := run.width_half _
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * run.width m) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) * run.width m := by rw [pow_succ]; ring
  have hsum (n : ℕ) :
      Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
    have hgeom : Summable (fun k : ℕ =>
        ((1 / 2 : ℝ) ^ k) * (2 * run.width (n + 1))) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))
      (fun k => ?_) hgeom
    have h := hbound (n + 1) k
    nlinarith
  have htail_nonneg (n : ℕ) : 0 ≤ p13WidthTail run n := by
    unfold p13WidthTail
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))
  have htail_half (n : ℕ) :
      p13WidthTail run (n + 1) ≤ (1 / 2 : ℝ) * p13WidthTail run n := by
    have hterm (k : ℕ) :
        2 * run.width (n + 1 + 1 + k) ≤
          (1 / 2 : ℝ) * (2 * run.width (n + 1 + k)) := by
      have hw : run.width (n + 1 + 1 + k) ≤
          (1 / 2 : ℝ) * run.width (n + 1 + k) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          run.width_half (n + 1 + k)
      nlinarith
    have h := Summable.tsum_le_tsum hterm (hsum (n + 1)) ((hsum n).mul_left (1 / 2 : ℝ))
    simpa only [p13WidthTail, tsum_mul_left] using h
  have hmajor_nonneg (n : ℕ) : 0 ≤ p13LinearMajorant run n := by
    unfold p13LinearMajorant
    have h := Real.add_one_le_exp (p13WidthTail run n)
    linarith [htail_nonneg n]
  have hmajor_half (n : ℕ) :
      p13LinearMajorant run (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant run n := by
    have he : Real.exp (2 * p13WidthTail run (n + 1)) ≤
        Real.exp (p13WidthTail run n) :=
      Real.exp_le_exp.mpr (by linarith [htail_half n])
    have heq : Real.exp (2 * p13WidthTail run (n + 1)) =
        (Real.exp (p13WidthTail run (n + 1))) ^ 2 := by
      rw [show 2 * p13WidthTail run (n + 1) =
        p13WidthTail run (n + 1) + p13WidthTail run (n + 1) by ring,
        Real.exp_add, pow_two]
    rw [heq] at he
    unfold p13LinearMajorant
    nlinarith [sq_nonneg (Real.exp (p13WidthTail run (n + 1)) - 1)]
  have hmajor_bound (n : ℕ) :
      p13LinearMajorant run n ≤
        (1 / 2 : ℝ) ^ n * p13LinearMajorant run 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        p13LinearMajorant run (n + 1) ≤
            (1 / 2 : ℝ) * p13LinearMajorant run n := hmajor_half n
        _ ≤ (1 / 2 : ℝ) *
            ((1 / 2 : ℝ) ^ n * p13LinearMajorant run 0) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) * p13LinearMajorant run 0 := by
          rw [pow_succ]; ring
  have hzero : Tendsto (p13LinearMajorant run) atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hp' : Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) ^ n * p13LinearMajorant run 0)
        atTop (nhds 0) := by
      simpa using hp.mul_const (p13LinearMajorant run 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hp' (fun n => hmajor_nonneg n) (fun n => hmajor_bound n)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hsum
  · intro n
    constructor
    · exact data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)
  · exact hmajor_nonneg
  · exact hmajor_half
  · exact hzero

end VSCLReuse

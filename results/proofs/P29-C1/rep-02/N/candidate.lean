import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P29-C1: the inverse-action and multiplier bounds used in Theorem 3.6. -/
theorem p29_c1_calu_multiplier_growth
    (b H : ℕ) (ell : ℕ → ℕ → ℕ → ℝ)
    (probeIn probeOut z : ℕ → ℕ → ℝ)
    (hp : P29CALUMultiplierProcess b H ell probeIn probeOut z) :
    (∀ h, h < H → ∀ i, i < b →
      |probeOut h i| ≤ (2 : ℝ) ^ i) ∧
    (∀ i, i < b → |z H i| ≤ (2 : ℝ) ^ (b * H)) := by
  -- PROOF_START P29-C1-H001
  have geometric (n : ℕ) :
      1 + ∑ k ∈ Finset.range n, (2 : ℝ) ^ k = (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        nlinarith
  have action_bound (h : ℕ) (hh : h < H) (v w : ℕ → ℝ)
      (heq : ∀ i, i < b →
        ∑ k ∈ Finset.range b, ell h i k * v k = w i)
      (M : ℝ) (hM : 0 ≤ M)
      (hw : ∀ i, i < b → |w i| ≤ M) :
      ∀ i, i < b → |v i| ≤ M * (2 : ℝ) ^ i := by
    intro i hi
    induction i using Nat.strong_induction_on with
    | h i ih =>
        have hsmall :
            (∑ k ∈ Finset.range (i + 1), ell h i k * v k) =
              ∑ k ∈ Finset.range b, ell h i k * v k := by
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hi))
          intro k hk hkn
          have hik : i < k := by
            have hnot : ¬ k < i + 1 := by simpa using hkn
            omega
          rw [hp.upper_zero h hh i hi k (Finset.mem_range.mp hk) hik]
          simp
        have hrow :
            (∑ k ∈ Finset.range i, ell h i k * v k) + v i = w i := by
          have hrow' := heq i hi
          rw [← hsmall, Finset.sum_range_succ,
            hp.unit_diagonal h hh i hi, one_mul] at hrow'
          exact hrow'
        have hsum :
            (∑ k ∈ Finset.range i, |ell h i k * v k|) ≤
              ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k := by
          apply Finset.sum_le_sum
          intro k hk
          have hki : k < i := Finset.mem_range.mp hk
          calc
            |ell h i k * v k| = |ell h i k| * |v k| := abs_mul _ _
            _ ≤ |v k| :=
              mul_le_of_le_one_left (abs_nonneg _) (hp.coefficient_bound h hh i hi k hki)
            _ ≤ M * (2 : ℝ) ^ k := ih k hki (lt_trans hki hi)
        have hgeom :
            M + ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k =
              M * (2 : ℝ) ^ i := by
          calc
            M + ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k =
                M * (1 + ∑ k ∈ Finset.range i, (2 : ℝ) ^ k) := by
                  rw [mul_add, Finset.mul_sum]
                  ring
            _ = M * (2 : ℝ) ^ i := by rw [geometric i]
        calc
          |v i| = |w i - ∑ k ∈ Finset.range i, ell h i k * v k| := by
            congr 1
            linarith [hrow]
          _ ≤ |w i| + |∑ k ∈ Finset.range i, ell h i k * v k| := abs_sub _ _
          _ ≤ M + ∑ k ∈ Finset.range i, |ell h i k * v k| :=
            add_le_add (hw i hi) (Finset.abs_sum_le_sum_abs _ _)
          _ ≤ M + ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k :=
            add_le_add_right hsum M
          _ = M * (2 : ℝ) ^ i := hgeom
  constructor
  · intro h hh i hi
    simpa using action_bound h hh (probeOut h) (probeIn h)
      (hp.probe_equation h hh) 1 (by norm_num) (hp.probe_input_bound h hh) i hi
  · have level_bound : ∀ h, h ≤ H → ∀ i, i < b →
        |z h i| ≤ (2 : ℝ) ^ (b * h) := by
      intro h
      induction h with
      | zero =>
          intro _ i hi
          simpa using hp.base_bound i hi
      | succ h ih =>
          intro hh i hi
          have hh' : h < H := by omega
          have hstep := action_bound h hh' (z (h + 1)) (z h)
            (hp.level_equation h hh') ((2 : ℝ) ^ (b * h))
            (by positivity) (ih (by omega)) i hi
          calc
            |z (h + 1) i| ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ i := hstep
            _ = (2 : ℝ) ^ (b * h + i) := by rw [pow_add]
            _ ≤ (2 : ℝ) ^ (b * (h + 1)) := by
              apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
              simpa [Nat.mul_succ] using
                Nat.add_le_add_left (Nat.le_of_lt hi) (b * h)
    exact level_bound H le_rfl

end VSCLReuse

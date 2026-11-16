import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p29_two_pow_sum (n : ℕ) :
    1 + ∑ k ∈ Finset.range n, (2 : ℝ) ^ k = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      rw [← ih]
      ring

private lemma p29_unit_lower_action_bound
    (b : ℕ) (L : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (C : ℝ)
    (hdiag : ∀ i, i < b → L i i = 1)
    (hupper : ∀ i, i < b → ∀ k, k < b → i < k → L i k = 0)
    (hcoeff : ∀ i, i < b → ∀ k, k < i → |L i k| ≤ 1)
    (heq : ∀ i, i < b → ∑ k ∈ Finset.range b, L i k * x k = y i)
    (hy : ∀ i, i < b → |y i| ≤ C) :
    ∀ i, i < b → |x i| ≤ C * (2 : ℝ) ^ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      have htail : (∑ k ∈ Finset.Ico (i + 1) b, L i k * x k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hklo : i + 1 ≤ k := (Finset.mem_Ico.mp hk).1
        have hk' : k < b := (Finset.mem_Ico.mp hk).2
        have hik : i < k := by omega
        rw [hupper i hi k hk' hik]
        simp
      have hrow : x i = y i - ∑ k ∈ Finset.range i, L i k * x k := by
        have hsplit :
            (∑ k ∈ Finset.range b, L i k * x k) =
              (∑ k ∈ Finset.range i, L i k * x k) + x i := by
          calc
            _ = ∑ k ∈ Finset.range (i + 1), L i k * x k := by
              have hsplit0 := Finset.sum_range_add_sum_Ico
                (fun k => L i k * x k) (show i + 1 ≤ b by omega)
              rw [htail, add_zero] at hsplit0
              exact hsplit0.symm
            _ = (∑ k ∈ Finset.range i, L i k * x k) + L i i * x i :=
              Finset.sum_range_succ _ _
            _ = (∑ k ∈ Finset.range i, L i k * x k) + x i := by
              rw [hdiag i hi, one_mul]
        have heqi := heq i hi
        rw [hsplit] at heqi
        linarith
      have hsum :
          (∑ k ∈ Finset.range i, |L i k * x k|) ≤
            ∑ k ∈ Finset.range i, C * (2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        have hki : k < i := Finset.mem_range.mp hk
        have hkb : k < b := lt_trans hki hi
        rw [abs_mul]
        calc
          |L i k| * |x k| ≤ 1 * |x k| :=
            mul_le_mul_of_nonneg_right (hcoeff i hi k hki) (abs_nonneg _)
          _ = |x k| := one_mul _
          _ ≤ C * (2 : ℝ) ^ k := ih k hki hkb
      calc
        |x i| = |y i - ∑ k ∈ Finset.range i, L i k * x k| := by rw [hrow]
        _ ≤ |y i| + |∑ k ∈ Finset.range i, L i k * x k| := by
          simpa only [abs_neg] using abs_add_le (y i) (-(∑ k ∈ Finset.range i, L i k * x k))
        _ ≤ |y i| + ∑ k ∈ Finset.range i, |L i k * x k| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ C + ∑ k ∈ Finset.range i, C * (2 : ℝ) ^ k := by
          exact add_le_add (hy i hi) hsum
        _ = C * (1 + ∑ k ∈ Finset.range i, (2 : ℝ) ^ k) := by
          rw [mul_add, mul_one, Finset.mul_sum]
        _ = C * (2 : ℝ) ^ i := by rw [p29_two_pow_sum]

/-- P29-C1: the inverse-action and multiplier bounds used in Theorem 3.6. -/
theorem p29_c1_calu_multiplier_growth
    (b H : ℕ) (ell : ℕ → ℕ → ℕ → ℝ)
    (probeIn probeOut z : ℕ → ℕ → ℝ)
    (hp : P29CALUMultiplierProcess b H ell probeIn probeOut z) :
    (∀ h, h < H → ∀ i, i < b →
      |probeOut h i| ≤ (2 : ℝ) ^ i) ∧
    (∀ i, i < b → |z H i| ≤ (2 : ℝ) ^ (b * H)) := by
  -- PROOF_START P29-C1-H001
  constructor
  · intro h hh i hi
    simpa using p29_unit_lower_action_bound b (ell h) (probeOut h) (probeIn h) 1
      (hp.unit_diagonal h hh) (hp.upper_zero h hh)
      (hp.coefficient_bound h hh) (hp.probe_equation h hh)
      (hp.probe_input_bound h hh) i hi
  · have hz : ∀ h, h ≤ H → ∀ i, i < b →
        |z h i| ≤ (2 : ℝ) ^ (b * h) := by
      intro h
      induction h with
      | zero =>
          intro _ i hi
          simpa using hp.base_bound i hi
      | succ h ih =>
          intro hH i hi
          have hh : h < H := by omega
          have hstep := p29_unit_lower_action_bound b (ell h) (z (h + 1)) (z h)
            ((2 : ℝ) ^ (b * h))
            (hp.unit_diagonal h hh) (hp.upper_zero h hh)
            (hp.coefficient_bound h hh) (hp.level_equation h hh)
            (ih (by omega)) i hi
          calc
            |z (h + 1) i| ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ i := hstep
            _ = (2 : ℝ) ^ (b * h + i) := by rw [pow_add]
            _ ≤ (2 : ℝ) ^ (b * (h + 1)) := by
              apply pow_le_pow_right₀ (by norm_num)
              rw [Nat.mul_succ]
              omega
    exact hz H le_rfl

end VSCLReuse

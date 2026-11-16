import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p29_sum_two_pow (n : ℕ) :
    1 + (∑ k ∈ Finset.range n, (2 : ℝ) ^ k) = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith

private lemma p29_triangular_solve_bound
    (b : ℕ) (a : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (M : ℝ)
    (hdiag : ∀ i, i < b → a i i = 1)
    (hupper : ∀ i, i < b → ∀ k, k < b → i < k → a i k = 0)
    (hcoeff : ∀ i, i < b → ∀ k, k < i → |a i k| ≤ 1)
    (heq : ∀ i, i < b → ∑ k ∈ Finset.range b, a i k * x k = y i)
    (hy : ∀ i, i < b → |y i| ≤ M) :
    ∀ i, i < b → |x i| ≤ (2 : ℝ) ^ i * M := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have htail : (∑ k ∈ Finset.Ico (i + 1) b, a i k * x k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hki : i < k := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        have hkb : k < b := (Finset.mem_Ico.mp hk).2
        rw [hupper i hi k hkb hki, zero_mul]
      have hsum : (∑ k ∈ Finset.range b, a i k * x k) =
          (∑ k ∈ Finset.range (i + 1), a i k * x k) := by
        rw [← Finset.sum_range_add_sum_Ico (fun k => a i k * x k)
          (Nat.succ_le_of_lt hi), htail, add_zero]
      have hrec : x i = y i - (∑ k ∈ Finset.range i, a i k * x k) := by
        have hrow := heq i hi
        rw [hsum, Finset.sum_range_succ, hdiag i hi, one_mul] at hrow
        linarith
      have hterms :
          (∑ k ∈ Finset.range i, |a i k * x k|) ≤
          (∑ k ∈ Finset.range i, (2 : ℝ) ^ k * M) := by
        apply Finset.sum_le_sum
        intro k hk
        have hki : k < i := Finset.mem_range.mp hk
        rw [abs_mul]
        calc
          |a i k| * |x k| ≤ 1 * |x k| :=
            mul_le_mul_of_nonneg_right (hcoeff i hi k hki) (abs_nonneg _)
          _ = |x k| := one_mul _
          _ ≤ (2 : ℝ) ^ k * M := ih k hki (lt_trans hki hi)
      calc
        |x i| = |y i - (∑ k ∈ Finset.range i, a i k * x k)| := by rw [hrec]
        _ ≤ |y i| + |∑ k ∈ Finset.range i, a i k * x k| := abs_sub _ _
        _ ≤ M + (∑ k ∈ Finset.range i, |a i k * x k|) := by
          exact add_le_add (hy i hi)
            (Finset.abs_sum_le_sum_abs (fun k => a i k * x k) (Finset.range i))
        _ ≤ M + (∑ k ∈ Finset.range i, (2 : ℝ) ^ k * M) := by
          exact add_le_add (le_refl M) hterms
        _ = (2 : ℝ) ^ i * M := by
          rw [← Finset.sum_mul]
          calc
            M + (∑ k ∈ Finset.range i, (2 : ℝ) ^ k) * M =
                (1 + ∑ k ∈ Finset.range i, (2 : ℝ) ^ k) * M := by ring
            _ = (2 : ℝ) ^ i * M := by rw [p29_sum_two_pow]

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
    have hbound := p29_triangular_solve_bound b (ell h) (probeOut h) (probeIn h) 1
      (hp.unit_diagonal h hh) (hp.upper_zero h hh)
      (hp.coefficient_bound h hh) (hp.probe_equation h hh)
      (hp.probe_input_bound h hh) i hi
    simpa using hbound
  · have hz : ∀ h, h ≤ H → ∀ i, i < b →
        |z h i| ≤ (2 : ℝ) ^ (b * h) := by
      intro h
      induction h with
      | zero =>
          intro _ i hi
          simpa using hp.base_bound i hi
      | succ h ih =>
          intro hh i hi
          have hhH : h < H := by omega
          have hbound := p29_triangular_solve_bound b (ell h) (z (h + 1)) (z h)
            ((2 : ℝ) ^ (b * h))
            (hp.unit_diagonal h hhH) (hp.upper_zero h hhH)
            (hp.coefficient_bound h hhH) (hp.level_equation h hhH)
            (ih (by omega)) i hi
          have hpow : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ b := by
            exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hi)
          have hm : (2 : ℝ) ^ i * (2 : ℝ) ^ (b * h) ≤
              (2 : ℝ) ^ b * (2 : ℝ) ^ (b * h) := by
            gcongr
          calc
            |z (h + 1) i| ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ (b * h) := hbound
            _ ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b * h) := hm
            _ = (2 : ℝ) ^ (b * (h + 1)) := by rw [← pow_add]; congr 1; ring
    exact hz H (le_refl H)

end VSCLReuse

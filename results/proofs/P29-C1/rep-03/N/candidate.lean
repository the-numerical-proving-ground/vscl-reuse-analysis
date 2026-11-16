import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p29_sum_two_powers (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℝ) ^ k) + 1 = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith

private lemma p29_lower_inverse_action
    (b : ℕ) (a : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hx : ∀ i, i < b → |x i| ≤ M)
    (hdiag : ∀ i, i < b → a i i = 1)
    (hupper : ∀ i, i < b → ∀ k, k < b → i < k → a i k = 0)
    (hcoeff : ∀ i, i < b → ∀ k, k < i → |a i k| ≤ 1)
    (heq : ∀ i, i < b → ∑ k ∈ Finset.range b, a i k * y k = x i) :
    ∀ i, i < b → |y i| ≤ M * (2 : ℝ) ^ i := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hsum : (∑ k ∈ Finset.range b, a i k * y k) =
        ∑ k ∈ Finset.range (i + 1), a i k * y k := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hi))
      intro k hk hnot
      have hkb : k < b := Finset.mem_range.mp hk
      have hik : i < k := by
        have : ¬ k < i + 1 := by simpa only [Finset.mem_range] using hnot
        omega
      simp [hupper i hi k hkb hik]
    have hrow : (∑ k ∈ Finset.range i, a i k * y k) + y i = x i := by
      have h := heq i hi
      rw [hsum, Finset.sum_range_succ, hdiag i hi, one_mul] at h
      exact h
    have hterms : ∀ k ∈ Finset.range i, |a i k * y k| ≤ M * (2 : ℝ) ^ k := by
      intro k hk
      have hki : k < i := Finset.mem_range.mp hk
      have hky : |y k| ≤ M * (2 : ℝ) ^ k := ih k hki (by omega)
      rw [abs_mul]
      calc
        |a i k| * |y k| ≤ 1 * |y k| :=
          mul_le_mul_of_nonneg_right (hcoeff i hi k hki) (abs_nonneg _)
        _ = |y k| := one_mul _
        _ ≤ M * (2 : ℝ) ^ k := hky
    have hsumabs : |∑ k ∈ Finset.range i, a i k * y k| ≤
        ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterms)
    have hgeom : M + (∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k) =
        M * (2 : ℝ) ^ i := by
      rw [← Finset.mul_sum]
      have h := p29_sum_two_powers i
      nlinarith
    have hy : y i = x i - ∑ k ∈ Finset.range i, a i k * y k := by
      linarith [hrow]
    rw [hy]
    calc
      |x i - ∑ k ∈ Finset.range i, a i k * y k| ≤
          |x i| + |∑ k ∈ Finset.range i, a i k * y k| := abs_sub _ _
      _ ≤ M + (∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k) :=
          add_le_add (hx i hi) hsumabs
      _ = M * (2 : ℝ) ^ i := hgeom

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
    have hbound := p29_lower_inverse_action b (ell h) (probeIn h) (probeOut h) 1
      (by norm_num) (hp.probe_input_bound h hh)
      (hp.unit_diagonal h hh) (hp.upper_zero h hh)
      (hp.coefficient_bound h hh) (hp.probe_equation h hh) i hi
    simpa using hbound
  · have hlevel : ∀ h, h ≤ H → ∀ i, i < b →
        |z h i| ≤ (2 : ℝ) ^ (b * h) := by
      intro h
      induction h with
      | zero =>
          intro _ i hi
          simpa using hp.base_bound i hi
      | succ h ih =>
          intro hH i hi
          have hh : h < H := by omega
          have hbound := p29_lower_inverse_action b (ell h) (z h) (z (h + 1))
            ((2 : ℝ) ^ (b * h)) (by positivity)
            (ih (by omega)) (hp.unit_diagonal h hh) (hp.upper_zero h hh)
            (hp.coefficient_bound h hh) (hp.level_equation h hh) i hi
          calc
            |z (h + 1) i| ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ i := hbound
            _ ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ b := by
              have hpowers : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ b := by
                exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hi)
              exact mul_le_mul_of_nonneg_left hpowers (by positivity)
            _ = (2 : ℝ) ^ (b * (h + 1)) := by rw [Nat.mul_succ, pow_add]
    exact hlevel H (le_refl H)

end VSCLReuse

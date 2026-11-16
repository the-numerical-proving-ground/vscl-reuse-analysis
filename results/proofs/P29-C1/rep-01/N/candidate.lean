import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem calu_geometric_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (2 : ℝ) ^ k) = (2 : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem calu_triangular_solve_bound
    (b : ℕ) (L : ℕ → ℕ → ℝ) (u v : ℕ → ℝ) (M : ℝ)
    (hdiag : ∀ i, i < b → L i i = 1)
    (hupper : ∀ i, i < b → ∀ k, k < b → i < k → L i k = 0)
    (hlower : ∀ i, i < b → ∀ k, k < i → |L i k| ≤ 1)
    (heq : ∀ i, i < b → ∑ k ∈ Finset.range b, L i k * v k = u i)
    (hinput : ∀ i, i < b → |u i| ≤ M) :
    ∀ i, i < b → |v i| ≤ M * (2 : ℝ) ^ i := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have hsum :
          (∑ k ∈ Finset.range b, L i k * v k) =
            (∑ k ∈ Finset.range i, L i k * v k) + v i := by
        have hs :
            (∑ k ∈ Finset.range (i + 1), L i k * v k) =
              ∑ k ∈ Finset.range b, L i k * v k := by
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hi))
          intro k hkb hki
          have hik : i < k := by
            have hki' : i + 1 ≤ k := Nat.le_of_not_lt (by simpa using hki)
            omega
          simp [hupper i hi k (Finset.mem_range.mp hkb) hik]
        rw [← hs, Finset.sum_range_succ, hdiag i hi, one_mul]
      have hv : v i = u i - ∑ k ∈ Finset.range i, L i k * v k := by
        have heqi := heq i hi
        rw [hsum] at heqi
        linarith
      have hterms :
          (∑ k ∈ Finset.range i, |L i k * v k|) ≤
            ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        have hki : k < i := Finset.mem_range.mp hk
        calc
          |L i k * v k| = |L i k| * |v k| := abs_mul _ _
          _ ≤ 1 * |v k| :=
            mul_le_mul_of_nonneg_right (hlower i hi k hki) (abs_nonneg _)
          _ = |v k| := one_mul _
          _ ≤ M * (2 : ℝ) ^ k := ih k hki (lt_trans hki hi)
      calc
        |v i| = |u i - ∑ k ∈ Finset.range i, L i k * v k| := congrArg abs hv
        _ ≤ |u i| + |∑ k ∈ Finset.range i, L i k * v k| := abs_sub _ _
        _ ≤ M + ∑ k ∈ Finset.range i, |L i k * v k| :=
          add_le_add (hinput i hi) (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ M + ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k :=
          add_le_add (le_refl M) hterms
        _ = M * (2 : ℝ) ^ i := by
          rw [← Finset.mul_sum, calu_geometric_sum]
          ring

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
    have hbound := calu_triangular_solve_bound b (ell h) (probeIn h)
      (probeOut h) 1
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
          have hlt : h < H := by omega
          have hM : 0 ≤ (2 : ℝ) ^ (b * h) := pow_nonneg (by norm_num) _
          have hbound := calu_triangular_solve_bound b (ell h) (z h)
            (z (h + 1)) ((2 : ℝ) ^ (b * h))
            (hp.unit_diagonal h hlt) (hp.upper_zero h hlt)
            (hp.coefficient_bound h hlt) (hp.level_equation h hlt)
            (ih (by omega)) i hi
          calc
            |z (h + 1) i| ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ i := hbound
            _ ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ b :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hi)) hM
            _ = (2 : ℝ) ^ (b * (h + 1)) := by
              rw [mul_add, mul_one, pow_add]
    exact hz H (le_refl H)

end VSCLReuse

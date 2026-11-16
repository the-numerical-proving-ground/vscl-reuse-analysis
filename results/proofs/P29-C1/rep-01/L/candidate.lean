import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p29_unit_lower_solve_bound
    (b : ℕ) (L : ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (M : ℝ)
    (hy : ∀ i, i < b → |y i| ≤ M)
    (hdiag : ∀ i, i < b → L i i = 1)
    (hupper : ∀ i, i < b → ∀ k, k < b → i < k → L i k = 0)
    (hcoeff : ∀ i, i < b → ∀ k, k < i → |L i k| ≤ 1)
    (heq : ∀ i, i < b → ∑ k ∈ Finset.range b, L i k * x k = y i) :
    ∀ i, i < b → |x i| ≤ M * (2 : ℝ) ^ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    have hsum : ∑ k ∈ Finset.range (i + 1), L i k * x k = y i := by
      rw [← heq i hi]
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro k hk hknot
      have hkb : k < b := Finset.mem_range.mp hk
      have hik : i < k := by
        have : ¬ k < i + 1 := by simpa using hknot
        omega
      rw [hupper i hi k hkb hik, zero_mul]
    rw [Finset.sum_range_succ, hdiag i hi, one_mul] at hsum
    have hx : x i = y i - ∑ k ∈ Finset.range i, L i k * x k := by
      linarith
    have hterms :
        ∑ k ∈ Finset.range i, |L i k * x k| ≤
          ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hki : k < i := Finset.mem_range.mp hk
      calc
        |L i k * x k| = |L i k| * |x k| := abs_mul _ _
        _ ≤ 1 * |x k| :=
          mul_le_mul_of_nonneg_right (hcoeff i hi k hki) (abs_nonneg _)
        _ = |x k| := one_mul _
        _ ≤ M * (2 : ℝ) ^ k := ih k hki (by omega)
    have hgeom : (∑ k ∈ Finset.range i, (2 : ℝ) ^ k) + 1 = (2 : ℝ) ^ i := by
      simpa [show (1 : ℝ) + 1 = 2 by norm_num] using geom_sum_mul_add (1 : ℝ) i
    calc
      |x i| = |y i - ∑ k ∈ Finset.range i, L i k * x k| := congrArg abs hx
      _ ≤ |y i| + |∑ k ∈ Finset.range i, L i k * x k| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (y i) (-(∑ k ∈ Finset.range i, L i k * x k)))
      _ ≤ M + ∑ k ∈ Finset.range i, |L i k * x k| := by
        exact add_le_add (hy i hi) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ M + ∑ k ∈ Finset.range i, M * (2 : ℝ) ^ k :=
        add_le_add (le_refl M) hterms
      _ = M * (2 : ℝ) ^ i := by
        rw [← Finset.mul_sum]
        calc
          M + M * (∑ k ∈ Finset.range i, (2 : ℝ) ^ k) =
              M * ((∑ k ∈ Finset.range i, (2 : ℝ) ^ k) + 1) := by ring
          _ = M * (2 : ℝ) ^ i := by rw [hgeom]

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
    have hb := p29_unit_lower_solve_bound b (ell h) (probeOut h) (probeIn h) 1
      (hp.probe_input_bound h hh)
      (hp.unit_diagonal h hh)
      (hp.upper_zero h hh)
      (hp.coefficient_bound h hh)
      (hp.probe_equation h hh) i hi
    simpa using hb
  · have hz : ∀ h : ℕ, h ≤ H → ∀ i, i < b →
        |z h i| ≤ (2 : ℝ) ^ (b * h) := by
      intro h
      induction h with
      | zero =>
        intro _ i hi
        simpa using hp.base_bound i hi
      | succ h ih =>
        intro hh i hi
        have hlt : h < H := by omega
        have hb := p29_unit_lower_solve_bound b (ell h) (z (h + 1)) (z h)
          ((2 : ℝ) ^ (b * h))
          (ih (by omega))
          (hp.unit_diagonal h hlt)
          (hp.upper_zero h hlt)
          (hp.coefficient_bound h hlt)
          (hp.level_equation h hlt) i hi
        calc
          |z (h + 1) i| ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ i := hb
          _ ≤ (2 : ℝ) ^ (b * h) * (2 : ℝ) ^ b := by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hi)) (by positivity)
          _ = (2 : ℝ) ^ (b * (h + 1)) := by rw [Nat.mul_succ, pow_add]
    exact hz H (le_refl H)

end VSCLReuse

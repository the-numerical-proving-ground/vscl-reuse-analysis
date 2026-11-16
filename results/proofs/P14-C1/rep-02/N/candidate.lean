import VSCLReuse.P14.Definitions

namespace VSCLReuse

open scoped BigOperators Topology

private lemma p14_exponent_decomposition (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = (p + 1) * m + p * n := by
  let q := k / p
  let m := k % p
  have hq : p - 1 ≤ q := (Nat.le_div_iff_mul_le hp).2 (by
    simpa only [Nat.mul_comm] using hk)
  have hm : m < p := Nat.mod_lt k hp
  have hmq : m ≤ q := by omega
  refine ⟨m, q - m, ?_⟩
  calc
    k = m + p * q := by exact (Nat.mod_add_div k p).symm
    _ = m + p * (m + (q - m)) := by rw [Nat.add_sub_of_le hmq]
    _ = (p + 1) * m + p * (q - m) := by ring

private lemma p14_norm_power_bound {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r) (a b m n : ℕ)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ (a * m + b * n)‖ ≤ r ^ (a * m + b * n) := by
  calc
    ‖A ^ (a * m + b * n)‖ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n := by
      rw [pow_add, pow_mul, pow_mul]
      exact (norm_mul_le _ _).trans
        (mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
          (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n := by gcongr
    _ = r ^ (a * m + b * n) := by rw [pow_add, pow_mul, pow_mul]

private lemma p14_series_bound_of_power_bounds
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hpow : ∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) :
    P14SeriesBound c A r := by
  have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hc : c k = 0
    · simp [hc]
    · calc
        ‖c k • A ^ k‖ = ‖c k‖ * ‖A ^ k‖ := norm_smul _ _
        _ ≤ ‖c k‖ * r ^ k := mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg _)
  exact ⟨Summable.of_norm_bounded hs hterm, by
    simpa only [p14SeriesValue, p14AbsoluteSeries] using
      (tsum_of_norm_bounded hs.hasSum hterm)⟩

/-- P14-C1: the ordinary and even power-series bounds of Theorem 4.2. -/
theorem p14_c1_theorem4_2
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (p ℓ : ℕ) (hp : 0 < p)
    (hcutoff : ∀ k < ℓ, c k = 0) :
    (∀ r : ℝ, 0 ≤ r → p * (p - 1) ≤ ℓ →
      ‖A ^ p‖ ≤ r ^ p →
      ‖A ^ (p + 1)‖ ≤ r ^ (p + 1) →
      Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k) →
      P14SeriesBound c A r) ∧
    ((∀ k : ℕ, ¬Even k → c k = 0) →
      ∀ r : ℝ, 0 ≤ r → 2 * p * (p - 1) ≤ ℓ →
        ‖A ^ (2 * p)‖ ≤ r ^ (2 * p) →
        ‖A ^ (2 * (p + 1))‖ ≤ r ^ (2 * (p + 1)) →
        Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k) →
        P14SeriesBound c A r) := by
  -- PROOF_START P14-C1-H001
  constructor
  · intro r hr hℓ ha hb hs
    apply p14_series_bound_of_power_bounds c A r hs
    intro k hc
    have hk : p * (p - 1) ≤ k :=
      le_trans hℓ (Nat.le_of_not_gt (fun h ↦ hc (hcutoff k h)))
    obtain ⟨m, n, hmn⟩ := p14_exponent_decomposition p k hp hk
    rw [hmn]
    exact p14_norm_power_bound A r hr (p + 1) p m n hb ha
  · intro heven r hr hℓ ha hb hs
    apply p14_series_bound_of_power_bounds c A r hs
    intro k hc
    have hkℓ : ℓ ≤ k := Nat.le_of_not_gt (fun h ↦ hc (hcutoff k h))
    have hkeven : Even k := by
      by_contra h
      exact hc (heven k h)
    obtain ⟨j, rfl⟩ := even_iff_two_dvd.mp hkeven
    have hj : p * (p - 1) ≤ j := by
      have h : 2 * p * (p - 1) ≤ 2 * j := le_trans hℓ hkℓ
      nlinarith
    obtain ⟨m, n, hmn⟩ := p14_exponent_decomposition p j hp hj
    have heq : 2 * j = (2 * (p + 1)) * m + (2 * p) * n := by
      rw [hmn]
      ring
    rw [heq]
    exact p14_norm_power_bound A r hr (2 * (p + 1)) (2 * p) m n hb ha

end VSCLReuse

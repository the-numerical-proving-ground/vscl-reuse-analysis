import VSCLReuse.P14.Definitions

namespace VSCLReuse

open scoped BigOperators Topology

private lemma p14_span_nat (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = (p + 1) * m + p * n := by
  have hq : p - 1 ≤ k / p :=
    (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.mul_comm] using hk)
  have hm : k % p < p := Nat.mod_lt k hp
  have hmq : k % p ≤ k / p := by omega
  refine ⟨k % p, k / p - k % p, ?_⟩
  calc
    k = k % p + p * (k / p) := (Nat.mod_add_div k p).symm
    _ = k % p + p * ((k / p - k % p) + k % p) := by
      rw [Nat.sub_add_cancel hmq]
    _ = (p + 1) * (k % p) + p * (k / p - k % p) := by ring

private lemma p14_pow_span {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (a b m n : ℕ)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ (a * m + b * n)‖ ≤ r ^ (a * m + b * n) := by
  calc
    ‖A ^ (a * m + b * n)‖ = ‖(A ^ a) ^ m * (A ^ b) ^ n‖ := by
      rw [pow_add, pow_mul, pow_mul]
    _ ≤ ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n := by
      exact mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
        (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n := by
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha m)
        (pow_le_pow_left₀ (norm_nonneg _) hb n)
        (pow_nonneg (norm_nonneg _) _) (pow_nonneg (le_trans (norm_nonneg _) ha) _)
    _ = r ^ (a * m + b * n) := by rw [← pow_mul, ← pow_mul, ← pow_add]

private lemma p14_series_bound_of_powers
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ) (ℓ : ℕ)
    (hcutoff : ∀ k < ℓ, c k = 0)
    (hpow : ∀ k ≥ ℓ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k)) :
    P14SeriesBound c A r := by
  have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hc : c k = 0
    · simp [hc]
    · have hk : ℓ ≤ k := by
        by_contra hn
        exact hc (hcutoff k (Nat.lt_of_not_ge hn))
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hpow k hk hc) (norm_nonneg _)
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm hs
  refine ⟨Summable.of_norm_bounded hs hterm, ?_⟩
  change ‖∑' k : ℕ, c k • A ^ k‖ ≤ ∑' k : ℕ, ‖c k‖ * r ^ k
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm hs)

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
  · intro r hr hℓ hAp hAp1 hs
    apply p14_series_bound_of_powers c A r ℓ hcutoff _ hs
    intro k hk _
    obtain ⟨m, n, hmn⟩ := p14_span_nat p k hp (le_trans hℓ hk)
    rw [hmn]
    exact p14_pow_span A r (p + 1) p m n hAp1 hAp
  · intro heven r hr hℓ hA2p hA2p2 hs
    apply p14_series_bound_of_powers c A r ℓ hcutoff _ hs
    intro k hk hck
    have hkeven : Even k := by
      by_contra hne
      exact hck (heven k hne)
    obtain ⟨j, hj⟩ := (even_iff_two_dvd.mp hkeven)
    have hjcut : p * (p - 1) ≤ j := by
      apply Nat.le_of_mul_le_mul_left (c := 2)
      · simpa [hj, mul_assoc] using le_trans hℓ hk
      · omega
    obtain ⟨m, n, hmn⟩ := p14_span_nat p j hp hjcut
    have hkmn : k = (2 * (p + 1)) * m + (2 * p) * n := by
      rw [hj, hmn]
      ring
    rw [hkmn]
    exact p14_pow_span A r (2 * (p + 1)) (2 * p) m n hA2p2 hA2p

end VSCLReuse

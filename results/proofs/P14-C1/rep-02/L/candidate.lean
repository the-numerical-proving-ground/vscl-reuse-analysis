import VSCLReuse.P14.Definitions

namespace VSCLReuse

open scoped BigOperators Topology

private lemma p14_coins (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ u v : ℕ, k = (p + 1) * u + p * v := by
  let q := k / p
  let s := k % p
  have hs : s < p := Nat.mod_lt k hp
  have hq : p - 1 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hp).2 (by simpa [mul_comm] using hk)
  have hsq : s ≤ q := by omega
  have hks : s + p * q = k := Nat.mod_add_div k p
  have hsub : q - s + s = q := Nat.sub_add_cancel hsq
  refine ⟨s, q - s, ?_⟩
  nlinarith

private lemma p14_norm_pow_le_of_coins
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r)
    (a b u v k : ℕ) (hk : k = a * u + b * v)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ k‖ ≤ r ^ k := by
  have h₁ : ‖(A ^ a) ^ u‖ ≤ (r ^ a) ^ u :=
    (norm_pow_le (A ^ a) u).trans (pow_le_pow_left₀ (norm_nonneg _) ha u)
  have h₂ : ‖(A ^ b) ^ v‖ ≤ (r ^ b) ^ v :=
    (norm_pow_le (A ^ b) v).trans (pow_le_pow_left₀ (norm_nonneg _) hb v)
  calc
    ‖A ^ k‖ = ‖(A ^ a) ^ u * (A ^ b) ^ v‖ := by rw [← pow_mul, ← pow_mul, ← pow_add, hk]
    _ ≤ ‖(A ^ a) ^ u‖ * ‖(A ^ b) ^ v‖ := norm_mul_le _ _
    _ ≤ (r ^ a) ^ u * (r ^ b) ^ v :=
      mul_le_mul h₁ h₂ (norm_nonneg _) (pow_nonneg (pow_nonneg hr _) _)
    _ = r ^ k := by rw [← pow_mul, ← pow_mul, ← pow_add, hk]

private lemma p14_series_bound_of_power_bound
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hpow : ∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k)
    (hsum : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k)) :
    P14SeriesBound c A r := by
  have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hc : c k = 0
    · simp [hc]
    · exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg _))
  exact ⟨hsum.of_norm_bounded hterm,
    by simpa only [p14SeriesValue, p14AbsoluteSeries] using
      (tsum_of_norm_bounded hsum.hasSum hterm)⟩

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
  · intro r hr hℓ ha hb hsum
    apply p14_series_bound_of_power_bound c A r ?_ hsum
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hn
      exact hck (hcutoff k (Nat.lt_of_not_ge hn))
    obtain ⟨u, v, huv⟩ := p14_coins p k hp (le_trans hℓ hkℓ)
    exact p14_norm_pow_le_of_coins A r hr (p + 1) p u v k huv hb ha
  · intro heven r hr hℓ ha hb hsum
    apply p14_series_bound_of_power_bound c A r ?_ hsum
    intro k hck
    have hkℓ : ℓ ≤ k := by
      by_contra hn
      exact hck (hcutoff k (Nat.lt_of_not_ge hn))
    have hkEven : Even k := by
      by_contra hn
      exact hck (heven k hn)
    obtain ⟨j, rfl⟩ := even_iff_two_dvd.mp hkEven
    have hj : p * (p - 1) ≤ j := by
      have : 2 * (p * (p - 1)) ≤ 2 * j := by
        nlinarith [le_trans hℓ hkℓ]
      omega
    obtain ⟨u, v, huv⟩ := p14_coins p j hp hj
    have hcoin : 2 * j = (2 * (p + 1)) * u + (2 * p) * v := by
      nlinarith
    exact p14_norm_pow_le_of_coins A r hr (2 * (p + 1)) (2 * p) u v (2 * j)
      hcoin hb ha

end VSCLReuse

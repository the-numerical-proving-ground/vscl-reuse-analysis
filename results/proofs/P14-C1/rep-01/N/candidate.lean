import VSCLReuse.P14.Definitions

namespace VSCLReuse

open scoped BigOperators Topology

private lemma p14_pow_bound
    {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (a b m n : ℕ)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ (a * m + b * n)‖ ≤ r ^ (a * m + b * n) := by
  have hra : 0 ≤ r ^ a := (norm_nonneg _).trans ha
  calc
    ‖A ^ (a * m + b * n)‖ = ‖(A ^ a) ^ m * (A ^ b) ^ n‖ := by
      rw [pow_add, pow_mul, pow_mul]
    _ ≤ ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n := by
      gcongr <;> apply norm_pow_le
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n := by
      gcongr
    _ = r ^ (a * m + b * n) := by rw [← pow_mul, ← pow_mul, ← pow_add]

private lemma p14_cofinite_rep (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = (p + 1) * m + p * n := by
  let q := k / p
  let s := k % p
  have hq : p - 1 ≤ q := (Nat.le_div_iff_mul_le hp).2 (by
    simpa only [Nat.mul_comm] using hk)
  have hslt : s < p := Nat.mod_lt k hp
  have hs : s ≤ q := by omega
  refine ⟨s, q - s, ?_⟩
  have hdiv : p * q + s = k := Nat.div_add_mod k p
  have hsub : q - s + s = q := Nat.sub_add_cancel hs
  nlinarith

private lemma p14_series_bound_of_pow_bound
    {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hpow : ∀ k, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k)) :
    P14SeriesBound c A r := by
  have hterm (k : ℕ) : ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    by_cases hc : c k = 0
    · simp [hc]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg _)
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hs
  exact ⟨hnorm.of_norm,
    (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_mono hs hterm)⟩

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
  · intro r hr hℓ hap hap1 hs
    apply p14_series_bound_of_pow_bound c A r ?_ hs
    intro k hck
    have hk : ℓ ≤ k := by
      by_contra h
      exact hck (hcutoff k (Nat.lt_of_not_ge h))
    obtain ⟨m, n, rfl⟩ := p14_cofinite_rep p k hp (hℓ.trans hk)
    exact p14_pow_bound A r (p + 1) p m n hap1 hap
  · intro heven r hr hℓ hap hap1 hs
    apply p14_series_bound_of_pow_bound c A r ?_ hs
    intro k hck
    have hk : ℓ ≤ k := by
      by_contra h
      exact hck (hcutoff k (Nat.lt_of_not_ge h))
    have he : Even k := by
      by_contra h
      exact hck (heven k h)
    obtain ⟨j, hj⟩ := even_iff_two_dvd.mp he
    subst k
    have hjcut : p * (p - 1) ≤ j := by
      nlinarith [hℓ.trans hk]
    obtain ⟨m, n, hrep⟩ := p14_cofinite_rep p j hp hjcut
    have hrep2 : 2 * j = (2 * (p + 1)) * m + (2 * p) * n := by
      nlinarith [hrep]
    rw [hrep2]
    exact p14_pow_bound A r (2 * (p + 1)) (2 * p) m n hap1 hap

end VSCLReuse

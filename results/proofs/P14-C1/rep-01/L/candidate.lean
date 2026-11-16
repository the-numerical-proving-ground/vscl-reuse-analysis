import VSCLReuse.P14.Definitions

namespace VSCLReuse

open scoped BigOperators Topology

private lemma p14_decompose (p k : ℕ) (hp : 0 < p)
    (hk : p * (p - 1) ≤ k) :
    ∃ m n : ℕ, k = p * m + (p + 1) * n := by
  let q := k / p
  let t := k % p
  have hq : p - 1 ≤ q := by
    apply (Nat.le_div_iff_mul_le hp).2
    simpa only [Nat.mul_comm] using hk
  have ht : t ≤ p - 1 := Nat.le_pred_of_lt (Nat.mod_lt k hp)
  have htq : t ≤ q := ht.trans hq
  refine ⟨q - t, t, ?_⟩
  have hmul : p * (q - t) + p * t = p * q := by
    rw [← mul_add, Nat.sub_add_cancel htq]
  calc
    k = t + p * q := (Nat.mod_add_div k p).symm
    _ = p * (q - t) + (p + 1) * t := by
      calc
        t + p * q = t + (p * (q - t) + p * t) := by rw [hmul]
        _ = p * (q - t) + (p + 1) * t := by ring

private lemma p14_power_of_decomp {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (hr : 0 ≤ r) (a b m n : ℕ)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b) :
    ‖A ^ (a * m + b * n)‖ ≤ r ^ (a * m + b * n) := by
  calc
    ‖A ^ (a * m + b * n)‖ = ‖(A ^ a) ^ m * (A ^ b) ^ n‖ := by
      rw [pow_add, pow_mul, pow_mul]
    _ ≤ ‖(A ^ a) ^ m‖ * ‖(A ^ b) ^ n‖ := norm_mul_le _ _
    _ ≤ ‖A ^ a‖ ^ m * ‖A ^ b‖ ^ n := by
      apply mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _)
      · positivity
      · positivity
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n := by
      apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha m)
        (pow_le_pow_left₀ (norm_nonneg _) hb n)
      · positivity
      · positivity
    _ = r ^ (a * m + b * n) := by rw [pow_add, pow_mul, pow_mul]

private lemma p14_series_of_power_bound {E : Type*} [NormedRing E]
    [NormOneClass E] [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hs : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hp : ∀ k, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) :
    P14SeriesBound c A r := by
  have hterm (k : ℕ) : ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    by_cases hc : c k = 0
    · simp [hc]
    · simpa only [norm_smul] using
        mul_le_mul_of_nonneg_left (hp k hc) (norm_nonneg (c k))
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hs
  have hseries : Summable (fun k : ℕ ↦ c k • A ^ k) :=
    Summable.of_norm_bounded hs hterm
  refine ⟨hseries, ?_⟩
  change ‖∑' k : ℕ, c k • A ^ k‖ ≤ ∑' k : ℕ, ‖c k‖ * r ^ k
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_mono hs hterm)

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
    apply p14_series_of_power_bound c A r hs
    intro k hc
    have hk : ℓ ≤ k := by
      by_contra h
      exact hc (hcutoff k (Nat.lt_of_not_ge h))
    obtain ⟨m, n, hkn⟩ := p14_decompose p k hp (hℓ.trans hk)
    rw [hkn]
    exact p14_power_of_decomp A r hr p (p + 1) m n hAp hAp1
  · intro heven r hr hℓ hA2p hA2p1 hs
    apply p14_series_of_power_bound c A r hs
    intro k hc
    have hk : ℓ ≤ k := by
      by_contra h
      exact hc (hcutoff k (Nat.lt_of_not_ge h))
    have hk_even : Even k := by
      by_contra h
      exact hc (heven k h)
    obtain ⟨j, rfl⟩ := hk_even
    have hj : p * (p - 1) ≤ j := by
      have h : 2 * p * (p - 1) ≤ j + j := hℓ.trans hk
      have h' : 2 * (p * (p - 1)) ≤ j + j := by
        simpa only [mul_assoc] using h
      omega
    obtain ⟨m, n, hjmn⟩ := p14_decompose p j hp hj
    have hdecomp : j + j = (2 * p) * m + (2 * (p + 1)) * n := by
      calc
        j + j = 2 * j := by omega
        _ = 2 * (p * m + (p + 1) * n) := by rw [hjmn]
        _ = (2 * p) * m + (2 * (p + 1)) * n := by ring
    rw [hdecomp]
    exact p14_power_of_decomp A r hr (2 * p) (2 * (p + 1)) m n hA2p hA2p1

end VSCLReuse

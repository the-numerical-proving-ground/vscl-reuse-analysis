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
    simpa [mul_comm] using hk
  have ht : t < p := Nat.mod_lt k hp
  have htq : t ≤ q := by omega
  refine ⟨q - t, t, ?_⟩
  have hk' : k = p * q + t := by
    simpa [q, t, add_comm, mul_comm] using (Nat.mod_add_div k p).symm
  calc
    k = p * q + t := hk'
    _ = p * ((q - t) + t) + t := by rw [Nat.sub_add_cancel htq]
    _ = p * (q - t) + (p + 1) * t := by ring

private lemma p14_power_bound {E : Type*} [NormedRing E] [NormOneClass E]
    (A : E) (r : ℝ) (a b m n k : ℕ)
    (hr : 0 ≤ r)
    (ha : ‖A ^ a‖ ≤ r ^ a) (hb : ‖A ^ b‖ ≤ r ^ b)
    (hk : k = a * m + b * n) : ‖A ^ k‖ ≤ r ^ k := by
  have ham : ‖A ^ (a * m)‖ ≤ (r ^ a) ^ m := by
    calc
      ‖A ^ (a * m)‖ = ‖(A ^ a) ^ m‖ := by rw [pow_mul]
      _ ≤ ‖A ^ a‖ ^ m := norm_pow_le _ _
      _ ≤ (r ^ a) ^ m := pow_le_pow_left₀ (norm_nonneg _) ha m
  have hbn : ‖A ^ (b * n)‖ ≤ (r ^ b) ^ n := by
    calc
      ‖A ^ (b * n)‖ = ‖(A ^ b) ^ n‖ := by rw [pow_mul]
      _ ≤ ‖A ^ b‖ ^ n := norm_pow_le _ _
      _ ≤ (r ^ b) ^ n := pow_le_pow_left₀ (norm_nonneg _) hb n
  calc
    ‖A ^ k‖ = ‖A ^ (a * m) * A ^ (b * n)‖ := by rw [hk, pow_add]
    _ ≤ ‖A ^ (a * m)‖ * ‖A ^ (b * n)‖ := norm_mul_le _ _
    _ ≤ (r ^ a) ^ m * (r ^ b) ^ n :=
      mul_le_mul ham hbn (norm_nonneg _) (pow_nonneg (pow_nonneg hr a) m)
    _ = r ^ k := by rw [hk, ← pow_mul, ← pow_mul, ← pow_add]

private lemma p14_series_bound {E : Type*} [NormedRing E] [NormOneClass E]
    [NormedAlgebra ℂ E] [CompleteSpace E]
    (c : ℕ → ℂ) (A : E) (r : ℝ)
    (hsum : Summable (fun k : ℕ ↦ ‖c k‖ * r ^ k))
    (hpow : ∀ k : ℕ, c k ≠ 0 → ‖A ^ k‖ ≤ r ^ k) :
    P14SeriesBound c A r := by
  have hterm : ∀ k : ℕ, ‖c k • A ^ k‖ ≤ ‖c k‖ * r ^ k := by
    intro k
    by_cases hc : c k = 0
    · simp [hc]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hpow k hc) (norm_nonneg _)
  have hnorm : Summable (fun k : ℕ ↦ ‖c k • A ^ k‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
  have hs : Summable (fun k : ℕ ↦ c k • A ^ k) := Summable.of_norm hnorm
  refine ⟨hs, ?_⟩
  unfold p14SeriesValue p14AbsoluteSeries
  exact (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum hterm hsum)

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
  · intro r hr hℓ hAp hAp1 hsum
    apply p14_series_bound c A r hsum
    intro k hc
    have hk : ℓ ≤ k := by
      by_contra hn
      exact hc (hcutoff k (Nat.lt_of_not_ge hn))
    obtain ⟨m, n, hdecomp⟩ := p14_decompose p k hp (le_trans hℓ hk)
    exact p14_power_bound A r p (p + 1) m n k hr hAp hAp1 hdecomp
  · intro heven r hr hℓ hA2p hA2p1 hsum
    apply p14_series_bound c A r hsum
    intro k hc
    have hk : ℓ ≤ k := by
      by_contra hn
      exact hc (hcutoff k (Nat.lt_of_not_ge hn))
    have he : Even k := by
      by_contra hn
      exact hc (heven k hn)
    obtain ⟨j, rfl⟩ := even_iff_exists_two_mul.mp he
    have hj : p * (p - 1) ≤ j := by
      have hh := le_trans hℓ hk
      nlinarith
    obtain ⟨m, n, hdecomp⟩ := p14_decompose p j hp hj
    apply p14_power_bound A r (2 * p) (2 * (p + 1)) m n (2 * j) hr hA2p hA2p1
    calc
      2 * j = 2 * (p * m + (p + 1) * n) := by rw [hdecomp]
      _ = (2 * p) * m + (2 * (p + 1)) * n := by ring

end VSCLReuse

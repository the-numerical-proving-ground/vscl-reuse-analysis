import VSCLReuse.P09.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p09_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ s, (a k + b k)) =
      (∏ k ∈ s, a k) +
        ∑ K ∈ s.powerset.erase s,
          (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k := by
  let f : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k
  have hs : s ∈ s.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl s)
  calc
    (∏ k ∈ s, (a k + b k)) = ∑ K ∈ s.powerset, f K := by
      simpa [f] using (Finset.prod_add a b s)
    _ = f s + ∑ K ∈ s.powerset.erase s, f K :=
      (Finset.add_sum_erase s.powerset f hs).symm
    _ = (∏ k ∈ s, a k) +
          ∑ K ∈ s.powerset.erase s,
            (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k := by
      simp [f]

private theorem p09_expansion_remainder_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u)
    (ha : ∀ k, |a k| ≤ u) (hb : ∀ k, |b k| ≤ v) :
    |∑ K ∈ s.powerset.erase s,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
      (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
  have hA (K : Finset ι) :
      |∏ k ∈ K, (1 + a k)| ≤ (1 + u) ^ K.card := by
    rw [Finset.abs_prod, ← Finset.prod_const]
    apply Finset.prod_le_prod
    · intro k hk
      positivity
    · intro k hk
      calc
        |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
        _ ≤ 1 + u := by simpa using add_le_add_left (ha k) 1
  have hB (K : Finset ι) :
      |∏ k ∈ K, b k| ≤ v ^ K.card := by
    rw [Finset.abs_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod (by intros; positivity) (fun k hk => hb k)
  have hterm (K : Finset ι) :
      |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
        (1 + u) ^ K.card * v ^ (s \ K).card := by
    rw [abs_mul]
    exact mul_le_mul (hA K) (hB (s \ K)) (abs_nonneg _) (pow_nonneg (by positivity) _)
  have hsum :
      (∑ K ∈ s.powerset.erase s,
        (1 + u) ^ K.card * v ^ (s.card - K.card)) =
          (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
    have hs : s ∈ s.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl s)
    have hextract := Finset.add_sum_erase s.powerset
      (fun K => (1 + u) ^ K.card * v ^ (s.card - K.card)) hs
    have hfull := Finset.sum_pow_mul_eq_add_pow (1 + u) v s
    simp only [Nat.sub_self, pow_zero, mul_one] at hextract
    linarith
  calc
    |∑ K ∈ s.powerset.erase s,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
      ∑ K ∈ s.powerset.erase s,
        |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K ∈ s.powerset.erase s,
          (1 + u) ^ K.card * v ^ (s.card - K.card) := by
      apply Finset.sum_le_sum
      intro K hK
      have hKs : K ⊆ s := Finset.mem_powerset.mp (Finset.mem_erase.mp hK).2
      simpa [Finset.card_sdiff_of_subset hKs] using hterm K
    _ = (1 + u + v) ^ s.card - (1 + u) ^ s.card := hsum

theorem p09_c1_centered_product_decomposition
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09Lemma310Run n Ω) :
    (∀ k X,
      p09HistoryMeasurable (p09ProductAlpha run) k X →
        p09Expectation run.probability
          (fun ω => X ω * p09ProductAlpha run k ω) = 0) ∧
      (∀ i ω,
        (∏ k ∈ p09SuffixIndexSet i, (1 + run.delta k ω)) =
          (∏ k ∈ p09SuffixIndexSet i,
              (1 + p09ProductAlpha run k ω)) +
            p09Lemma310BiasRemainder run i ω) ∧
      ∀ i ω,
        |p09Lemma310BiasRemainder run i ω| ≤
          p09Gamma (p09SuffixIndexSet i).card
              (run.unitRoundoff + run.biasRoundoff) -
            p09Gamma (p09SuffixIndexSet i).card run.unitRoundoff := by
  -- PROOF_START P09-C1-H001
  constructor
  · intro k X hX
    have h := run.conditional_mean_from_alpha_history k X hX
    unfold p09Expectation at h ⊢
    simp only [p09ProductAlpha, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  constructor
  · intro i ω
    have h := p09_product_expansion (p09SuffixIndexSet i)
      (fun k => 1 + p09ProductAlpha run k ω) (fun k => run.beta k ω)
    convert h using 1
    · congr 1
      ext k
      simp only [p09ProductAlpha]
      ring
  · intro i ω
    unfold p09Lemma310BiasRemainder p09Gamma
    convert p09_expansion_remainder_bound (p09SuffixIndexSet i)
      (fun k => p09ProductAlpha run k ω) (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg
      (fun k => run.alpha_bound k ω) (fun k => run.beta_bound k ω)
      using 1
    ring

end VSCLReuse

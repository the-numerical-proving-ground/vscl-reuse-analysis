import VSCLReuse.P09.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p09_powerset_remainder_bound
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u)
    (ha : ∀ k ∈ I, |a k| ≤ u)
    (hb : ∀ k ∈ I, |b k| ≤ v) :
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
  have hterm (K : Finset ι) (hK : K ∈ I.powerset.erase I) :
      |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
        (1 + u) ^ K.card * v ^ (I.card - K.card) := by
    have hKI : K ⊆ I := Finset.mem_powerset.mp (Finset.mem_erase.mp hK).2
    have hA : |∏ k ∈ K, (1 + a k)| ≤ (1 + u) ^ K.card := by
      rw [Finset.abs_prod, ← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro k hk
        exact abs_nonneg _
      · intro k hk
        calc
          |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left (ha k (hKI hk)) 1
    have hB : |∏ k ∈ I \ K, b k| ≤ v ^ (I.card - K.card) := by
      rw [Finset.abs_prod, ← Finset.card_sdiff_of_subset hKI, ← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro k hk
        exact abs_nonneg _
      · intro k hk
        exact hb k (Finset.mem_sdiff.mp hk).1
    rw [abs_mul]
    exact mul_le_mul hA hB (abs_nonneg _) (pow_nonneg (by positivity) _)
  have hsum :
      (∑ K ∈ I.powerset.erase I,
        (1 + u) ^ K.card * v ^ (I.card - K.card)) =
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
    have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (by rfl)
    have hpow := Finset.sum_pow_mul_eq_add_pow (1 + u) v I
    have herase := Finset.sum_erase_add I.powerset
      (fun K => (1 + u) ^ K.card * v ^ (I.card - K.card)) hI
    simp only [Nat.sub_self, pow_zero, mul_one] at herase
    rw [← herase] at hpow
    linarith
  calc
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
      ∑ K ∈ I.powerset.erase I,
        |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K ∈ I.powerset.erase I,
        (1 + u) ^ K.card * v ^ (I.card - K.card) := by
      exact Finset.sum_le_sum hterm
    _ = _ := hsum

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
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k X hX
    have h := run.conditional_mean_from_alpha_history k X
      (by simpa only [p09ProductAlpha] using hX)
    change p09Expectation run.probability
      (fun ω => X ω * (run.delta k ω - run.beta k ω)) = 0
    simp only [p09Expectation, mul_sub, Finset.sum_sub_distrib] at *
    exact sub_eq_zero.mpr h
  · intro i ω
    let I := p09SuffixIndexSet i
    have hδ (k : Fin n) :
        1 + run.delta k ω =
          (1 + p09ProductAlpha run k ω) + run.beta k ω := by
      unfold p09ProductAlpha
      ring
    have hprod :
        (∏ k ∈ I, (1 + run.delta k ω)) =
          ∑ K ∈ I.powerset,
            (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
              ∏ k ∈ I \ K, run.beta k ω := by
      simp_rw [hδ]
      exact Finset.prod_add _ _ I
    have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (by rfl)
    have herase := Finset.add_sum_erase I.powerset
      (fun K =>
        (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
          ∏ k ∈ I \ K, run.beta k ω) hI
    simp only [Finset.sdiff_self, Finset.prod_empty, mul_one] at herase
    change (∏ k ∈ I, (1 + run.delta k ω)) =
      (∏ k ∈ I, (1 + p09ProductAlpha run k ω)) +
        ∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
            ∏ k ∈ I \ K, run.beta k ω
    rw [hprod]
    exact herase.symm
  · intro i ω
    change |∑ K ∈ (p09SuffixIndexSet i).powerset.erase (p09SuffixIndexSet i),
        (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
          ∏ k ∈ p09SuffixIndexSet i \ K, run.beta k ω| ≤ _
    unfold p09Gamma
    have hbound := p09_powerset_remainder_bound
      (p09SuffixIndexSet i)
      (fun k => p09ProductAlpha run k ω)
      (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg
      (fun k _ => run.alpha_bound k ω)
      (fun k _ => run.beta_bound k ω)
    convert hbound using 1
    ring

end VSCLReuse

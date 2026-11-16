import VSCLReuse.P09.Definitions

namespace VSCLReuse

open scoped BigOperators

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
  constructor
  · intro k X hX
    have h := run.conditional_mean_from_alpha_history k X hX
    unfold p09ProductAlpha
    unfold p09Expectation at h ⊢
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  constructor
  · intro i ω
    let I := p09SuffixIndexSet i
    let a : Fin n → ℝ := fun k => 1 + p09ProductAlpha run k ω
    let b : Fin n → ℝ := fun k => run.beta k ω
    have hprod := Finset.prod_add a b I
    have hsplit :
        (∑ K ∈ I.powerset, (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k) =
          (∏ k ∈ I, a k) +
            ∑ K ∈ I.powerset.erase I,
              (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k := by
      rw [← Finset.add_sum_erase I.powerset
        (fun K => (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k)
        (Finset.mem_powerset.mpr (Finset.Subset.refl I))]
      simp
    convert hprod.trans hsplit using 1
    simp only [I, a, b, p09ProductAlpha]
    congr 1 with k
    ring
  · intro i ω
    let I := p09SuffixIndexSet i
    let u := run.unitRoundoff
    let v := run.biasRoundoff
    let a : Fin n → ℝ := fun k => 1 + p09ProductAlpha run k ω
    let b : Fin n → ℝ := fun k => run.beta k ω
    let major : Finset (Fin n) → ℝ := fun K =>
      (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v
    have hua (k : Fin n) : |a k| ≤ 1 + u := by
      calc
        |a k| ≤ |(1 : ℝ)| + |p09ProductAlpha run k ω| := by
          simpa [a] using abs_add_le (1 : ℝ) (p09ProductAlpha run k ω)
        _ ≤ 1 + u := by
          simpa [u, p09ProductAlpha] using
            add_le_add_left (run.alpha_bound k ω) (1 : ℝ)
    have hvb (k : Fin n) : |b k| ≤ v := by
      simpa [b, v] using run.beta_bound k ω
    have hterm (K : Finset (Fin n)) :
        |(∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k| ≤ major K := by
      have hA : (∏ k ∈ K, |a k|) ≤ ∏ k ∈ K, (1 + u) := by
        apply Finset.prod_le_prod
        · intro k hk; exact abs_nonneg _
        · intro k hk; exact hua k
      have hB : (∏ k ∈ I \ K, |b k|) ≤ ∏ k ∈ I \ K, v := by
        apply Finset.prod_le_prod
        · intro k hk; exact abs_nonneg _
        · intro k hk; exact hvb k
      have hnonneg : 0 ≤ ∏ k ∈ I \ K, |b k| := by
        apply Finset.prod_nonneg
        intro k hk; exact abs_nonneg _
      have hnonneg' : 0 ≤ ∏ k ∈ K, (1 + u) := by
        apply Finset.prod_nonneg
        intro k hk
        exact add_nonneg (by norm_num) run.unitRoundoff_nonneg
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      exact mul_le_mul hA hB hnonneg hnonneg'
    have hbound :
        |p09Lemma310BiasRemainder run i ω| ≤
          ∑ K ∈ I.powerset.erase I, major K := by
      change |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k| ≤ _
      calc
        _ ≤ ∑ K ∈ I.powerset.erase I,
            |(∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ K ∈ I.powerset.erase I, major K := by
          apply Finset.sum_le_sum
          intro K hK
          exact hterm K
    have hmajor :
        (∑ K ∈ I.powerset.erase I, major K) =
          (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
      have hprod := Finset.prod_add
        (fun _ : Fin n => (1 + u)) (fun _ : Fin n => v) I
      have hsplit := Finset.add_sum_erase I.powerset major
        (Finset.mem_powerset.mpr (Finset.Subset.refl I))
      simp only [Finset.prod_const] at hprod
      dsimp [major] at hsplit
      simp only [Finset.prod_const, Finset.sdiff_self] at hsplit
      rw [← hsplit] at hprod
      simp only [Finset.card_empty, pow_zero, mul_one] at hprod
      simp only [major, Finset.prod_const]
      linarith
    calc
      |p09Lemma310BiasRemainder run i ω| ≤
          ∑ K ∈ I.powerset.erase I, major K := hbound
      _ = (1 + u + v) ^ I.card - (1 + u) ^ I.card := hmajor
      _ = p09Gamma I.card (u + v) - p09Gamma I.card u := by
        unfold p09Gamma
        ring

end VSCLReuse

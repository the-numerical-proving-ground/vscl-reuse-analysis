import VSCLReuse.P09.Definitions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace VSCLReuse

open scoped BigOperators

private theorem p09_powerset_remainder_bound
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (a b : ι → ℝ)
    (u v : ℝ) (hu : 0 ≤ u)
    (ha : ∀ k ∈ I, |a k| ≤ u) (hb : ∀ k ∈ I, |b k| ≤ v) :
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
  classical
  have hterm (K : Finset ι) (hK : K ∈ I.powerset.erase I) :
      |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
        (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v := by
    have hKI : K ⊆ I := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hK)
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    have hA : (∏ k ∈ K, |1 + a k|) ≤ ∏ k ∈ K, (1 + u) := by
      apply Finset.prod_le_prod
      · intro k hk; positivity
      · intro k hk
        calc |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left (ha k (hKI hk)) 1
    have hB : (∏ k ∈ I \ K, |b k|) ≤ ∏ k ∈ I \ K, v := by
      apply Finset.prod_le_prod
      · intro k hk; positivity
      · intro k hk; exact hb k (Finset.sdiff_subset hk)
    exact mul_le_mul hA hB (by positivity) (by positivity)
  have hsum :
      (∑ K ∈ I.powerset.erase I,
        |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k|) ≤
      ∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v := by
    apply Finset.sum_le_sum
    intro K hK
    exact hterm K hK
  have hpow :
      (1 + u + v) ^ I.card =
        ∑ K ∈ I.powerset,
          (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v := by
    simpa only [Finset.prod_const] using
      (Finset.prod_add (fun _ : ι => (1 + u)) (fun _ => v) I)
  have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl I)
  have hsplit := Finset.add_sum_erase I.powerset
    (fun K => (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v) hI
  have hfull :
      (∏ k ∈ I, (1 + u)) * ∏ k ∈ I \ I, v = (1 + u) ^ I.card := by
    simp
  have hrest :
      (∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v) =
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
    dsimp only at hsplit
    rw [hfull, ← hpow] at hsplit
    linarith
  calc
    _ ≤ ∑ K ∈ I.powerset.erase I,
        |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by simpa only [hrest] using hsum

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
    unfold p09Expectation at h ⊢
    simp only [p09ProductAlpha, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  constructor
  · intro i ω
    let I := p09SuffixIndexSet i
    have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl I)
    have hprod := Finset.prod_add
      (fun k => 1 + p09ProductAlpha run k ω)
      (fun k => run.beta k ω) I
    have hsum := Finset.add_sum_erase I.powerset
      (fun K => (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
        ∏ k ∈ I \ K, run.beta k ω) hI
    have hfull :
        (∏ k ∈ I, (1 + p09ProductAlpha run k ω)) *
          (∏ k ∈ I \ I, run.beta k ω) =
        ∏ k ∈ I, (1 + p09ProductAlpha run k ω) := by simp
    calc
      (∏ k ∈ I, (1 + run.delta k ω)) =
          ∏ k ∈ I, ((1 + p09ProductAlpha run k ω) + run.beta k ω) := by
            congr 1
            ext k
            simp [p09ProductAlpha]
            ring
      _ = (∏ k ∈ I, (1 + p09ProductAlpha run k ω)) +
          p09Lemma310BiasRemainder run i ω := by
            rw [hprod]
            simpa only [hfull, p09Lemma310BiasRemainder, I] using hsum.symm
  · intro i ω
    let I := p09SuffixIndexSet i
    have hb := p09_powerset_remainder_bound I
      (fun k => p09ProductAlpha run k ω) (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg
      (by intro k hk; exact run.alpha_bound k ω)
      (by intro k hk; exact run.beta_bound k ω)
    unfold p09Lemma310BiasRemainder p09Gamma
    dsimp only
    convert hb using 1
    ring

end VSCLReuse


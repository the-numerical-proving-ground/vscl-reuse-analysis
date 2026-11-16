import VSCLReuse.P09.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p09_product_split {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ s, (a k + b k)) =
      (∏ k ∈ s, a k) +
        ∑ K ∈ s.powerset.erase s,
          (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k := by
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (by simp : s ∈ s.powerset)]
  simp

private theorem p09_product_remainder_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u)
    (ha : ∀ k ∈ s, |a k| ≤ 1 + u)
    (hb : ∀ k ∈ s, |b k| ≤ v) :
    |∑ K ∈ s.powerset.erase s,
        (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k| ≤
      (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
  let term : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k
  let major : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, (1 + u)) * ∏ k ∈ s \ K, v
  have hterm : ∀ K ∈ s.powerset.erase s, |term K| ≤ major K := by
    intro K hK
    have hKs : K ⊆ s := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hK)
    dsimp [term, major]
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    apply mul_le_mul
    · exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k hk => ha k (hKs hk))
    · exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k hk => hb k (Finset.mem_sdiff.mp hk).1)
    · exact Finset.prod_nonneg (fun k hk => abs_nonneg _)
    · exact Finset.prod_nonneg (fun k hk => by positivity)
  have hsum : |∑ K ∈ s.powerset.erase s, term K| ≤
      ∑ K ∈ s.powerset.erase s, major K := by
    calc
      _ ≤ ∑ K ∈ s.powerset.erase s, |term K| :=
        Finset.abs_sum_le_sum_abs term (s.powerset.erase s)
      _ ≤ ∑ K ∈ s.powerset.erase s, major K :=
        Finset.sum_le_sum hterm
  have hmajor : (∑ K ∈ s.powerset.erase s, major K) =
      (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
    have h := Finset.prod_add (fun _ : ι => 1 + u) (fun _ => v) s
    rw [← Finset.add_sum_erase _ _ (by simp : s ∈ s.powerset)] at h
    simp only [Finset.sdiff_self, Finset.prod_empty, mul_one] at h
    change (∏ k ∈ s, (1 + u + v)) =
      (∏ k ∈ s, (1 + u)) + ∑ K ∈ s.powerset.erase s, major K at h
    rw [Finset.prod_const, Finset.prod_const] at h
    linarith
  exact hsum.trans_eq hmajor

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
    have h := run.conditional_mean_from_alpha_history k X
      (by simpa [p09ProductAlpha] using hX)
    change (∑ ω, run.probability.prob ω *
      (X ω * (run.delta k ω - run.beta k ω))) = 0
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  constructor
  · intro i ω
    have h := p09_product_split (p09SuffixIndexSet i)
      (fun k => 1 + p09ProductAlpha run k ω)
      (fun k => run.beta k ω)
    simpa [p09Lemma310BiasRemainder, p09ProductAlpha, add_assoc, sub_add_cancel]
      using h
  · intro i ω
    have h := p09_product_remainder_bound
      (p09SuffixIndexSet i)
      (fun k => 1 + p09ProductAlpha run k ω)
      (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg
      (by
        intro k hk
        calc
          |1 + p09ProductAlpha run k ω| ≤ |(1 : ℝ)| + |p09ProductAlpha run k ω| :=
            abs_add_le _ _
          _ ≤ 1 + run.unitRoundoff := by
            simpa [p09ProductAlpha] using
              add_le_add_left (run.alpha_bound k ω) 1)
      (by intro k hk; exact run.beta_bound k ω)
    simpa [p09Lemma310BiasRemainder, p09Gamma, add_assoc] using h

end VSCLReuse

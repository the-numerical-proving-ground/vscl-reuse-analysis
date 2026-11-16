import VSCLReuse.P09.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p09_product_sum_erase
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ s, (a k + b k)) =
      (∏ k ∈ s, a k) +
        ∑ K ∈ s.powerset.erase s,
          (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k := by
  rw [Finset.prod_add]
  have h := Finset.sum_erase_add s.powerset
    (fun K => (∏ k ∈ K, a k) * ∏ k ∈ s \ K, b k)
    (Finset.mem_powerset_self s)
  simpa [add_comm] using h.symm

private theorem p09_product_remainder_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u)
    (ha : ∀ k ∈ s, |a k| ≤ u)
    (hb : ∀ k ∈ s, |b k| ≤ v) :
    |∑ K ∈ s.powerset.erase s,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
      (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
  have hterm (K : Finset ι) (hK : K ∈ s.powerset.erase s) :
      |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
        (1 + u) ^ K.card * v ^ (s.card - K.card) := by
    have hsub : K ⊆ s := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hK)
    have hfirst : (∏ k ∈ K, |1 + a k|) ≤ (1 + u) ^ K.card := by
      calc
        (∏ k ∈ K, |1 + a k|) ≤ ∏ k ∈ K, (1 + u) := by
          apply Finset.prod_le_prod
          · intro k hk
            positivity
          · intro k hk
            calc
              |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
              _ ≤ 1 + u := by simpa using add_le_add_left (ha k (hsub hk)) 1
        _ = (1 + u) ^ K.card := by simp
    have hsecond : (∏ k ∈ s \ K, |b k|) ≤ v ^ (s.card - K.card) := by
      calc
        (∏ k ∈ s \ K, |b k|) ≤ ∏ k ∈ s \ K, v := by
          apply Finset.prod_le_prod
          · intro k hk
            positivity
          · intro k hk
            exact hb k (Finset.mem_sdiff.mp hk).1
        _ = v ^ (s.card - K.card) := by
          rw [Finset.prod_const, Finset.card_sdiff_of_subset hsub]
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hsum :
      (∑ K ∈ s.powerset.erase s,
        (1 + u) ^ K.card * v ^ (s.card - K.card)) =
        (1 + u + v) ^ s.card - (1 + u) ^ s.card := by
    have h := Finset.sum_erase_add s.powerset
      (fun K => (1 + u) ^ K.card * v ^ (s.card - K.card))
      (Finset.mem_powerset_self s)
    rw [Finset.sum_pow_mul_eq_add_pow] at h
    simp only [Nat.sub_self, pow_zero, mul_one] at h
    linarith
  calc
    |∑ K ∈ s.powerset.erase s,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| ≤
      ∑ K ∈ s.powerset.erase s,
        |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ s \ K, b k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K ∈ s.powerset.erase s,
        (1 + u) ^ K.card * v ^ (s.card - K.card) :=
          Finset.sum_le_sum hterm
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
  constructor
  · intro k X hX
    have h := run.conditional_mean_from_alpha_history k X hX
    have hdiff :
        p09Expectation run.probability
            (fun ω => X ω * p09ProductAlpha run k ω) =
          p09Expectation run.probability (fun ω => X ω * run.delta k ω) -
            p09Expectation run.probability (fun ω => X ω * run.beta k ω) := by
      simp [p09Expectation, p09ProductAlpha, mul_sub, Finset.sum_sub_distrib]
    rw [hdiff, h, sub_self]
  constructor
  · intro i ω
    have h := p09_product_sum_erase (p09SuffixIndexSet i)
      (fun k => 1 + p09ProductAlpha run k ω) (fun k => run.beta k ω)
    simpa [p09ProductAlpha, p09Lemma310BiasRemainder, add_assoc] using h
  · intro i ω
    have h := p09_product_remainder_bound (p09SuffixIndexSet i)
      (fun k => p09ProductAlpha run k ω) (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg
      (fun k hk => run.alpha_bound k ω)
      (fun k hk => run.beta_bound k ω)
    simpa [p09Lemma310BiasRemainder, p09Gamma, add_assoc] using h

end VSCLReuse

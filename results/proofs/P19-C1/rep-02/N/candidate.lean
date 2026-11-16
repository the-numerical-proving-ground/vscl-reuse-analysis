import VSCLReuse.P19.Definitions

namespace VSCLReuse

private theorem p19_component_bound
    {n t : ℕ} (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n)
    (ha : P19Admissible g f dp db) (i : Fin n) :
    |p19LinearResponse K H dp db i| ≤ p19ConditionRadius K H g f i := by
  rcases ha with ⟨hpa, hba⟩
  change |(∑ j, H i j * db j) - (∑ j, K i j * dp j)| ≤
    (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j
  calc
    |(∑ j, H i j * db j) - (∑ j, K i j * dp j)|
        ≤ |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| := by
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hba j) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpa j) (abs_nonneg _)
    _ = (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j := by ac_rfl

private theorem p19_attain_component
    {n t : ℕ} (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    ∃ dp db, P19Admissible g f dp db ∧
      p19LinearResponse K H dp db i = p19ConditionRadius K H g f i := by
  let dp : P19Vector t := fun j => if 0 ≤ K i j then -g j else g j
  let db : P19Vector n := fun j => if 0 ≤ H i j then f j else -f j
  have hadm : P19Admissible g f dp db := by
    constructor
    · intro j
      dsimp [dp]
      split_ifs <;> simp [abs_of_nonneg (hg j)]
    · intro j
      dsimp [db]
      split_ifs <;> simp [abs_of_nonneg (hf j)]
  have hK : ∀ j, K i j * dp j = -(|K i j| * g j) := by
    intro j
    by_cases h : 0 ≤ K i j
    · simp [dp, h, abs_of_nonneg h]
    · have hn : K i j < 0 := lt_of_not_ge h
      simp [dp, h, abs_of_neg hn]
  have hH : ∀ j, H i j * db j = |H i j| * f j := by
    intro j
    by_cases h : 0 ≤ H i j
    · simp [db, h, abs_of_nonneg h]
    · have hn : H i j < 0 := lt_of_not_ge h
      simp [db, h, abs_of_neg hn]
  refine ⟨dp, db, hadm, ?_⟩
  change (∑ j, H i j * db j) - (∑ j, K i j * dp j) =
    (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j
  simp_rw [hH, hK]
  rw [Finset.sum_neg_distrib]
  ring

/-- P19-C1: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p19_c1_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p19LinearizedCondition K H g f xNorm =
      p19ConditionFormula K H g f xNorm := by
  -- PROOF_START P19-C1-H001
  let R := p19ConditionRadius K H g f
  let V := p19LinearizedValues K H g f xNorm
  have hRnonneg : ∀ i, 0 ≤ R i := by
    intro i
    change 0 ≤ (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (abs_nonneg _) (hg j)
    · apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (abs_nonneg _) (hf j)
  have hupper : ∀ dp db, P19Admissible g f dp db →
      ‖p19LinearResponse K H dp db‖ ≤ ‖R‖ := by
    intro dp db ha
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
    intro i
    rw [Real.norm_eq_abs]
    calc
      |p19LinearResponse K H dp db i| ≤ R i := p19_component_bound K H g f dp db ha i
      _ = ‖R i‖ := (Real.norm_eq_abs _).trans (abs_of_nonneg (hRnonneg i)) |>.symm
      _ ≤ ‖R‖ := norm_le_pi_norm R i
  have hVnonempty : V.Nonempty := by
    refine ⟨‖p19LinearResponse K H 0 0‖ / xNorm, ?_⟩
    change ∃ dp db, P19Admissible g f dp db ∧
      ‖p19LinearResponse K H 0 0‖ / xNorm =
        ‖p19LinearResponse K H dp db‖ / xNorm
    refine ⟨0, 0, ?_, rfl⟩
    constructor
    · intro j
      simpa using hg j
    · intro i
      simpa using hf i
  have hVbounded : BddAbove V := by
    refine ⟨‖R‖ / xNorm, ?_⟩
    intro q hq
    change ∃ dp db, P19Admissible g f dp db ∧
      q = ‖p19LinearResponse K H dp db‖ / xNorm at hq
    rcases hq with ⟨dp, db, ha, rfl⟩
    exact div_le_div_of_nonneg_right (hupper dp db ha) hx.le
  have hsup_nonneg : 0 ≤ sSup V := by
    rcases hVnonempty with ⟨q, hq⟩
    have hq_nonneg : 0 ≤ q := by
      change ∃ dp db, P19Admissible g f dp db ∧
        q = ‖p19LinearResponse K H dp db‖ / xNorm at hq
      rcases hq with ⟨dp, db, _, rfl⟩
      positivity
    exact hq_nonneg.trans (le_csSup hVbounded hq)
  change sSup V = ‖R‖ / xNorm
  apply le_antisymm
  · apply csSup_le hVnonempty
    intro q hq
    change ∃ dp db, P19Admissible g f dp db ∧
      q = ‖p19LinearResponse K H dp db‖ / xNorm at hq
    rcases hq with ⟨dp, db, ha, rfl⟩
    exact div_le_div_of_nonneg_right (hupper dp db ha) hx.le
  · apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    obtain ⟨dp, db, ha, heq⟩ := p19_attain_component K H g f hg hf i
    have hq : ‖p19LinearResponse K H dp db‖ / xNorm ∈ V := by
      exact ⟨dp, db, ha, rfl⟩
    have hcoord : ‖R i‖ ≤ ‖p19LinearResponse K H dp db‖ := by
      change ‖p19ConditionRadius K H g f i‖ ≤ ‖p19LinearResponse K H dp db‖
      rw [← heq]
      exact norm_le_pi_norm (p19LinearResponse K H dp db) i
    have hdiv : ‖R i‖ / xNorm ≤ sSup V :=
      (div_le_div_of_nonneg_right hcoord hx.le).trans (le_csSup hVbounded hq)
    exact (div_le_iff₀ hx).1 hdiv

end VSCLReuse

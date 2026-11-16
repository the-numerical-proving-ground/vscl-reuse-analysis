import VSCLReuse.P19.Definitions

namespace VSCLReuse

private lemma p19_radius_nonneg
    {n t : ℕ} (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ p19ConditionRadius K H g f i := by
  simp only [p19ConditionRadius]
  exact add_nonneg
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j))
    (Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j))

private lemma p19_response_abs_le_radius
    {n t : ℕ} (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n)
    (ha : P19Admissible g f dp db) (i : Fin n) :
    |p19LinearResponse K H dp db i| ≤ p19ConditionRadius K H g f i := by
  rcases ha with ⟨hdp, hdb⟩
  simp only [p19LinearResponse, p19ConditionRadius]
  calc
    |(∑ j, H i j * db j) - (∑ j, K i j * dp j)| ≤
        |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + (∑ j, |K i j * dp j|) := by
      exact add_le_add
        (Finset.abs_sum_le_sum_abs (fun j ↦ H i j * db j) Finset.univ)
        (Finset.abs_sum_le_sum_abs (fun j ↦ K i j * dp j) Finset.univ)
    _ ≤ (∑ j, |H i j| * f j) + (∑ j, |K i j| * g j) := by
      simp only [abs_mul]
      exact add_le_add
        (Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hdb j) (abs_nonneg _))
        (Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hdp j) (abs_nonneg _))
    _ = (∑ j, |K i j| * g j) + (∑ j, |H i j| * f j) := add_comm _ _

private lemma p19_attains_radius_coord
    {n t : ℕ} (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    ∃ dp db, P19Admissible g f dp db ∧
      p19LinearResponse K H dp db i = p19ConditionRadius K H g f i := by
  let dp : P19Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
  let db : P19Vector n := fun j ↦ if 0 ≤ H i j then f j else -f j
  have hdp (j : Fin t) : |dp j| ≤ g j := by
    dsimp [dp]
    split_ifs <;> simp [abs_of_nonneg (hg j)]
  have hdb (j : Fin n) : |db j| ≤ f j := by
    dsimp [db]
    split_ifs <;> simp [abs_of_nonneg (hf j)]
  have hk (j : Fin t) : K i j * dp j = -(|K i j| * g j) := by
    dsimp [dp]
    split_ifs with h
    · rw [abs_of_nonneg h]
      ring
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  have hh (j : Fin n) : H i j * db j = |H i j| * f j := by
    dsimp [db]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨dp, db, ⟨hdp, hdb⟩, ?_⟩
  simp only [p19LinearResponse, p19ConditionRadius]
  simp_rw [hh, hk]
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
  let S := p19LinearizedValues K H g f xNorm
  let R := p19ConditionRadius K H g f
  have hnorm_bound (dp : P19Vector t) (db : P19Vector n)
      (ha : P19Admissible g f dp db) :
      ‖p19LinearResponse K H dp db‖ ≤ ‖R‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
    intro i
    rw [Real.norm_eq_abs]
    have hr : 0 ≤ R i := p19_radius_nonneg K H g f hg hf i
    exact (p19_response_abs_le_radius K H g f dp db ha i).trans
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using norm_le_pi_norm R i)
  have hvalue_bound : ∀ q ∈ S, q ≤ ‖R‖ / xNorm := by
    intro q hq
    obtain ⟨dp, db, ha, rfl⟩ := hq
    exact div_le_div_of_nonneg_right (hnorm_bound dp db ha) hx.le
  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨0, 0, ?_, ?_⟩
    · exact ⟨fun j ↦ by simpa using hg j, fun i ↦ by simpa using hf i⟩
    · have hz : p19LinearResponse K H (0 : P19Vector t) (0 : P19Vector n) = 0 := by
        funext i
        simp [p19LinearResponse]
      simp [hz]
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hbdd : BddAbove S := ⟨‖R‖ / xNorm, hvalue_bound⟩
  have hupper : sSup S ≤ ‖R‖ / xNorm := csSup_le hnonempty hvalue_bound
  have hsup_nonneg : 0 ≤ sSup S := (le_csSup hbdd hzero)
  have hlower : ‖R‖ / xNorm ≤ sSup S := by
    apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    obtain ⟨dp, db, ha, heq⟩ := p19_attains_radius_coord K H g f hg hf i
    have hmem : ‖p19LinearResponse K H dp db‖ / xNorm ∈ S :=
      ⟨dp, db, ha, rfl⟩
    have hcoord : ‖R i‖ ≤ ‖p19LinearResponse K H dp db‖ := by
      have h := norm_le_pi_norm (p19LinearResponse K H dp db) i
      rw [heq] at h
      exact h
    exact (div_le_iff₀ hx).1
      ((div_le_div_of_nonneg_right hcoord hx.le).trans (le_csSup hbdd hmem))
  exact le_antisymm hupper hlower

end VSCLReuse

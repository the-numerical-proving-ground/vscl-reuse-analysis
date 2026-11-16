import VSCLReuse.P19.Definitions

namespace VSCLReuse

/-- P19-C1: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p19_c1_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p19LinearizedCondition K H g f xNorm =
      p19ConditionFormula K H g f xNorm := by
  -- PROOF_START P19-C1-H001
  let V := p19LinearizedValues K H g f xNorm
  let r := p19ConditionRadius K H g f
  have hr_nonneg (i : Fin n) : 0 ≤ r i := by
    dsimp [r, p19ConditionRadius]
    apply add_nonneg
    · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hg j)
    · exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (hf j)
  have hbound (dp : P19Vector t) (db : P19Vector n)
      (had : P19Admissible g f dp db) :
      ‖p19LinearResponse K H dp db‖ ≤ ‖r‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg r)).2
    intro i
    rw [Real.norm_eq_abs]
    have hH : |∑ j, H i j * db j| ≤ ∑ j, |H i j| * f j := by
      calc
        |∑ j, H i j * db j| ≤ ∑ j, |H i j * db j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |H i j| * f j := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (had.2 j) (abs_nonneg _)
    have hK : |∑ j, K i j * dp j| ≤ ∑ j, |K i j| * g j := by
      calc
        |∑ j, K i j * dp j| ≤ ∑ j, |K i j * dp j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |K i j| * g j := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (had.1 j) (abs_nonneg _)
    calc
      |p19LinearResponse K H dp db i| ≤
          |∑ j, H i j * db j| + |∑ j, K i j * dp j| := by
            exact abs_sub _ _
      _ ≤ (∑ j, |H i j| * f j) + (∑ j, |K i j| * g j) := add_le_add hH hK
      _ = r i := by dsimp [r, p19ConditionRadius]; ring
      _ = ‖r i‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hr_nonneg i)]
      _ ≤ ‖r‖ := norm_le_pi_norm _ i
  have hV_zero : (0 : ℝ) ∈ V := by
    change ∃ dp db, P19Admissible g f dp db ∧
      (0 : ℝ) = ‖p19LinearResponse K H dp db‖ / xNorm
    refine ⟨0, 0, ?_, ?_⟩
    · exact ⟨by simpa using hg, by simpa using hf⟩
    · have hz : p19LinearResponse K H (0 : P19Vector t) (0 : P19Vector n) = 0 := by
        ext i
        simp [p19LinearResponse]
      rw [hz]
      simp
  have hV_nonempty : V.Nonempty := ⟨0, hV_zero⟩
  have hV_bdd : BddAbove V := by
    refine ⟨‖r‖ / xNorm, ?_⟩
    intro q hq
    obtain ⟨dp, db, had, rfl⟩ := hq
    exact div_le_div_of_nonneg_right (hbound dp db had) hx.le
  have hsup_upper : sSup V ≤ ‖r‖ / xNorm :=
    csSup_le hV_nonempty fun q hq ↦ by
      obtain ⟨dp, db, had, rfl⟩ := hq
      exact div_le_div_of_nonneg_right (hbound dp db had) hx.le
  have hsup_nonneg : 0 ≤ sSup V := le_csSup hV_bdd hV_zero
  have hsup_lower : ‖r‖ / xNorm ≤ sSup V := by
    apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hr_nonneg i)]
    let dp : P19Vector t := fun j ↦ if 0 ≤ K i j then -g j else g j
    let db : P19Vector n := fun j ↦ if 0 ≤ H i j then f j else -f j
    have had : P19Admissible g f dp db := by
      constructor
      · intro j
        dsimp [dp]
        split_ifs <;> simp [abs_of_nonneg (hg j)]
      · intro j
        dsimp [db]
        split_ifs <;> simp [abs_of_nonneg (hf j)]
    have hdb (j : Fin n) : H i j * db j = |H i j| * f j := by
      dsimp [db]
      split_ifs with h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]
        ring
    have hdp (j : Fin t) : K i j * dp j = -(|K i j| * g j) := by
      dsimp [dp]
      split_ifs with h
      · rw [abs_of_nonneg h]
        ring
      · rw [abs_of_neg (lt_of_not_ge h)]
        ring
    have hresp : p19LinearResponse K H dp db i = r i := by
      simp only [p19LinearResponse, hdb, hdp]
      dsimp [r, p19ConditionRadius]
      rw [Finset.sum_neg_distrib]
      ring
    have hrow : r i ≤ ‖p19LinearResponse K H dp db‖ := by
      calc
        r i = ‖p19LinearResponse K H dp db i‖ := by
          rw [Real.norm_eq_abs, hresp, abs_of_nonneg (hr_nonneg i)]
        _ ≤ ‖p19LinearResponse K H dp db‖ := norm_le_pi_norm _ i
    have hmem : ‖p19LinearResponse K H dp db‖ / xNorm ∈ V := by
      exact ⟨dp, db, had, rfl⟩
    have hle := le_csSup hV_bdd hmem
    have hdiv : r i / xNorm ≤ sSup V :=
      (div_le_div_of_nonneg_right hrow hx.le).trans hle
    exact (div_le_iff₀ hx).1 hdiv
  exact le_antisymm hsup_upper hsup_lower

end VSCLReuse

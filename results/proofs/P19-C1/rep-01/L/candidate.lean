import VSCLReuse.P19.Definitions
import NumStability.Analysis.Summation.Signs

namespace VSCLReuse

private lemma p19_radius_nonneg {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ p19ConditionRadius K H g f i := by
  unfold p19ConditionRadius
  apply add_nonneg
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hg j))
  · exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hf j))

private lemma p19_response_le_radius {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n)
    (hadm : P19Admissible g f dp db) (i : Fin n) :
    |p19LinearResponse K H dp db i| ≤ p19ConditionRadius K H g f i := by
  rcases hadm with ⟨hgp, hfb⟩
  unfold p19LinearResponse p19ConditionRadius
  calc
    |(∑ j, H i j * db j) - ∑ j, K i j * dp j| ≤
        |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
    _ ≤ (∑ j, |H i j * db j|) + ∑ j, |K i j * dp j| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ j, |H i j| * f j) + ∑ j, |K i j| * g j := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hfb j) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hgp j) (abs_nonneg _)
    _ = (∑ j, |K i j| * g j) + ∑ j, |H i j| * f j := add_comm _ _

private lemma p19_radius_attained_at {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    ∃ dp db, P19Admissible g f dp db ∧
      p19LinearResponse K H dp db i = p19ConditionRadius K H g f i := by
  let dp : P19Vector t := fun j => -(NumStability.summationAbsSign (K i j) * g j)
  let db : P19Vector n := fun j => NumStability.summationAbsSign (H i j) * f j
  refine ⟨dp, db, ?_, ?_⟩
  · constructor
    · intro j
      simp [dp, abs_mul, NumStability.abs_summationAbsSign, abs_of_nonneg (hg j)]
    · intro j
      simp [db, abs_mul, NumStability.abs_summationAbsSign, abs_of_nonneg (hf j)]
  · have hH : (∑ j, H i j * db j) = ∑ j, |H i j| * f j := by
      apply Finset.sum_congr rfl
      intro j _
      change H i j * (NumStability.summationAbsSign (H i j) * f j) = _
      rw [← mul_assoc, NumStability.mul_summationAbsSign_eq_abs]
    have hK : (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
      change (∑ j, K i j * (-(NumStability.summationAbsSign (K i j) * g j))) = _
      simp_rw [mul_neg, ← mul_assoc, NumStability.mul_summationAbsSign_eq_abs]
      rw [Finset.sum_neg_distrib]
    simp [p19LinearResponse, p19ConditionRadius, hH, hK, add_comm]

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
  let C := p19ConditionFormula K H g f xNorm
  have hzero : 0 ∈ S := by
    refine ⟨0, 0, ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        simpa using hf i
    · have hz : p19LinearResponse K H 0 0 = 0 := by
        ext i
        simp [p19LinearResponse]
      simp [hz]
  have hbound : ∀ q ∈ S, q ≤ C := by
    intro q hq
    obtain ⟨dp, db, hadm, rfl⟩ := hq
    have hnorm : ‖p19LinearResponse K H dp db‖ ≤ ‖R‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg R)).2
      intro i
      rw [Real.norm_eq_abs]
      exact (p19_response_le_radius K H g f dp db hadm i).trans
        (by simpa [R, Real.norm_eq_abs,
          abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)] using
          (norm_le_pi_norm R i))
    exact (div_le_div_of_nonneg_right hnorm hx.le)
  have hbdd : BddAbove S := ⟨C, hbound⟩
  have hupper : sSup S ≤ C := csSup_le ⟨0, hzero⟩ hbound
  have hlower : C ≤ sSup S := by
    have hsup_nonneg : 0 ≤ sSup S := le_csSup hbdd hzero
    have hRle : ‖R‖ ≤ sSup S * xNorm := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
      intro i
      have ⟨dp, db, hadm, heq⟩ := p19_radius_attained_at K H g f hg hf i
      have hmem : ‖p19LinearResponse K H dp db‖ / xNorm ∈ S :=
        ⟨dp, db, hadm, rfl⟩
      have hcoord : R i ≤ ‖p19LinearResponse K H dp db‖ := by
        have hi := norm_le_pi_norm (p19LinearResponse K H dp db) i
        simpa [R, heq, Real.norm_eq_abs,
          abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)] using hi
      have hquot : R i / xNorm ≤ sSup S :=
        (div_le_div_of_nonneg_right hcoord hx.le).trans (le_csSup hbdd hmem)
      rw [Real.norm_eq_abs, abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)]
      exact (div_le_iff₀ hx).mp hquot
    exact (div_le_iff₀ hx).2 (by simpa [C, p19ConditionFormula, R] using hRle)
  exact le_antisymm hupper hlower

end VSCLReuse

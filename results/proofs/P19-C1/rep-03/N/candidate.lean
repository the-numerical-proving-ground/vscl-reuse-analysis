import VSCLReuse.P19.Definitions

namespace VSCLReuse

private lemma p19_abs_sum_mul_le {m : ℕ}
    (a d r : Fin m → ℝ) (hd : ∀ j, |d j| ≤ r j) :
    |∑ j, a j * d j| ≤ ∑ j, |a j| * r j := by
  calc
    |∑ j, a j * d j| ≤ ∑ j, |a j * d j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |d j| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |a j| * r j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hd j) (abs_nonneg _)

private noncomputable def p19Choice (a r : ℝ) : ℝ := if 0 ≤ a then r else -r

private lemma p19Choice_abs_le (a r : ℝ) (hr : 0 ≤ r) :
    |p19Choice a r| ≤ r := by
  unfold p19Choice
  split_ifs <;> simp [abs_of_nonneg hr]

private lemma p19Choice_mul (a r : ℝ) :
    a * p19Choice a r = |a| * r := by
  unfold p19Choice
  split_ifs with h
  · rw [abs_of_nonneg h]
  · have hn : a < 0 := lt_of_not_ge h
    rw [abs_of_neg hn]
    ring

private lemma p19_radius_nonneg {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ p19ConditionRadius K H g f i := by
  unfold p19ConditionRadius
  apply add_nonneg
  · exact Finset.sum_nonneg (fun j hj ↦ mul_nonneg (abs_nonneg _) (hg j))
  · exact Finset.sum_nonneg (fun j hj ↦ mul_nonneg (abs_nonneg _) (hf j))

private lemma p19_response_le_radius {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i)
    (hadm : P19Admissible g f dp db) :
    ‖p19LinearResponse K H dp db‖ ≤ ‖p19ConditionRadius K H g f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  have hi : |p19LinearResponse K H dp db i| ≤ p19ConditionRadius K H g f i := by
    change |(∑ j, H i j * db j) - (∑ j, K i j * dp j)| ≤
      (∑ j, |K i j| * g j) + (∑ j, |H i j| * f j)
    calc
      |(∑ j, H i j * db j) - (∑ j, K i j * dp j)|
          ≤ |∑ j, H i j * db j| + |∑ j, K i j * dp j| := abs_sub _ _
      _ ≤ (∑ j, |H i j| * f j) + (∑ j, |K i j| * g j) := by
        apply add_le_add
        · exact p19_abs_sum_mul_le _ _ _ hadm.2
        · exact p19_abs_sum_mul_le _ _ _ hadm.1
      _ = (∑ j, |K i j| * g j) + (∑ j, |H i j| * f j) := add_comm _ _
  have hcoord := norm_le_pi_norm (p19ConditionRadius K H g f) i
  rw [Real.norm_eq_abs, abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)] at hcoord
  exact hi.trans hcoord

private lemma p19_coordinate_attained {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    ∃ dp db, P19Admissible g f dp db ∧
      p19LinearResponse K H dp db i = p19ConditionRadius K H g f i := by
  let dp : P19Vector t := fun j ↦ -p19Choice (K i j) (g j)
  let db : P19Vector n := fun j ↦ p19Choice (H i j) (f j)
  refine ⟨dp, db, ?_, ?_⟩
  · constructor
    · intro j
      simpa only [dp, abs_neg] using p19Choice_abs_le (K i j) (g j) (hg j)
    · intro j
      exact p19Choice_abs_le (H i j) (f j) (hf j)
  · have hH : (∑ j, H i j * db j) = ∑ j, |H i j| * f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact p19Choice_mul _ _
    have hK : (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
      calc
        (∑ j, K i j * dp j) = ∑ j, -(|K i j| * g j) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [dp, mul_neg, p19Choice_mul]
        _ = -(∑ j, |K i j| * g j) := by simp
    change (∑ j, H i j * db j) - (∑ j, K i j * dp j) =
      (∑ j, |K i j| * g j) + (∑ j, |H i j| * f j)
    rw [hH, hK]
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
  let C := p19ConditionFormula K H g f xNorm
  have hupper : ∀ q ∈ S, q ≤ C := by
    intro q hq
    obtain ⟨dp, db, hadm, rfl⟩ := hq
    change ‖p19LinearResponse K H dp db‖ / xNorm ≤
      ‖p19ConditionRadius K H g f‖ / xNorm
    exact div_le_div_of_nonneg_right
      (p19_response_le_radius K H g f dp db hg hf hadm) hx.le
  have hbdd : BddAbove S := ⟨C, hupper⟩
  have hzero : (0 : ℝ) ∈ S := by
    refine ⟨0, 0, ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        simpa using hf i
    · have hresp : p19LinearResponse K H (0 : P19Vector t) (0 : P19Vector n) = 0 := by
        funext i
        simp [p19LinearResponse]
      simp [hresp]
  have hnonempty : S.Nonempty := ⟨0, hzero⟩
  have hsup_nonneg : 0 ≤ sSup S := le_csSup hbdd hzero
  have hle : sSup S ≤ C := csSup_le hnonempty hupper
  have hge : C ≤ sSup S := by
    change ‖R‖ / xNorm ≤ sSup S
    apply (div_le_iff₀ hx).2
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).2
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)]
    obtain ⟨dp, db, hadm, hcoord⟩ := p19_coordinate_attained K H g f hg hf i
    have hmem : ‖p19LinearResponse K H dp db‖ / xNorm ∈ S :=
      ⟨dp, db, hadm, rfl⟩
    have hcoordle : R i ≤ ‖p19LinearResponse K H dp db‖ := by
      calc
        R i = |p19LinearResponse K H dp db i| := by
          rw [hcoord, abs_of_nonneg (p19_radius_nonneg K H g f hg hf i)]
        _ = ‖p19LinearResponse K H dp db i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖p19LinearResponse K H dp db‖ := norm_le_pi_norm _ i
    have hdiv : R i / xNorm ≤ sSup S :=
      (div_le_div_of_nonneg_right hcoordle hx.le).trans (le_csSup hbdd hmem)
    exact (div_le_iff₀ hx).1 hdiv
  exact hle.antisymm hge

end VSCLReuse

import VSCLReuse.P19.Definitions

namespace VSCLReuse

private noncomputable def p19Signed (a r : ℝ) : ℝ := if 0 ≤ a then r else -r

private lemma p19Signed_abs (a r : ℝ) (hr : 0 ≤ r) : |p19Signed a r| = r := by
  unfold p19Signed
  split_ifs <;> simp [abs_of_nonneg hr]

private lemma p19Signed_mul (a r : ℝ) : a * p19Signed a r = |a| * r := by
  unfold p19Signed
  split_ifs with h
  · rw [abs_of_nonneg h]
  · have ha : a < 0 := lt_of_not_ge h
    rw [abs_of_neg ha]
    ring

private lemma p19WeightedSum_bound {m : ℕ} (a : Fin m → ℝ)
    (r v : Fin m → ℝ) (hv : ∀ j, |v j| ≤ r j) :
    |∑ j, a j * v j| ≤ ∑ j, |a j| * r j := by
  calc
    |∑ j, a j * v j| ≤ ∑ j, |a j * v j| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (fun j : Fin m => a j * v j) Finset.univ)
    _ = ∑ j, |a j| * |v j| := by simp only [abs_mul]
    _ ≤ ∑ j, |a j| * r j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)

private lemma p19Radius_nonneg {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ p19ConditionRadius K H g f i := by
  unfold p19ConditionRadius
  apply add_nonneg
  · exact Finset.sum_nonneg fun j hj => mul_nonneg (abs_nonneg _) (hg j)
  · exact Finset.sum_nonneg fun j hj => mul_nonneg (abs_nonneg _) (hf j)

private lemma p19Response_bound {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n)
    (ha : P19Admissible g f dp db) (i : Fin n) :
    |p19LinearResponse K H dp db i| ≤ p19ConditionRadius K H g f i := by
  rcases ha with ⟨hp, hb⟩
  have hH := p19WeightedSum_bound (H i) f db hb
  have hK := p19WeightedSum_bound (K i) g dp hp
  unfold p19LinearResponse p19ConditionRadius
  have ht : |(∑ j, H i j * db j) - (∑ j, K i j * dp j)| ≤
      |∑ j, H i j * db j| + |∑ j, K i j * dp j| := by
    simpa using abs_sub_le (∑ j, H i j * db j) 0 (∑ j, K i j * dp j)
  linarith

private lemma p19Radius_attained {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    ∃ dp db, P19Admissible g f dp db ∧
      p19LinearResponse K H dp db i = p19ConditionRadius K H g f i := by
  let dp : P19Vector t := fun j => -p19Signed (K i j) (g j)
  let db : P19Vector n := fun j => p19Signed (H i j) (f j)
  refine ⟨dp, db, ?_, ?_⟩
  · constructor
    · intro j
      simp [dp, p19Signed_abs _ _ (hg j)]
    · intro j
      simp [db, p19Signed_abs _ _ (hf j)]
  · have hH : (∑ j, H i j * db j) = ∑ j, |H i j| * f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact p19Signed_mul (H i j) (f j)
    have hK : (∑ j, K i j * dp j) = -(∑ j, |K i j| * g j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [dp]
      rw [mul_neg, p19Signed_mul]
    simp only [p19LinearResponse, p19ConditionRadius]
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
  have hzero_mem : (0 : ℝ) ∈ S := by
    refine ⟨0, 0, ?_, ?_⟩
    · constructor
      · intro j
        simpa using hg j
      · intro i
        simpa using hf i
    · have hz : p19LinearResponse K H (0 : P19Vector t) (0 : P19Vector n) = 0 := by
        funext i
        simp [p19LinearResponse]
      simp [hz]
  have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
  have hS_upper : ∀ q ∈ S, q ≤ p19ConditionFormula K H g f xNorm := by
    intro q hq
    rcases hq with ⟨dp, db, ha, rfl⟩
    apply (div_le_div_iff_of_pos_right hx).mpr
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using
      (p19Response_bound K H g f dp db ha i).trans
        (by simpa only [Real.norm_eq_abs, abs_of_nonneg (p19Radius_nonneg K H g f hg hf i)]
          using (norm_le_pi_norm (p19ConditionRadius K H g f) i))
  have hS_bdd : BddAbove S := ⟨p19ConditionFormula K H g f xNorm, hS_upper⟩
  apply le_antisymm
  · apply csSup_le hS_nonempty
    exact hS_upper
  · have hsup_nonneg : 0 ≤ sSup S := le_csSup hS_bdd hzero_mem
    have hnorm_le : ‖p19ConditionRadius K H g f‖ ≤ sSup S * xNorm := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsup_nonneg hx.le)).mpr
      intro i
      obtain ⟨dp, db, ha, heq⟩ := p19Radius_attained K H g f hg hf i
      have hmem : ‖p19LinearResponse K H dp db‖ / xNorm ∈ S :=
        ⟨dp, db, ha, rfl⟩
      have hle : ‖p19LinearResponse K H dp db‖ / xNorm ≤ sSup S :=
        le_csSup hS_bdd hmem
      have hcoord : p19ConditionRadius K H g f i ≤ ‖p19LinearResponse K H dp db‖ := by
        calc
          p19ConditionRadius K H g f i = |p19ConditionRadius K H g f i| :=
            (abs_of_nonneg (p19Radius_nonneg K H g f hg hf i)).symm
          _ = |p19LinearResponse K H dp db i| := by rw [heq]
          _ ≤ ‖p19LinearResponse K H dp db‖ := by
            simpa only [Real.norm_eq_abs] using
              (norm_le_pi_norm (p19LinearResponse K H dp db) i)
      have htotal : ‖p19LinearResponse K H dp db‖ ≤ sSup S * xNorm :=
        (div_le_iff₀ hx).mp hle
      simpa only [Real.norm_eq_abs, abs_of_nonneg (p19Radius_nonneg K H g f hg hf i)]
        using hcoord.trans htotal
    exact (div_le_iff₀ hx).mpr hnorm_le

end VSCLReuse

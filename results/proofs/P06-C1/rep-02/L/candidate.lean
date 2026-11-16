import VSCLReuse.P06.Definitions

namespace VSCLReuse

private theorem p06_sum_perturbation_bound {m : ℕ}
    (a c : Fin m → ℝ) (g : ℝ)
    (hc : ∀ j, |c j - 1| ≤ g) :
    |(∑ j, a j * c j) - ∑ j, a j| ≤ g * ∑ j, |a j| := by
  have heq : (∑ j, a j * c j) - ∑ j, a j =
      ∑ j, a j * (c j - 1) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext j
    ring
  rw [heq]
  calc
    |∑ j, a j * (c j - 1)| ≤ ∑ j, |a j * (c j - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |c j - 1| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |a j| * g := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hc j) (abs_nonneg _)
    _ = g * ∑ j, |a j| := by rw [Finset.mul_sum]; congr 1; ext j; ring

private theorem p06_ratio_perturbation_bound
    {A B A' B' eA eB : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hEA : |A' - A| ≤ eA * |A|)
    (hEB : |B' - B| ≤ eB * |B|)
    (heB : eB < 1) :
    |A / B - A' / B'| / |A / B| ≤ (eA + eB) / (1 - eB) := by
  have hAabs : 0 < |A| := abs_pos.mpr hA
  have hBabs : 0 < |B| := abs_pos.mpr hB
  let a : ℝ := (A' - A) / A
  let b : ℝ := (B' - B) / B
  have ha_le : |a| ≤ eA := by
    dsimp [a]
    rw [abs_div]
    exact (div_le_iff₀ hAabs).2 (by nlinarith [hEA])
  have hb_le : |b| ≤ eB := by
    dsimp [b]
    rw [abs_div]
    exact (div_le_iff₀ hBabs).2 (by nlinarith [hEB])
  have ha0 : 0 ≤ eA := (abs_nonneg a).trans ha_le
  have hb0 : 0 ≤ eB := (abs_nonneg b).trans hb_le
  have hb_lt : |b| < 1 := lt_of_le_of_lt hb_le heB
  have hOneB : 0 < 1 + b := by
    have := neg_abs_le b
    linarith
  have hAp : A' = A * (1 + a) := by
    dsimp [a]
    field_simp
    <;> ring
  have hBp : B' = B * (1 + b) := by
    dsimp [b]
    field_simp
    <;> ring
  have hB' : B' ≠ 0 := by
    rw [hBp]
    exact mul_ne_zero hB (ne_of_gt hOneB)
  have hAB : A / B ≠ 0 := div_ne_zero hA hB
  have hrat : A' / B' = (A / B) * ((1 + a) / (1 + b)) := by
    rw [hAp, hBp]
    field_simp
    <;> ring
  have hrel : |A / B - A' / B'| / |A / B| =
      |1 - (1 + a) / (1 + b)| := by
    rw [hrat]
    have hx : A / B - A / B * ((1 + a) / (1 + b)) =
        (A / B) * (1 - (1 + a) / (1 + b)) := by ring
    rw [hx, abs_mul]
    exact mul_div_cancel_left₀ _ (abs_ne_zero.mpr hAB)
  rw [hrel]
  have hnorm : |1 - (1 + a) / (1 + b)| = |b - a| / (1 + b) := by
    have heq : 1 - (1 + a) / (1 + b) = (b - a) / (1 + b) := by
      field_simp
      <;> ring
    rw [heq, abs_div, abs_of_pos hOneB]
  rw [hnorm]
  have htri : |b - a| ≤ eA + eB := by
    have h := abs_sub_le b 0 a
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hden : 0 < 1 - eB := by linarith
  have hden_le : 1 - eB ≤ 1 + b := by
    have := neg_abs_le b
    linarith
  apply (div_le_div_iff₀ hOneB hden).2
  exact (mul_le_mul_of_nonneg_right htri (le_of_lt hden)).trans
    (mul_le_mul_of_nonneg_left hden_le (add_nonneg ha0 hb0))

private theorem p06_barycentric_gamma_bound
    {n : ℕ} (problem : P06SecondBarycentricProblem n) (u : ℝ)
    (run : P06SecondBarycentricExecution problem u)
    (hnumerator : p06SecondBarycentricNumerator problem ≠ 0)
    (hdenominator : p06SecondBarycentricDenominator problem ≠ 0)
    (hsmall : gamma u (p06DenominatorCounterLength n) *
      p06SecondBarycentricOneCondition problem < 1) :
    p06SecondBarycentricRelativeError run ≤
      (gamma u (p06NumeratorCounterLength n) *
          p06SecondBarycentricDataCondition problem +
        gamma u (p06DenominatorCounterLength n) *
          p06SecondBarycentricOneCondition problem) /
        (1 - gamma u (p06DenominatorCounterLength n) *
          p06SecondBarycentricOneCondition problem) := by
  let c : Fin (n + 1) → ℝ :=
    p06DirectBarycentricCoefficient problem.nodes problem.x
  let a : Fin (n + 1) → ℝ := fun j => c j * problem.data j
  let b : Fin (n + 1) → ℝ := c
  let A : ℝ := ∑ j, a j
  let B : ℝ := ∑ j, b j
  let A' : ℝ := ∑ j, a j * (run.numeratorCounter j).value
  let B' : ℝ := ∑ j, b j * (run.denominatorCounter j).value
  let gA : ℝ := gamma u (p06NumeratorCounterLength n)
  let gB : ℝ := gamma u (p06DenominatorCounterLength n)
  let cA : ℝ := (∑ j, |a j|) / |A|
  let cB : ℝ := (∑ j, |b j|) / |B|
  have hA : A ≠ 0 := by
    change p06SecondBarycentricNumerator problem ≠ 0
    exact hnumerator
  have hB : B ≠ 0 := by
    simpa only [B, b, c, p06SecondBarycentricDenominator,
      p06InterpolationValue, mul_one] using hdenominator
  have hCA : cA = p06SecondBarycentricDataCondition problem := by
    rfl
  have hCB : cB = p06SecondBarycentricOneCondition problem := by
    simp only [cB, B, b, c, p06SecondBarycentricOneCondition,
      p06Condition, p06SecondBarycentricDenominator,
      p06InterpolationValue, mul_one]
  have hA' : A' =
      (∑ j,
        c j * (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) *
        run.quotientCounter.value := by
    dsimp [A']
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.numeratorCounter_eq j]
    dsimp [a]
    ring
  have hB' : B' =
      ∑ j, c j * (run.weightCounter j).value *
        (run.denominatorEvaluationCounter j).value := by
    dsimp [B']
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.denominatorCounter_eq j]
    dsimp [b]
    ring
  have hcomputed : p06SecondBarycentricComputed run = A' / B' := by
    dsimp [p06SecondBarycentricComputed]
    rw [hA', hB']
    dsimp [c]
    ring
  have hEA0 : |A' - A| ≤ gA * ∑ j, |a j| :=
    p06_sum_perturbation_bound a (fun j => (run.numeratorCounter j).value) gA
      (fun j => (run.numeratorCounter j).gamma_le run.numeratorGammaValid)
  have hEB0 : |B' - B| ≤ gB * ∑ j, |b j| :=
    p06_sum_perturbation_bound b (fun j => (run.denominatorCounter j).value) gB
      (fun j => (run.denominatorCounter j).gamma_le run.denominatorGammaValid)
  have hEA : |A' - A| ≤ (gA * cA) * |A| := by
    refine hEA0.trans ?_
    dsimp [cA]
    field_simp
    exact le_refl _
  have hEB : |B' - B| ≤ (gB * cB) * |B| := by
    refine hEB0.trans ?_
    dsimp [cB]
    field_simp
    exact le_refl _
  have hsmall' : gB * cB < 1 := by simpa only [gB, hCB] using hsmall
  have hratio := p06_ratio_perturbation_bound hA hB hEA hEB hsmall'
  have hAN : A = p06SecondBarycentricNumerator problem := rfl
  have hBD : B = p06SecondBarycentricDenominator problem := by
    simp [B, b, c, p06SecondBarycentricDenominator, p06InterpolationValue]
  rw [hAN, hBD, hCA, hCB] at hratio
  simpa only [p06SecondBarycentricRelativeError, p06SecondBarycentricExact,
    hcomputed, gA, gB] using hratio

private noncomputable def p06_envelope (a b c d z : ℝ) : ℝ :=
  ((a * z / (1 - a * z)) * c + (b * z / (1 - b * z)) * d) /
    (1 - (b * z / (1 - b * z)) * d)

private noncomputable def p06_envelopeRemainder (a b c d z : ℝ) : ℝ :=
  p06_envelope a b c d z - (a * c + b * d) * z

private theorem p06_envelopeRemainder_isBigO (a b c d : ℝ) :
    (fun z : ℝ => p06_envelopeRemainder a b c d z) =O[nhds 0]
      (fun z : ℝ => z ^ 2) := by
  let H : ℝ → ℝ := fun z =>
    ((a * c + b * d) * (a + b * (1 + d)) - a * b * (c + d) -
      (a * c + b * d) * a * b * (1 + d) * z) /
    ((1 - a * z) * (1 - b * (1 + d) * z))
  have hHcont : ContinuousAt H 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  have hH : H =O[nhds 0] (fun _ : ℝ => (1 : ℝ)) :=
    hHcont.isBigO_one ℝ
  have hprod : (fun z : ℝ => z ^ 2 * H z) =O[nhds 0]
      (fun z : ℝ => z ^ 2) := by
    have hs : (fun z : ℝ => z ^ 2) =O[nhds 0]
        (fun z : ℝ => z ^ 2) := Asymptotics.isBigO_refl _ _
    simpa only [mul_one] using hs.mul hH
  have h1 : ∀ᶠ z : ℝ in nhds 0, 1 - a * z ≠ 0 := by
    have hc : ContinuousAt (fun z : ℝ => 1 - a * z) 0 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  have h2 : ∀ᶠ z : ℝ in nhds 0, 1 - b * z ≠ 0 := by
    have hc : ContinuousAt (fun z : ℝ => 1 - b * z) 0 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  have h3 : ∀ᶠ z : ℝ in nhds 0,
      1 - b * (1 + d) * z ≠ 0 := by
    have hc : ContinuousAt (fun z : ℝ => 1 - b * (1 + d) * z) 0 := by fun_prop
    exact hc.eventually_ne (by norm_num)
  have heq : (fun z : ℝ => p06_envelopeRemainder a b c d z) =ᶠ[nhds 0]
      (fun z : ℝ => z ^ 2 * H z) := by
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    have hdenEq : 1 - (b * z / (1 - b * z)) * d =
        (1 - b * (1 + d) * z) / (1 - b * z) := by
      field_simp
      ring
    have hden : 1 - (b * z / (1 - b * z)) * d ≠ 0 := by
      rw [hdenEq]
      exact div_ne_zero hz3 hz2
    have hz2' : 1 - z * b ≠ 0 := by
      convert hz2 using 1 <;> ring
    have hz3' : 1 + (-(z * b) - z * b * d) ≠ 0 := by
      convert hz3 using 1 <;> ring
    have hz3'' : 1 - z * b * (1 + d) ≠ 0 := by
      convert hz3 using 1 <;> ring
    dsimp [p06_envelopeRemainder, p06_envelope, H]
    rw [hdenEq]
    field_simp [hz1, hz2, hz3, hz2', hz3']
    field_simp [hz3'']
    <;> ring
  exact hprod.congr' heq.symm Filter.EventuallyEq.rfl

theorem p06_c1_barycentric_forward_bound
    {n : ℕ} {ι : Type*} {l : Filter ι} [l.NeBot]
    (problem : P06SecondBarycentricProblem n)
    (u : ι → ℝ)
    (run : ∀ t, P06SecondBarycentricExecution problem (u t))
    (hu : Filter.Tendsto u l (nhds 0))
    (hnumerator : p06SecondBarycentricNumerator problem ≠ 0)
    (hdenominator : p06SecondBarycentricDenominator problem ≠ 0) :
    let conditionData := p06SecondBarycentricDataCondition problem
    let conditionOne := p06SecondBarycentricOneCondition problem
    ∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        p06SecondBarycentricRelativeError (run t) ≤
          u t * p06SecondBarycentricFirstOrderCoefficient n
            conditionData conditionOne +
          |remainder t| := by
  -- PROOF_START P06-C1-H001
  let conditionData := p06SecondBarycentricDataCondition problem
  let conditionOne := p06SecondBarycentricOneCondition problem
  let a : ℝ := p06NumeratorCounterLength n
  let b : ℝ := p06DenominatorCounterLength n
  let remainder : ι → ℝ :=
    fun t => p06_envelopeRemainder a b conditionData conditionOne (u t)
  refine ⟨remainder, ?_, ?_⟩
  · have h := p06_envelopeRemainder_isBigO a b conditionData conditionOne
    simpa only [remainder, Function.comp_def] using h.comp_tendsto hu
  · have hcontGamma : ContinuousAt
        (fun z : ℝ => gamma z (p06DenominatorCounterLength n)) 0 := by
      unfold gamma
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    have hcont : ContinuousAt
        (fun z : ℝ => gamma z (p06DenominatorCounterLength n) *
          conditionOne) 0 := hcontGamma.mul continuousAt_const
    have hlim : Filter.Tendsto
        (fun t => gamma (u t) (p06DenominatorCounterLength n) * conditionOne)
        l (nhds 0) := by
      convert hcont.tendsto.comp hu using 1 <;>
        simp [gamma]
    have hsmall : ∀ᶠ t in l,
        gamma (u t) (p06DenominatorCounterLength n) * conditionOne < 1 :=
      hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with t ht
    have hbound := p06_barycentric_gamma_bound problem (u t) (run t)
      hnumerator hdenominator ht
    have henv : p06SecondBarycentricRelativeError (run t) ≤
        p06_envelope a b conditionData conditionOne (u t) := by
      simpa only [p06_envelope, gamma, a, b, conditionData, conditionOne]
        using hbound
    calc
      p06SecondBarycentricRelativeError (run t) ≤
          p06_envelope a b conditionData conditionOne (u t) := henv
      _ = u t * p06SecondBarycentricFirstOrderCoefficient n
            conditionData conditionOne + remainder t := by
          dsimp [remainder, p06_envelopeRemainder,
            p06SecondBarycentricFirstOrderCoefficient, a, b]
          ring
      _ ≤ u t * p06SecondBarycentricFirstOrderCoefficient n
            conditionData conditionOne + |remainder t| := by
          exact add_le_add_right (le_abs_self (remainder t)) _

end VSCLReuse

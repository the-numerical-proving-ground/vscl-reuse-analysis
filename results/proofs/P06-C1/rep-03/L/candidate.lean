import VSCLReuse.P06.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p06_sum_counter_error {m : ℕ} (a r : Fin m → ℝ) (e : ℝ)
    (hr : ∀ j, |r j - 1| ≤ e) :
    |(∑ j, a j * r j) - ∑ j, a j| ≤ e * ∑ j, |a j| := by
  have hsum : (∑ j, a j * r j) - ∑ j, a j =
      ∑ j, a j * (r j - 1) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    |∑ j, a j * (r j - 1)| ≤ ∑ j, |a j * (r j - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, e * |a j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, mul_comm e]
      exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _)
    _ = e * ∑ j, |a j| := by rw [← Finset.mul_sum]

private theorem p06_quotient_error
    {A B X Y eN eD : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (heN : 0 ≤ eN) (heD : 0 ≤ eD) (heD1 : eD < 1)
    (hX : |X - A| ≤ eN * |A|) (hY : |Y - B| ≤ eD * |B|) :
    |A / B - X / Y| / |A / B| ≤ (eN + eD) / (1 - eD) := by
  have ha : 0 < |A| := abs_pos.mpr hA
  have hb : 0 < |B| := abs_pos.mpr hB
  have hlow : (1 - eD) * |B| ≤ |Y| := by
    have htri : |B| ≤ |Y| + |Y - B| := by
      calc
        |B| = |Y - (Y - B)| := by congr 1; ring
        _ ≤ |Y| + |Y - B| := abs_sub _ _
    nlinarith
  have hy : 0 < |Y| := lt_of_lt_of_le (mul_pos (by linarith) hb) hlow
  have hYne : Y ≠ 0 := (abs_pos.mp hy)
  have htop : |A * Y - X * B| ≤ (eN + eD) * |A| * |B| := by
    calc
      |A * Y - X * B| = |A * (Y - B) - (X - A) * B| := by ring
      _ ≤ |A * (Y - B)| + |(X - A) * B| := abs_sub _ _
      _ = |A| * |Y - B| + |X - A| * |B| := by rw [abs_mul, abs_mul]
      _ ≤ |A| * (eD * |B|) + (eN * |A|) * |B| := by
        gcongr
      _ = (eN + eD) * |A| * |B| := by ring
  have hident : |A / B - X / Y| / |A / B| =
      |A * Y - X * B| / (|A| * |Y|) := by
    rw [div_sub_div A X hB hYne, abs_div, abs_div, abs_mul]
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hy]
  rw [hident]
  apply (div_le_div_iff₀ (mul_pos ha hy) (sub_pos.mpr heD1)).2
  have h1 := mul_le_mul_of_nonneg_right htop (sub_nonneg.mpr heD1.le)
  have h2 := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg (add_nonneg heN heD) (le_of_lt ha))
  nlinarith

private theorem p06_gamma_quadratic (k : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hsmall : (k : ℝ) * u ≤ 1 / 2) :
    gamma u k ≤ (k : ℝ) * u + 2 * ((k : ℝ) * u) ^ 2 := by
  unfold gamma
  have hz : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hden : 0 < 1 - (k : ℝ) * u := by linarith
  apply (div_le_iff₀ hden).2
  have hprod : 0 ≤ ((k : ℝ) * u) ^ 2 * (1 - 2 * ((k : ℝ) * u)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

private theorem p06_first_order_quotient
    {u eN eD L Q R : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (heN : 0 ≤ eN) (heD : 0 ≤ eD)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hE : eN + eD ≤ u * L + u ^ 2 * Q)
    (hD : eD ≤ u * R) (hsmall : u * R ≤ 1 / 2) :
    (eN + eD) / (1 - eD) ≤
      u * L + (Q + 2 * (L + Q) * R) * u ^ 2 := by
  have heDhalf : eD ≤ 1 / 2 := le_trans hD hsmall
  have hden : 0 < 1 - eD := by linarith
  have hsum : 0 ≤ eN + eD := add_nonneg heN heD
  have hrec : (eN + eD) / (1 - eD) ≤ (eN + eD) * (1 + 2 * eD) := by
    apply (div_le_iff₀ hden).2
    have hz : 0 ≤ eD * (1 - 2 * eD) := mul_nonneg heD (by linarith)
    nlinarith [mul_nonneg hsum hz]
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hElinear : eN + eD ≤ u * (L + Q) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu2) hQ]
  have hcross := mul_le_mul hElinear hD heD (mul_nonneg hu (add_nonneg hL hQ))
  have hcross2 : (eN + eD) * eD ≤ u ^ 2 * ((L + Q) * R) := by
    nlinarith [hcross]
  linarith [hrec, hE, hcross2]

private theorem p06_computed_quotient {n : ℕ}
    {problem : P06SecondBarycentricProblem n} {u : ℝ}
    (run : P06SecondBarycentricExecution problem u) :
    p06SecondBarycentricComputed run =
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        problem.data j * (run.numeratorCounter j).value) /
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.denominatorCounter j).value) := by
  let c := p06DirectBarycentricCoefficient problem.nodes problem.x
  have hnum :
      (∑ j, c j * problem.data j * (run.numeratorCounter j).value) =
        (∑ j, c j * (run.weightCounter j).value * problem.data j *
          (run.numeratorEvaluationCounter j).value) * run.quotientCounter.value := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.numeratorCounter_eq j]
    ring
  have hden :
      (∑ j, c j * (run.denominatorCounter j).value) =
        ∑ j, c j * (run.weightCounter j).value *
          (run.denominatorEvaluationCounter j).value := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.denominatorCounter_eq j]
    ring
  change
    ((∑ j, c j * (run.weightCounter j).value * problem.data j *
      (run.numeratorEvaluationCounter j).value) /
      (∑ j, c j * (run.weightCounter j).value *
        (run.denominatorEvaluationCounter j).value)) *
      run.quotientCounter.value =
      (∑ j, c j * problem.data j * (run.numeratorCounter j).value) /
      (∑ j, c j * (run.denominatorCounter j).value)
  rw [hnum, hden]
  simp only [div_eq_mul_inv]
  ring

private theorem p06_run_ratio_bound {n : ℕ}
    (problem : P06SecondBarycentricProblem n) {u : ℝ}
    (run : P06SecondBarycentricExecution problem u)
    (hA : p06SecondBarycentricNumerator problem ≠ 0)
    (hB : p06SecondBarycentricDenominator problem ≠ 0)
    (hsmall : gamma u (p06DenominatorCounterLength n) *
      p06SecondBarycentricOneCondition problem < 1) :
    p06SecondBarycentricRelativeError run ≤
      (gamma u (p06NumeratorCounterLength n) *
          p06SecondBarycentricDataCondition problem +
        gamma u (p06DenominatorCounterLength n) *
          p06SecondBarycentricOneCondition problem) /
      (1 - gamma u (p06DenominatorCounterLength n) *
        p06SecondBarycentricOneCondition problem) := by
  let c := p06DirectBarycentricCoefficient problem.nodes problem.x
  let A := p06SecondBarycentricNumerator problem
  let B := p06SecondBarycentricDenominator problem
  let X := ∑ j, c j * problem.data j * (run.numeratorCounter j).value
  let Y := ∑ j, c j * (run.denominatorCounter j).value
  let eN := gamma u (p06NumeratorCounterLength n) *
    p06SecondBarycentricDataCondition problem
  let eD := gamma u (p06DenominatorCounterLength n) *
    p06SecondBarycentricOneCondition problem
  have hgammaN : 0 ≤ gamma u (p06NumeratorCounterLength n) := by
    unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) run.u_nonneg)
      (le_of_lt (sub_pos.mpr run.numeratorGammaValid))
  have hgammaD : 0 ≤ gamma u (p06DenominatorCounterLength n) := by
    unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) run.u_nonneg)
      (le_of_lt (sub_pos.mpr run.denominatorGammaValid))
  have hC : 0 ≤ p06SecondBarycentricDataCondition problem := by
    unfold p06SecondBarycentricDataCondition p06Condition p06InterpolationValue
    exact div_nonneg (Finset.sum_nonneg fun j hj => abs_nonneg _) (abs_nonneg _)
  have hD : 0 ≤ p06SecondBarycentricOneCondition problem := by
    unfold p06SecondBarycentricOneCondition p06Condition p06InterpolationValue
    exact div_nonneg (Finset.sum_nonneg fun j hj => abs_nonneg _) (abs_nonneg _)
  have heN : 0 ≤ eN := mul_nonneg hgammaN hC
  have heD : 0 ≤ eD := mul_nonneg hgammaD hD
  have hXsum : |X - A| ≤ gamma u (p06NumeratorCounterLength n) *
      ∑ j, |c j * problem.data j| := by
    convert p06_sum_counter_error (fun j => c j * problem.data j)
      (fun j => (run.numeratorCounter j).value)
      (gamma u (p06NumeratorCounterLength n))
      (fun j => (run.numeratorCounter j).gamma_le run.numeratorGammaValid) using 1
  have hYsum : |Y - B| ≤ gamma u (p06DenominatorCounterLength n) *
      ∑ j, |c j| := by
    simpa [Y, B, c, p06SecondBarycentricDenominator, p06InterpolationValue]
      using p06_sum_counter_error c
        (fun j => (run.denominatorCounter j).value)
        (gamma u (p06DenominatorCounterLength n))
        (fun j => (run.denominatorCounter j).gamma_le run.denominatorGammaValid)
  have hX : |X - A| ≤ eN * |A| := by
    refine le_trans hXsum ?_
    have hAbsA : |A| ≠ 0 := abs_ne_zero.mpr hA
    change gamma u (p06NumeratorCounterLength n) *
      (∑ j, |c j * problem.data j|) ≤
      (gamma u (p06NumeratorCounterLength n) *
        ((∑ j, |c j * problem.data j|) / |A|)) * |A|
    apply le_of_eq
    field_simp [hAbsA]
  have hY : |Y - B| ≤ eD * |B| := by
    refine le_trans hYsum ?_
    have hAbsB : |B| ≠ 0 := abs_ne_zero.mpr hB
    change gamma u (p06DenominatorCounterLength n) *
      (∑ j, |c j|) ≤
      (gamma u (p06DenominatorCounterLength n) *
        ((∑ j, |c j * (1 : ℝ)|) / |B|)) * |B|
    simp only [mul_one]
    apply le_of_eq
    field_simp [hAbsB]
  have hcomp : p06SecondBarycentricComputed run = X / Y :=
    p06_computed_quotient run
  change |A / B - p06SecondBarycentricComputed run| / |A / B| ≤
    (eN + eD) / (1 - eD)
  rw [hcomp]
  exact p06_quotient_error hA hB heN heD hsmall hX hY

private theorem p06_gamma_pair_first_order (a b : ℕ) (C D u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsa : (a : ℝ) * u ≤ 1 / 2)
    (hsb : (b : ℝ) * u ≤ 1 / 2)
    (hsR : u * (((b : ℝ) + 2 * (b : ℝ) ^ 2) * D) ≤ 1 / 2) :
    (gamma u a * C + gamma u b * D) / (1 - gamma u b * D) ≤
      u * ((a : ℝ) * C + (b : ℝ) * D) +
      (2 * (a : ℝ) ^ 2 * C + 2 * (b : ℝ) ^ 2 * D +
        2 * (((a : ℝ) * C + (b : ℝ) * D) +
          (2 * (a : ℝ) ^ 2 * C + 2 * (b : ℝ) ^ 2 * D)) *
          (((b : ℝ) + 2 * (b : ℝ) ^ 2) * D)) * u ^ 2 := by
  let L := (a : ℝ) * C + (b : ℝ) * D
  let Q := 2 * (a : ℝ) ^ 2 * C + 2 * (b : ℝ) ^ 2 * D
  let R := ((b : ℝ) + 2 * (b : ℝ) ^ 2) * D
  let eN := gamma u a * C
  let eD := gamma u b * D
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hγa : 0 ≤ gamma u a := by
    unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)
  have hγb : 0 ≤ gamma u b := by
    unfold gamma
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)
  have heN : 0 ≤ eN := mul_nonneg hγa hC
  have heD : 0 ≤ eD := mul_nonneg hγb hD
  have hγa' := mul_le_mul_of_nonneg_right (p06_gamma_quadratic a u hu hsa) hC
  have hγb' := mul_le_mul_of_nonneg_right (p06_gamma_quadratic b u hu hsb) hD
  have hE : eN + eD ≤ u * L + u ^ 2 * Q := by
    dsimp [eN, eD, L, Q]
    nlinarith [hγa', hγb']
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hDsmall : eD ≤ u * R := by
    dsimp [eD, R]
    nlinarith [hγb', mul_nonneg (sub_nonneg.mpr hu2)
      (mul_nonneg (sq_nonneg (b : ℝ)) hD)]
  exact p06_first_order_quotient hu hu1 heN heD hL hQ hE hDsmall hsR

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
  let a := p06NumeratorCounterLength n
  let b := p06DenominatorCounterLength n
  let C := p06SecondBarycentricDataCondition problem
  let D := p06SecondBarycentricOneCondition problem
  let L := (a : ℝ) * C + (b : ℝ) * D
  let Q := 2 * (a : ℝ) ^ 2 * C + 2 * (b : ℝ) ^ 2 * D
  let R := ((b : ℝ) + 2 * (b : ℝ) ^ 2) * D
  let K := Q + 2 * (L + Q) * R
  have hC : 0 ≤ C := by
    dsimp [C, p06SecondBarycentricDataCondition, p06Condition,
      p06InterpolationValue]
    exact div_nonneg (Finset.sum_nonneg fun j hj => abs_nonneg _) (abs_nonneg _)
  have hD : 0 ≤ D := by
    dsimp [D, p06SecondBarycentricOneCondition, p06Condition,
      p06InterpolationValue]
    exact div_nonneg (Finset.sum_nonneg fun j hj => abs_nonneg _) (abs_nonneg _)
  have hK : 0 ≤ K := by
    dsimp [K, L, Q, R]
    positivity
  have hsa : ∀ᶠ t in l, (a : ℝ) * u t ≤ 1 / 2 := by
    have hlim : Filter.Tendsto (fun t => (a : ℝ) * u t) l (nhds 0) := by
      simpa using hu.const_mul (a : ℝ)
    filter_upwards [(tendsto_order.mp hlim).2 (1 / 2) (by norm_num)]
      with t ht
    exact le_of_lt ht
  have hsb : ∀ᶠ t in l, (b : ℝ) * u t ≤ 1 / 2 := by
    have hlim : Filter.Tendsto (fun t => (b : ℝ) * u t) l (nhds 0) := by
      simpa using hu.const_mul (b : ℝ)
    filter_upwards [(tendsto_order.mp hlim).2 (1 / 2) (by norm_num)]
      with t ht
    exact le_of_lt ht
  have hsR : ∀ᶠ t in l, u t * R ≤ 1 / 2 := by
    have hlim : Filter.Tendsto (fun t => u t * R) l (nhds 0) := by
      simpa using hu.mul_const R
    filter_upwards [(tendsto_order.mp hlim).2 (1 / 2) (by norm_num)]
      with t ht
    exact le_of_lt ht
  have hu1 : ∀ᶠ t in l, u t ≤ 1 := by
    filter_upwards [(tendsto_order.mp hu).2 1 zero_lt_one]
      with t ht
    exact le_of_lt ht
  refine ⟨fun t => K * (u t) ^ 2, ?_, ?_⟩
  · simpa using
      (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).const_mul_left K
  · filter_upwards [hsa, hsb, hsR, hu1] with t hsa_t hsb_t hsR_t hu1_t
    have hu_t : 0 ≤ u t := (run t).u_nonneg
    have hγb := mul_le_mul_of_nonneg_right
      (p06_gamma_quadratic b (u t) hu_t hsb_t) hD
    have hu2 : (u t) ^ 2 ≤ u t := by nlinarith
    have hsmall : gamma (u t) b * D < 1 := by
      dsimp [R] at hsR_t
      nlinarith [hγb, mul_nonneg (sub_nonneg.mpr hu2)
        (mul_nonneg (sq_nonneg (b : ℝ)) hD)]
    have hratio := p06_run_ratio_bound problem (run t)
      hnumerator hdenominator (show gamma (u t)
        (p06DenominatorCounterLength n) *
        p06SecondBarycentricOneCondition problem < 1 from hsmall)
    have hpair := p06_gamma_pair_first_order a b C D (u t)
      hu_t hu1_t hC hD hsa_t hsb_t hsR_t
    change p06SecondBarycentricRelativeError (run t) ≤
      u t * p06SecondBarycentricFirstOrderCoefficient n C D +
        |K * (u t) ^ 2|
    calc
      p06SecondBarycentricRelativeError (run t) ≤
          (gamma (u t) a * C + gamma (u t) b * D) /
            (1 - gamma (u t) b * D) := by simpa [a, b, C, D] using hratio
      _ ≤ u t * p06SecondBarycentricFirstOrderCoefficient n C D +
          K * (u t) ^ 2 := by
        simpa [K, L, Q, R, a, b, p06SecondBarycentricFirstOrderCoefficient]
          using hpair
      _ = u t * p06SecondBarycentricFirstOrderCoefficient n C D +
          |K * (u t) ^ 2| := by rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]

end VSCLReuse

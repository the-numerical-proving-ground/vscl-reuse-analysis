import VSCLReuse.P06.Definitions

namespace VSCLReuse

private lemma p06_sum_error {m : ℕ} (a e : Fin m → ℝ) (g : ℝ)
    (he : ∀ j, |e j - 1| ≤ g) :
    |(∑ j, a j * e j) - ∑ j, a j| ≤ g * ∑ j, |a j| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j, (a j * e j - a j)| = |∑ j, a j * (e j - 1)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j, |a j * (e j - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |a j| * g := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
    _ = g * ∑ j, |a j| := by rw [← Finset.sum_mul]; ring

private lemma p06_unit_quotient_bound (a b α β : ℝ)
    (ha : |a| ≤ α) (hb : |b| ≤ β) (hβ : β < 1) :
    |1 - (1 + a) / (1 + b)| ≤ (α + β) / (1 - β) := by
  have hα : 0 ≤ α := le_trans (abs_nonneg _) ha
  have hβ0 : 0 ≤ β := le_trans (abs_nonneg _) hb
  have hden : 0 < 1 + b := by
    have := (abs_le.mp hb).1
    linarith
  have hlow : 0 < 1 - β := by linarith
  have hdenlow : 1 - β ≤ 1 + b := by
    have := (abs_le.mp hb).1
    linarith
  have hnum : |b - a| ≤ α + β := by
    calc
      |b - a| ≤ |b| + |a| := by simpa using abs_sub_le b 0 a
      _ ≤ α + β := by linarith
  have hident : 1 - (1 + a) / (1 + b) = (b - a) / (1 + b) := by
    field_simp
    ring
  rw [hident, abs_div, abs_of_pos hden]
  calc
    |b - a| / (1 + b) ≤ (α + β) / (1 + b) := by gcongr
    _ ≤ (α + β) / (1 - β) := by gcongr

private lemma p06_quotient_bound (A B A' B' α β : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hAerr : |A' - A| ≤ α * |A|)
    (hBerr : |B' - B| ≤ β * |B|)
    (hβ : β < 1) :
    |A / B - A' / B'| / |A / B| ≤ (α + β) / (1 - β) := by
  have hB' : B' ≠ 0 := by
    intro hz
    have hbound : |B| ≤ β * |B| := by
      simpa [hz, abs_neg] using hBerr
    have hpos : 0 < |B| := abs_pos.mpr hB
    nlinarith [mul_lt_mul_of_pos_right hβ hpos]
  let a := (A' - A) / A
  let b := (B' - B) / B
  have ha : |a| ≤ α := by
    dsimp [a]
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hA)).2 hAerr
  have hb : |b| ≤ β := by
    dsimp [b]
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hB)).2 hBerr
  have haeq : 1 + a = A' / A := by
    dsimp [a]
    field_simp
    ring
  have hbeq : 1 + b = B' / B := by
    dsimp [b]
    field_simp
    ring
  have hident : (A / B - A' / B') / (A / B) =
      1 - (1 + a) / (1 + b) := by
    rw [haeq, hbeq]
    field_simp
  rw [← abs_div, hident]
  exact p06_unit_quotient_bound a b α β ha hb hβ

private lemma p06_computed_eq_counter_quotient {n : ℕ}
    {problem : P06SecondBarycentricProblem n} {u : ℝ}
    (run : P06SecondBarycentricExecution problem u) :
    p06SecondBarycentricComputed run =
      (∑ j, (p06DirectBarycentricCoefficient problem.nodes problem.x j *
        problem.data j) * (run.numeratorCounter j).value) /
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.denominatorCounter j).value) := by
  let c := p06DirectBarycentricCoefficient problem.nodes problem.x
  have hn :
      (∑ j, (c j * problem.data j) * (run.numeratorCounter j).value) =
      (∑ j, c j * (run.weightCounter j).value * problem.data j *
        (run.numeratorEvaluationCounter j).value) * run.quotientCounter.value := by
    simp_rw [run.numeratorCounter_eq]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hd :
      (∑ j, c j * (run.denominatorCounter j).value) =
      ∑ j, c j * (run.weightCounter j).value *
        (run.denominatorEvaluationCounter j).value := by
    apply Finset.sum_congr rfl
    intro j _
    rw [run.denominatorCounter_eq]
    ring
  change ((∑ j, c j * (run.weightCounter j).value * problem.data j *
      (run.numeratorEvaluationCounter j).value) /
    (∑ j, c j * (run.weightCounter j).value *
      (run.denominatorEvaluationCounter j).value)) * run.quotientCounter.value = _
  rw [hn, hd]
  ring

private lemma p06_gamma_nonneg (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : GammaValid u k) : 0 ≤ gamma u k := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p06_forward_bound_at {n : ℕ}
    {problem : P06SecondBarycentricProblem n} {u : ℝ}
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
  let a := fun j => c j * problem.data j
  let A := ∑ j, a j
  let B := ∑ j, c j
  let A' := ∑ j, a j * (run.numeratorCounter j).value
  let B' := ∑ j, c j * (run.denominatorCounter j).value
  let gA := gamma u (p06NumeratorCounterLength n)
  let gB := gamma u (p06DenominatorCounterLength n)
  let C := p06SecondBarycentricDataCondition problem
  let D := p06SecondBarycentricOneCondition problem
  have hgA : 0 ≤ gA := p06_gamma_nonneg u _ run.u_nonneg run.numeratorGammaValid
  have hgB : 0 ≤ gB := p06_gamma_nonneg u _ run.u_nonneg run.denominatorGammaValid
  have hAerr' : |A' - A| ≤ gA * ∑ j, |a j| := by
    exact p06_sum_error a (fun j => (run.numeratorCounter j).value) gA
      (fun j => (run.numeratorCounter j).gamma_le run.numeratorGammaValid)
  have hBerr' : |B' - B| ≤ gB * ∑ j, |c j| := by
    exact p06_sum_error c (fun j => (run.denominatorCounter j).value) gB
      (fun j => (run.denominatorCounter j).gamma_le run.denominatorGammaValid)
  have hAeq : A = p06SecondBarycentricNumerator problem := by
    simp only [A, a, c, p06SecondBarycentricNumerator, p06InterpolationValue]
  have hBeq : B = p06SecondBarycentricDenominator problem := by
    simp only [B, c, p06SecondBarycentricDenominator, p06InterpolationValue,
      mul_one]
  have hA0 : A ≠ 0 := hAeq ▸ hA
  have hB0 : B ≠ 0 := hBeq ▸ hB
  have hCeq : C = (∑ j, |a j|) / |A| := by
    simp only [C, a, A, c, p06SecondBarycentricDataCondition,
      p06Condition, p06InterpolationValue]
  have hDeq : D = (∑ j, |c j|) / |B| := by
    simp only [D, B, c, p06SecondBarycentricOneCondition,
      p06Condition, p06InterpolationValue, mul_one]
  have hAerr : |A' - A| ≤ (gA * C) * |A| := by
    calc
      |A' - A| ≤ gA * ∑ j, |a j| := hAerr'
      _ = (gA * C) * |A| := by rw [hCeq]; field_simp [hA0]
  have hBerr : |B' - B| ≤ (gB * D) * |B| := by
    calc
      |B' - B| ≤ gB * ∑ j, |c j| := hBerr'
      _ = (gB * D) * |B| := by rw [hDeq]; field_simp [hB0]
  have hquot := p06_quotient_bound A B A' B' (gA * C) (gB * D)
    hA0 hB0 hAerr hBerr hsmall
  have hrepr : p06SecondBarycentricRelativeError run =
      |A / B - A' / B'| / |A / B| := by
    rw [p06SecondBarycentricRelativeError,
      p06_computed_eq_counter_quotient, p06SecondBarycentricExact]
    rw [← hAeq, ← hBeq]
  rw [hrepr]
  exact hquot

private noncomputable def p06_remainder_factor (N D C O v : ℝ) : ℝ :=
  N ^ 2 * C / (1 - N * v) + D ^ 2 * O / (1 - D * v) +
    (N * C / (1 - N * v) + D * O / (1 - D * v)) *
      (D * O / (1 - D * v)) /
        (1 - (D * v / (1 - D * v)) * O)

private lemma p06_envelope_expansion (N D C O v : ℝ)
    (hN : 1 - N * v ≠ 0) (hD : 1 - D * v ≠ 0)
    (hsmall : 1 - (D * v / (1 - D * v)) * O ≠ 0) :
    ((N * v / (1 - N * v)) * C + (D * v / (1 - D * v)) * O) /
        (1 - (D * v / (1 - D * v)) * O) =
      v * (N * C + D * O) + v ^ 2 * p06_remainder_factor N D C O v := by
  let a := (N * v / (1 - N * v)) * C
  let b := (D * v / (1 - D * v)) * O
  let L := N * C / (1 - N * v) + D * O / (1 - D * v)
  let M := D * O / (1 - D * v)
  let P := N ^ 2 * C / (1 - N * v) + D ^ 2 * O / (1 - D * v)
  have ha : a = v * (N * C) + v ^ 2 * (N ^ 2 * C / (1 - N * v)) := by
    dsimp [a]
    field_simp [hN]
    ring
  have hb : b = v * (D * O) + v ^ 2 * (D ^ 2 * O / (1 - D * v)) := by
    dsimp [b]
    field_simp [hD]
    ring
  have hab : a + b = v * (N * C + D * O) + v ^ 2 * P := by
    rw [ha, hb]
    dsimp [P]
    ring
  have hL : a + b = v * L := by
    dsimp [a, b, L]
    ring
  have hM : b = v * M := by
    dsimp [b, M]
    ring
  have hfrac : (a + b) / (1 - b) =
      (a + b) + (a + b) * b / (1 - b) := by
    have hs : 1 - b ≠ 0 := hsmall
    field_simp [hs]
    ring
  have hprod : (a + b) * b / (1 - b) =
      v ^ 2 * (L * M / (1 - b)) := by
    rw [hL, hM]
    ring
  change (a + b) / (1 - b) =
    v * (N * C + D * O) + v ^ 2 * (P + L * M / (1 - b))
  rw [hfrac, hprod, hab]
  ring

private lemma p06_remainder_factor_continuousAt (N D C O : ℝ) :
    ContinuousAt (p06_remainder_factor N D C O) 0 := by
  unfold p06_remainder_factor
  fun_prop (disch := norm_num)

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
  dsimp
  let N : ℝ := (p06NumeratorCounterLength n : ℝ)
  let D : ℝ := (p06DenominatorCounterLength n : ℝ)
  let C := p06SecondBarycentricDataCondition problem
  let O := p06SecondBarycentricOneCondition problem
  let remainder : ι → ℝ := fun t =>
    (u t) ^ 2 * p06_remainder_factor N D C O (u t)
  refine ⟨remainder, ?_, ?_⟩
  · have hfac : Filter.Tendsto
        (fun t => p06_remainder_factor N D C O (u t)) l
        (nhds (p06_remainder_factor N D C O 0)) :=
      (p06_remainder_factor_continuousAt N D C O).tendsto.comp hu
    have hfacO : (fun t => p06_remainder_factor N D C O (u t)) =O[l]
        (fun _ => (1 : ℝ)) := hfac.isBigO_one ℝ
    have h := (Asymptotics.isBigO_refl (fun t => (u t) ^ 2) l).mul hfacO
    simpa only [remainder, mul_one] using h
  · have hgammaCont : ContinuousAt
        (fun v : ℝ => gamma v (p06DenominatorCounterLength n)) 0 := by
      unfold gamma
      fun_prop (disch := norm_num)
    have hgamma : Filter.Tendsto
        (fun t => gamma (u t) (p06DenominatorCounterLength n)) l (nhds 0) := by
      simpa [gamma] using hgammaCont.tendsto.comp hu
    have hsmall : ∀ᶠ t in l,
        gamma (u t) (p06DenominatorCounterLength n) * O < 1 := by
      have hlim : Filter.Tendsto
          (fun t => gamma (u t) (p06DenominatorCounterLength n) * O) l (nhds 0) := by
        simpa using hgamma.mul (tendsto_const_nhds (x := O))
      exact hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hsmall] with t hsmallt
    have hN : 1 - N * u t ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr (run t).numeratorGammaValid
    have hD : 1 - D * u t ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr (run t).denominatorGammaValid
    have hsmall' : 1 - (D * u t / (1 - D * u t)) * O ≠ 0 := by
      apply ne_of_gt
      exact sub_pos.mpr hsmallt
    have hbound := p06_forward_bound_at (run t) hnumerator hdenominator hsmallt
    change p06SecondBarycentricRelativeError (run t) ≤
      ((N * u t / (1 - N * u t)) * C +
        (D * u t / (1 - D * u t)) * O) /
        (1 - (D * u t / (1 - D * u t)) * O) at hbound
    rw [p06_envelope_expansion N D C O (u t) hN hD hsmall'] at hbound
    calc
      p06SecondBarycentricRelativeError (run t) ≤
          u t * (N * C + D * O) + remainder t := hbound
      _ ≤ u t * p06SecondBarycentricFirstOrderCoefficient n C O +
          |remainder t| := by
        change u t * (N * C + D * O) + remainder t ≤
          u t * (N * C + D * O) + |remainder t|
        simpa [add_comm] using
          add_le_add_left (le_abs_self (remainder t)) (u t * (N * C + D * O))

end VSCLReuse

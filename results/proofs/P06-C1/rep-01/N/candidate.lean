import VSCLReuse.P06.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p06_sum_error {m k : ℕ} (u : ℝ) (hu : GammaValid u k)
    (a : Fin m → ℝ) (c : Fin m → P06RelativeErrorCounter u k) :
    |(∑ j, a j * (c j).value) - ∑ j, a j| ≤
      gamma u k * ∑ j, |a j| := by
  calc
    |(∑ j, a j * (c j).value) - ∑ j, a j|
        = |∑ j, a j * ((c j).value - 1)| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ ≤ ∑ j, |a j * ((c j).value - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |a j| * gamma u k := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((c j).gamma_le hu) (abs_nonneg _)
    _ = gamma u k * ∑ j, |a j| := by rw [← Finset.sum_mul]; ring

private theorem p06_ratio_error_bound
    {a b x y en ed : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hen : 0 ≤ en) (hed : 0 ≤ ed) (hed1 : ed < 1)
    (hxn : |x - a| ≤ en * |a|) (hyd : |y - b| ≤ ed * |b|) :
    |a / b - x / y| / |a / b| ≤ (en + ed) / (1 - ed) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  have hbbs : 0 < |b| := abs_pos.mpr hb
  have hden : (1 - ed) * |b| ≤ |y| := by
    have h := abs_sub_abs_le_abs_sub b y
    rw [abs_sub_comm] at h
    nlinarith
  have hypos : 0 < |y| := lt_of_lt_of_le (mul_pos (sub_pos.mpr hed1) hbbs) hden
  have hy : y ≠ 0 := (abs_pos.mp hypos)
  have hnum : |a * y - x * b| ≤ (en + ed) * |a| * |b| := by
    calc
      |a * y - x * b| = |a * (y - b) - (x - a) * b| := by congr 1; ring
      _ ≤ |a * (y - b)| + |(x - a) * b| := abs_sub _ _
      _ ≤ |a| * (ed * |b|) + (en * |a|) * |b| := by
        rw [abs_mul, abs_mul]
        gcongr
      _ = (en + ed) * |a| * |b| := by ring
  have hform : |a / b - x / y| / |a / b| =
      |a * y - x * b| / (|a| * |y|) := by
    rw [div_sub_div _ _ hb hy]
    simp only [abs_div, abs_mul]
    have hcross : a * y - b * x = a * y - x * b := by ring
    rw [hcross]
    field_simp
  rw [hform]
  have hratio :
      |a * y - x * b| / (|a| * |y|) ≤
        ((en + ed) * |a| * |b|) / (|a| * |y|) :=
    div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos habs hypos))
  have hratio2 :
      ((en + ed) * |a| * |b|) / (|a| * |y|) ≤
        ((en + ed) * |a| * |b|) / (|a| * ((1 - ed) * |b|)) := by
    apply div_le_div_of_nonneg_left
    · exact mul_nonneg (mul_nonneg (add_nonneg hen hed) (le_of_lt habs)) (le_of_lt hbbs)
    · exact mul_pos habs (mul_pos (sub_pos.mpr hed1) hbbs)
    · exact mul_le_mul_of_nonneg_left hden (le_of_lt habs)
  have hcancel :
      ((en + ed) * |a| * |b|) / (|a| * ((1 - ed) * |b|)) =
        (en + ed) / (1 - ed) := by
    field_simp
  exact hratio.trans (hratio2.trans_eq hcancel)

private theorem p06_gamma_linear_quadratic
    (K z : ℝ) (hK : 0 ≤ K) (hz : 0 ≤ z) (hsmall : K * z ≤ 1 / 2) :
    0 ≤ K * z / (1 - K * z) ∧
    K * z / (1 - K * z) ≤ 2 * K * z ∧
    K * z / (1 - K * z) ≤ K * z + 2 * K ^ 2 * z ^ 2 := by
  have ha : 0 ≤ K * z := mul_nonneg hK hz
  have hhalf : 0 ≤ 1 - 2 * (K * z) := by linarith
  have hden : 0 < 1 - K * z := by linarith
  constructor
  · exact div_nonneg ha (le_of_lt hden)
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg ha hhalf]
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg (K * z)) hhalf]

private theorem p06_gamma_ratio_quadratic
    (K L C D z : ℝ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hz : 0 ≤ z)
    (hKs : K * z ≤ 1 / 2) (hLs : L * z ≤ 1 / 2)
    (hDs : 2 * (L * D) * z ≤ 1 / 2) :
    let en := (K * z / (1 - K * z)) * C
    let ed := (L * z / (1 - L * z)) * D
    let M := 2 * (K ^ 2 * C + L ^ 2 * D) +
      8 * (K * C + L * D) * (L * D)
    ed < 1 ∧
    (en + ed) / (1 - ed) ≤ z * (K * C + L * D) + M * z ^ 2 := by
  dsimp
  obtain ⟨hgn0, hgnlin, hgnquad⟩ := p06_gamma_linear_quadratic K z hK hz hKs
  obtain ⟨hgd0, hgdlin, hgdquad⟩ := p06_gamma_linear_quadratic L z hL hz hLs
  have hen0 : 0 ≤ (K * z / (1 - K * z)) * C := mul_nonneg hgn0 hC
  have hed0 : 0 ≤ (L * z / (1 - L * z)) * D := mul_nonneg hgd0 hD
  have hedhalf : (L * z / (1 - L * z)) * D ≤ 1 / 2 := by
    calc
      _ ≤ (2 * L * z) * D := mul_le_mul_of_nonneg_right hgdlin hD
      _ = 2 * (L * D) * z := by ring
      _ ≤ 1 / 2 := hDs
  have hed1 : (L * z / (1 - L * z)) * D < 1 := by linarith
  constructor
  · exact hed1
  have hsumlin :
      (K * z / (1 - K * z)) * C + (L * z / (1 - L * z)) * D ≤
        2 * (K * C + L * D) * z := by
    have hn := mul_le_mul_of_nonneg_right hgnlin hC
    have hd := mul_le_mul_of_nonneg_right hgdlin hD
    nlinarith
  have hedlin : (L * z / (1 - L * z)) * D ≤ 2 * (L * D) * z := by
    nlinarith [mul_le_mul_of_nonneg_right hgdlin hD]
  have hsumquad :
      (K * z / (1 - K * z)) * C + (L * z / (1 - L * z)) * D ≤
        (K * C + L * D) * z + 2 * (K ^ 2 * C + L ^ 2 * D) * z ^ 2 := by
    have hn := mul_le_mul_of_nonneg_right hgnquad hC
    have hd := mul_le_mul_of_nonneg_right hgdquad hD
    nlinarith
  have hcross :
      ((K * z / (1 - K * z)) * C + (L * z / (1 - L * z)) * D) *
        ((L * z / (1 - L * z)) * D) ≤
      4 * (K * C + L * D) * (L * D) * z ^ 2 := by
    calc
      _ ≤ (2 * (K * C + L * D) * z) * ((L * z / (1 - L * z)) * D) :=
        mul_le_mul_of_nonneg_right hsumlin hed0
      _ ≤ (2 * (K * C + L * D) * z) * (2 * (L * D) * z) :=
        mul_le_mul_of_nonneg_left hedlin (by positivity)
      _ = 4 * (K * C + L * D) * (L * D) * z ^ 2 := by ring
  have hquot :
      ((K * z / (1 - K * z)) * C + (L * z / (1 - L * z)) * D) /
        (1 - (L * z / (1 - L * z)) * D) ≤
      ((K * z / (1 - K * z)) * C + (L * z / (1 - L * z)) * D) +
        2 * (((K * z / (1 - K * z)) * C +
          (L * z / (1 - L * z)) * D) *
          ((L * z / (1 - L * z)) * D)) := by
    apply (div_le_iff₀ (by linarith :
      0 < 1 - (L * z / (1 - L * z)) * D)).2
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg hen0 hed0) hed0)
      (show 0 ≤ 1 - 2 * ((L * z / (1 - L * z)) * D) by linarith)]
  nlinarith [hquot, hsumquad, hcross]

private theorem p06_computed_eq_counter_sums {n : ℕ}
    (problem : P06SecondBarycentricProblem n) (u : ℝ)
    (run : P06SecondBarycentricExecution problem u) :
    p06SecondBarycentricComputed run =
      (∑ j : Fin (n + 1),
        (p06DirectBarycentricCoefficient problem.nodes problem.x j * problem.data j) *
          (run.numeratorCounter j).value) /
      (∑ j : Fin (n + 1),
        p06DirectBarycentricCoefficient problem.nodes problem.x j *
          (run.denominatorCounter j).value) := by
  have hn :
      (∑ j : Fin (n + 1),
        p06DirectBarycentricCoefficient problem.nodes problem.x j *
          (run.weightCounter j).value * problem.data j *
            (run.numeratorEvaluationCounter j).value) * run.quotientCounter.value =
      ∑ j : Fin (n + 1),
        (p06DirectBarycentricCoefficient problem.nodes problem.x j * problem.data j) *
          (run.numeratorCounter j).value := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.numeratorCounter_eq]
    ring
  have hd :
      (∑ j : Fin (n + 1),
        p06DirectBarycentricCoefficient problem.nodes problem.x j *
          (run.weightCounter j).value *
            (run.denominatorEvaluationCounter j).value) =
      ∑ j : Fin (n + 1),
        p06DirectBarycentricCoefficient problem.nodes problem.x j *
          (run.denominatorCounter j).value := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.denominatorCounter_eq]
    ring
  unfold p06SecondBarycentricComputed
  rw [div_mul_eq_mul_div, hn, hd]

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
  let a : Fin (n + 1) → ℝ := fun j =>
    p06DirectBarycentricCoefficient problem.nodes problem.x j * problem.data j
  let b : Fin (n + 1) → ℝ := fun j =>
    p06DirectBarycentricCoefficient problem.nodes problem.x j
  let N : ℝ := ∑ j, a j
  let D : ℝ := ∑ j, b j
  let C : ℝ := (∑ j, |a j|) / |N|
  let E : ℝ := (∑ j, |b j|) / |D|
  let K : ℝ := (p06NumeratorCounterLength n : ℝ)
  let L : ℝ := (p06DenominatorCounterLength n : ℝ)
  let M : ℝ := 2 * (K ^ 2 * C + L ^ 2 * E) +
    8 * (K * C + L * E) * (L * E)
  have hN : N ≠ 0 := by
    simpa [N, a, p06SecondBarycentricNumerator, p06InterpolationValue]
      using hnumerator
  have hD : D ≠ 0 := by
    simpa [D, b, p06SecondBarycentricDenominator, p06InterpolationValue]
      using hdenominator
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hCN : C * |N| = ∑ j, |a j| := by
    dsimp [C]
    field_simp
  have hED : E * |D| = ∑ j, |b j| := by
    dsimp [E]
    field_simp
  have hC_id : C = p06SecondBarycentricDataCondition problem := by
    rfl
  have hE_id : E = p06SecondBarycentricOneCondition problem := by
    simp [E, D, b, p06SecondBarycentricOneCondition, p06Condition,
      p06InterpolationValue]
  have hKsmall : ∀ᶠ t in l, K * u t ≤ 1 / 2 := by
    have ht : Filter.Tendsto (fun t => K * u t) l (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hu :
        Filter.Tendsto (fun t => K * u t) l (nhds (K * 0)))
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hLsmall : ∀ᶠ t in l, L * u t ≤ 1 / 2 := by
    have ht : Filter.Tendsto (fun t => L * u t) l (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hu :
        Filter.Tendsto (fun t => L * u t) l (nhds (L * 0)))
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hEsmall : ∀ᶠ t in l, 2 * (L * E) * u t ≤ 1 / 2 := by
    have ht : Filter.Tendsto (fun t => (2 * (L * E)) * u t) l (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hu :
        Filter.Tendsto (fun t => (2 * (L * E)) * u t) l
          (nhds ((2 * (L * E)) * 0)))
    exact ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨fun t => M * (u t) ^ 2, ?_, ?_⟩
  · exact Asymptotics.isBigO_const_mul_self M (fun t => (u t) ^ 2) l
  filter_upwards [hKsmall, hLsmall, hEsmall] with t hKt hLt hEt
  let X : ℝ := ∑ j, a j * ((run t).numeratorCounter j).value
  let Y : ℝ := ∑ j, b j * ((run t).denominatorCounter j).value
  have hNX : |X - N| ≤ (gamma (u t) (p06NumeratorCounterLength n) * C) * |N| := by
    calc
      _ ≤ gamma (u t) (p06NumeratorCounterLength n) * ∑ j, |a j| :=
        p06_sum_error (u t) (run t).numeratorGammaValid a (run t).numeratorCounter
      _ = (gamma (u t) (p06NumeratorCounterLength n) * C) * |N| := by
        rw [← hCN]
        ring
  have hDY : |Y - D| ≤ (gamma (u t) (p06DenominatorCounterLength n) * E) * |D| := by
    calc
      _ ≤ gamma (u t) (p06DenominatorCounterLength n) * ∑ j, |b j| :=
        p06_sum_error (u t) (run t).denominatorGammaValid b (run t).denominatorCounter
      _ = (gamma (u t) (p06DenominatorCounterLength n) * E) * |D| := by
        rw [← hED]
        ring
  have hgammaN : gamma (u t) (p06NumeratorCounterLength n) =
      K * u t / (1 - K * u t) := rfl
  have hgammaD : gamma (u t) (p06DenominatorCounterLength n) =
      L * u t / (1 - L * u t) := rfl
  obtain ⟨hgn0, _, _⟩ :=
    p06_gamma_linear_quadratic K (u t) hK (run t).u_nonneg hKt
  obtain ⟨hgd0, _, _⟩ :=
    p06_gamma_linear_quadratic L (u t) hL (run t).u_nonneg hLt
  have hrel : p06SecondBarycentricRelativeError (run t) =
      |N / D - X / Y| / |N / D| := by
    unfold p06SecondBarycentricRelativeError p06SecondBarycentricExact
    rw [p06_computed_eq_counter_sums]
    simp [N, D, X, Y, a, b, p06SecondBarycentricNumerator,
      p06SecondBarycentricDenominator, p06InterpolationValue]
  have hbound : p06SecondBarycentricRelativeError (run t) ≤
      ((gamma (u t) (p06NumeratorCounterLength n) * C) +
        (gamma (u t) (p06DenominatorCounterLength n) * E)) /
        (1 - gamma (u t) (p06DenominatorCounterLength n) * E) := by
    rw [hrel]
    apply p06_ratio_error_bound hN hD
    · exact mul_nonneg (by simpa [hgammaN] using hgn0) hC
    · exact mul_nonneg (by simpa [hgammaD] using hgd0) hE
    · rw [hgammaD]
      exact (p06_gamma_ratio_quadratic K L C E (u t)
        hK hL hC hE (run t).u_nonneg hKt hLt hEt).1
    · exact hNX
    · exact hDY
  have hquadratic :=
    (p06_gamma_ratio_quadratic K L C E (u t)
      hK hL hC hE (run t).u_nonneg hKt hLt hEt).2
  rw [hgammaN, hgammaD] at hbound
  have hfinal : p06SecondBarycentricRelativeError (run t) ≤
      u t * (K * C + L * E) + |M * (u t) ^ 2| := by
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hu2 : 0 ≤ (u t) ^ 2 := sq_nonneg _
    rw [abs_of_nonneg (mul_nonneg hM hu2)]
    dsimp [M] at hquadratic ⊢
    nlinarith
  simpa [hC_id, hE_id, K, L, p06SecondBarycentricFirstOrderCoefficient]
    using hfinal

end VSCLReuse

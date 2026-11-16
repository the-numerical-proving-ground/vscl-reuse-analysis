import VSCLReuse.P06.Definitions

namespace VSCLReuse

private lemma p06_sum_perturb {α : Type*} [Fintype α]
    (c e : α → ℝ) (g : ℝ)
    (he : ∀ j, |e j - 1| ≤ g) :
    |(∑ j, c j * e j) - ∑ j, c j| ≤ g * ∑ j, |c j| := by
  have heq : (∑ j, c j * e j) - ∑ j, c j = ∑ j, c j * (e j - 1) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext j
    ring
  rw [heq]
  calc
    |∑ j, c j * (e j - 1)| ≤ ∑ j, |c j * (e j - 1)| :=
      Finset.abs_sum_le_sum_abs (fun j => c j * (e j - 1)) _
    _ ≤ ∑ j, g * |c j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      calc
        |c j| * |e j - 1| ≤ |c j| * g := mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)
        _ = g * |c j| := mul_comm _ _
    _ = g * ∑ j, |c j| := by rw [Finset.mul_sum]

private lemma p06_normalized_ratio_bound
    (a b α β : ℝ) (ha : |a| ≤ α) (hb : |b| ≤ β) (hβ : β < 1) :
    |1 - (1 + a) / (1 + b)| ≤ (α + β) / (1 - β) := by
  have hbp : 0 < 1 + b := by have := neg_abs_le b; linarith
  have hβp : 0 < 1 - β := by linarith
  have hαβ : 0 ≤ α + β := by nlinarith [abs_nonneg a, abs_nonneg b]
  have hden : 1 - β ≤ 1 + b := by have := neg_abs_le b; linarith
  have hnum : |b - a| ≤ α + β := by
    calc
      |b - a| ≤ |b| + |a| := abs_sub_le _ 0 _ |>.trans_eq (by simp)
      _ ≤ β + α := add_le_add hb ha
      _ = α + β := add_comm _ _
  have hdiv : |b - a| / (1 + b) ≤ (α + β) / (1 - β) := by
    apply (div_le_div_iff₀ hbp hβp).2
    calc
      |b - a| * (1 - β) ≤ (α + β) * (1 - β) :=
        mul_le_mul_of_nonneg_right hnum hβp.le
      _ ≤ (α + β) * (1 + b) :=
        mul_le_mul_of_nonneg_left hden hαβ
  have heq : 1 - (1 + a) / (1 + b) = (b - a) / (1 + b) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hbp]
  exact hdiv

private lemma p06_fraction_perturb
    (N D Nh Dh α β : ℝ)
    (hN : N ≠ 0) (hD : D ≠ 0)
    (hNh : |Nh - N| ≤ α * |N|)
    (hDh : |Dh - D| ≤ β * |D|)
    (hβ : β < 1) :
    |N / D - Nh / Dh| / |N / D| ≤ (α + β) / (1 - β) := by
  let a := (Nh - N) / N
  let b := (Dh - D) / D
  have hNa : Nh = N * (1 + a) := by
    dsimp [a]
    field_simp
    ring
  have hDb : Dh = D * (1 + b) := by
    dsimp [b]
    field_simp
    ring
  have ha : |a| ≤ α := by
    dsimp [a]
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hN)).2 (by simpa [mul_comm] using hNh)
  have hb : |b| ≤ β := by
    dsimp [b]
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr hD)).2 (by simpa [mul_comm] using hDh)
  have hbp : 0 < 1 + b := by have := neg_abs_le b; linarith
  have hDhne : Dh ≠ 0 := by rw [hDb]; exact mul_ne_zero hD (ne_of_gt hbp)
  have hq : (N / D - Nh / Dh) / (N / D) = 1 - (1 + a) / (1 + b) := by
    rw [hNa, hDb]
    field_simp
  rw [← abs_div, hq]
  exact p06_normalized_ratio_bound a b α β ha hb hβ

private lemma p06_gamma_bounds (x : ℝ) (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    x / (1 - x) ≤ 2 * x ∧ x / (1 - x) ≤ x + 2 * x ^ 2 := by
  have hden : 0 < 1 - x := by linarith
  have hfactor : 0 ≤ 1 - 2 * x := by linarith
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hx hfactor]
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg x) hfactor]

private lemma p06_quadratic_ratio
    (u α β C D b : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hnum : α + β ≤ C * u + D * u ^ 2)
    (hβbound : β ≤ 2 * b * u)
    (hsmall : 2 * b * u ≤ 1 / 2) :
    β < 1 ∧ (α + β) / (1 - β) ≤
      C * u + (D + 4 * b * (C + D)) * u ^ 2 := by
  have hβhalf : β ≤ 1 / 2 := le_trans hβbound hsmall
  have hβlt : β < 1 := by linarith
  have hden : 0 < 1 - β := by linarith
  have hfactor : 0 ≤ 1 - 2 * β := by linarith
  have hsum : 0 ≤ α + β := add_nonneg hα hβ
  have hrecip : (α + β) / (1 - β) ≤ (α + β) * (1 + 2 * β) := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hsum (mul_nonneg hβ hfactor)]
  have hfactorp : 0 ≤ 1 + 2 * β := by linarith
  have hfactorle : 1 + 2 * β ≤ 1 + 4 * b * u := by linarith
  have hnumpos : 0 ≤ C * u + D * u ^ 2 := by positivity
  have hprod : (α + β) * (1 + 2 * β) ≤
      (C * u + D * u ^ 2) * (1 + 4 * b * u) := by
    calc
      _ ≤ (C * u + D * u ^ 2) * (1 + 2 * β) :=
        mul_le_mul_of_nonneg_right hnum hfactorp
      _ ≤ (C * u + D * u ^ 2) * (1 + 4 * b * u) :=
        mul_le_mul_of_nonneg_left hfactorle hnumpos
  have hu3 : u ^ 3 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
  have hpoly : (C * u + D * u ^ 2) * (1 + 4 * b * u) ≤
      C * u + (D + 4 * b * (C + D)) * u ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hu3 (by positivity : 0 ≤ 4 * b * D)]
  exact ⟨hβlt, (hrecip.trans hprod).trans hpoly⟩

private lemma p06_execution_fraction {n : ℕ}
    {problem : P06SecondBarycentricProblem n} {u : ℝ}
    (run : P06SecondBarycentricExecution problem u) :
    p06SecondBarycentricComputed run =
      (∑ j, (p06DirectBarycentricCoefficient problem.nodes problem.x j * problem.data j) *
        (run.numeratorCounter j).value) /
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        (run.denominatorCounter j).value) := by
  let c := p06DirectBarycentricCoefficient problem.nodes problem.x
  have hn : (∑ j, (c j * problem.data j) * (run.numeratorCounter j).value) =
      (∑ j, c j * (run.weightCounter j).value * problem.data j *
        (run.numeratorEvaluationCounter j).value) * run.quotientCounter.value := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.numeratorCounter_eq j]
    ring
  have hd : (∑ j, c j * (run.denominatorCounter j).value) =
      ∑ j, c j * (run.weightCounter j).value *
        (run.denominatorEvaluationCounter j).value := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [run.denominatorCounter_eq j]
    ring
  change ((∑ j, c j * (run.weightCounter j).value * problem.data j *
        (run.numeratorEvaluationCounter j).value) /
      (∑ j, c j * (run.weightCounter j).value *
        (run.denominatorEvaluationCounter j).value)) *
      run.quotientCounter.value = _
  rw [hn, hd]
  ring

private lemma p06_execution_bound {n : ℕ}
    (problem : P06SecondBarycentricProblem n) (u : ℝ)
    (run : P06SecondBarycentricExecution problem u)
    (hN : p06SecondBarycentricNumerator problem ≠ 0)
    (hD : p06SecondBarycentricDenominator problem ≠ 0)
    (hβ : gamma u (p06DenominatorCounterLength n) *
      p06SecondBarycentricOneCondition problem < 1) :
    p06SecondBarycentricRelativeError run ≤
      (gamma u (p06NumeratorCounterLength n) *
          p06SecondBarycentricDataCondition problem +
        gamma u (p06DenominatorCounterLength n) *
          p06SecondBarycentricOneCondition problem) /
      (1 - gamma u (p06DenominatorCounterLength n) *
          p06SecondBarycentricOneCondition problem) := by
  let c := p06DirectBarycentricCoefficient problem.nodes problem.x
  let N := p06SecondBarycentricNumerator problem
  let D := p06SecondBarycentricDenominator problem
  let Nh := ∑ j, (c j * problem.data j) * (run.numeratorCounter j).value
  let Dh := ∑ j, c j * (run.denominatorCounter j).value
  let ga := gamma u (p06NumeratorCounterLength n)
  let gb := gamma u (p06DenominatorCounterLength n)
  have hn_sum : |Nh - N| ≤ ga * ∑ j, |c j * problem.data j| := by
    simpa [Nh, N, ga, p06SecondBarycentricNumerator, p06InterpolationValue, c] using
      p06_sum_perturb (fun j => c j * problem.data j)
        (fun j => (run.numeratorCounter j).value) ga
        (fun j => (run.numeratorCounter j).gamma_le run.numeratorGammaValid)
  have hd_sum : |Dh - D| ≤ gb * ∑ j, |c j| := by
    simpa [Dh, D, gb, p06SecondBarycentricDenominator, p06InterpolationValue, c] using
      p06_sum_perturb c (fun j => (run.denominatorCounter j).value) gb
        (fun j => (run.denominatorCounter j).gamma_le run.denominatorGammaValid)
  have hcdata : p06SecondBarycentricDataCondition problem * |N| =
      ∑ j, |c j * problem.data j| := by
    unfold p06SecondBarycentricDataCondition p06Condition
    change ((∑ j, |c j * problem.data j|) / |N|) * |N| = _
    field_simp [show |N| ≠ 0 from abs_ne_zero.mpr hN]
  have hcone : p06SecondBarycentricOneCondition problem * |D| =
      ∑ j, |c j| := by
    unfold p06SecondBarycentricOneCondition p06Condition
    change ((∑ j, |c j * (1 : ℝ)|) / |D|) * |D| = _
    simp only [mul_one]
    field_simp [show |D| ≠ 0 from abs_ne_zero.mpr hD]
  have hNh : |Nh - N| ≤ (ga * p06SecondBarycentricDataCondition problem) * |N| := by
    rw [mul_assoc, hcdata]
    exact hn_sum
  have hDh : |Dh - D| ≤ (gb * p06SecondBarycentricOneCondition problem) * |D| := by
    rw [mul_assoc, hcone]
    exact hd_sum
  change |N / D - p06SecondBarycentricComputed run| / |N / D| ≤ _
  rw [p06_execution_fraction]
  exact p06_fraction_perturb N D Nh Dh
    (ga * p06SecondBarycentricDataCondition problem)
    (gb * p06SecondBarycentricOneCondition problem)
    hN hD hNh hDh hβ

private lemma p06_gamma_ratio_quadratic
    (u A B cd co : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcd : 0 ≤ cd) (hco : 0 ≤ co)
    (hAsmall : A * u ≤ 1 / 2)
    (hBsmall : B * u ≤ 1 / 2)
    (hcondsmall : 2 * B * co * u ≤ 1 / 2) :
    let ga := (A * u) / (1 - A * u)
    let gb := (B * u) / (1 - B * u)
    let C := A * cd + B * co
    let D := 2 * (A ^ 2 * cd + B ^ 2 * co)
    let b := B * co
    gb * co < 1 ∧
      (ga * cd + gb * co) / (1 - gb * co) ≤
        u * C + (D + 4 * b * (C + D)) * u ^ 2 := by
  dsimp
  have hAu : 0 ≤ A * u := mul_nonneg hA hu
  have hBu : 0 ≤ B * u := mul_nonneg hB hu
  obtain ⟨hga1, hga2⟩ := p06_gamma_bounds (A * u) hAu hAsmall
  obtain ⟨hgb1, hgb2⟩ := p06_gamma_bounds (B * u) hBu hBsmall
  have hga0 : 0 ≤ (A * u) / (1 - A * u) :=
    div_nonneg hAu (by linarith)
  have hgb0 : 0 ≤ (B * u) / (1 - B * u) :=
    div_nonneg hBu (by linarith)
  have hα : 0 ≤ (A * u / (1 - A * u)) * cd := mul_nonneg hga0 hcd
  have hβ : 0 ≤ (B * u / (1 - B * u)) * co := mul_nonneg hgb0 hco
  have hC : 0 ≤ A * cd + B * co := add_nonneg (mul_nonneg hA hcd) (mul_nonneg hB hco)
  have hD : 0 ≤ 2 * (A ^ 2 * cd + B ^ 2 * co) := by positivity
  have hb : 0 ≤ B * co := mul_nonneg hB hco
  have hga2' : A * u / (1 - A * u) ≤ A * u + 2 * A ^ 2 * u ^ 2 := by
    calc
      _ ≤ A * u + 2 * (A * u) ^ 2 := hga2
      _ = _ := by ring
  have hgb2' : B * u / (1 - B * u) ≤ B * u + 2 * B ^ 2 * u ^ 2 := by
    calc
      _ ≤ B * u + 2 * (B * u) ^ 2 := hgb2
      _ = _ := by ring
  have hnum :
      (A * u / (1 - A * u)) * cd + (B * u / (1 - B * u)) * co ≤
      (A * cd + B * co) * u +
        (2 * (A ^ 2 * cd + B ^ 2 * co)) * u ^ 2 := by
    calc
      _ ≤ (A * u + 2 * A ^ 2 * u ^ 2) * cd +
          (B * u + 2 * B ^ 2 * u ^ 2) * co :=
        add_le_add (mul_le_mul_of_nonneg_right hga2' hcd)
          (mul_le_mul_of_nonneg_right hgb2' hco)
      _ = _ := by ring
  have hβbound : (B * u / (1 - B * u)) * co ≤ 2 * (B * co) * u := by
    calc
      _ ≤ (2 * (B * u)) * co := mul_le_mul_of_nonneg_right hgb1 hco
      _ = _ := by ring
  have hresult := p06_quadratic_ratio u
    ((A * u / (1 - A * u)) * cd)
    ((B * u / (1 - B * u)) * co)
    (A * cd + B * co)
    (2 * (A ^ 2 * cd + B ^ 2 * co))
    (B * co)
    hu hu1 hα hβ hC hD hb hnum hβbound (by nlinarith [hcondsmall])
  convert hresult using 1 <;> ring

private lemma p06_condition_nonneg {n : ℕ} (ell f : Fin n → ℝ) :
    0 ≤ p06Condition ell f := by
  unfold p06Condition
  exact div_nonneg (Finset.sum_nonneg (fun i hi => abs_nonneg _)) (abs_nonneg _)

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
  let cd := p06SecondBarycentricDataCondition problem
  let co := p06SecondBarycentricOneCondition problem
  let A : ℝ := p06NumeratorCounterLength n
  let B : ℝ := p06DenominatorCounterLength n
  let C := A * cd + B * co
  let D := 2 * (A ^ 2 * cd + B ^ 2 * co)
  let b := B * co
  let K := D + 4 * b * (C + D)
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hcd : 0 ≤ cd := p06_condition_nonneg _ _
  have hco : 0 ≤ co := p06_condition_nonneg _ _
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hA hcd) (mul_nonneg hB hco)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : 0 ≤ b := mul_nonneg hB hco
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hu1 : ∀ᶠ t in l, u t ≤ 1 :=
    (Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1) hu).mono
      (fun t ht => ht.le)
  have hAu_tend : Filter.Tendsto (fun t => A * u t) l (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hu :
      Filter.Tendsto (fun t => A * u t) l (nhds (A * 0)))
  have hBu_tend : Filter.Tendsto (fun t => B * u t) l (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hu :
      Filter.Tendsto (fun t => B * u t) l (nhds (B * 0)))
  have hbu_tend : Filter.Tendsto (fun t => (2 * B * co) * u t) l (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hu :
      Filter.Tendsto (fun t => (2 * B * co) * u t) l
        (nhds ((2 * B * co) * 0)))
  have hAu : ∀ᶠ t in l, A * u t ≤ 1 / 2 :=
    (Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
      hAu_tend).mono (fun t ht => ht.le)
  have hBu : ∀ᶠ t in l, B * u t ≤ 1 / 2 :=
    (Filter.Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
      hBu_tend).mono (fun t ht => ht.le)
  have hbu : ∀ᶠ t in l, 2 * B * co * u t ≤ 1 / 2 := by
    filter_upwards [Filter.Tendsto.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2) hbu_tend] with t ht
    convert ht.le using 1 <;> ring
  refine ⟨fun t => K * (u t) ^ 2, ?_, ?_⟩
  · exact Asymptotics.isBigO_const_mul_self K (fun t => (u t) ^ 2) l
  · filter_upwards [hu1, hAu, hBu, hbu] with t ht1 htA htB htbu
    have hu0 : 0 ≤ u t := (run t).u_nonneg
    have hratio := p06_gamma_ratio_quadratic (u t) A B cd co
      hu0 ht1 hA hB hcd hco htA htB htbu
    have hratio' :
        gamma (u t) (p06DenominatorCounterLength n) * co < 1 ∧
        (gamma (u t) (p06NumeratorCounterLength n) * cd +
          gamma (u t) (p06DenominatorCounterLength n) * co) /
          (1 - gamma (u t) (p06DenominatorCounterLength n) * co) ≤
          u t * C + K * (u t) ^ 2 := by
      simpa [A, B, C, D, b, K, gamma, mul_assoc] using hratio
    change p06SecondBarycentricRelativeError (run t) ≤
      u t * C + |K * (u t) ^ 2|
    rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]
    exact (p06_execution_bound problem (u t) (run t)
      hnumerator hdenominator hratio'.1).trans hratio'.2

end VSCLReuse

import VSCLReuse.P06.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p06_sum_error {m : ℕ} (a c : Fin m → ℝ) (g : ℝ)
    (hc : ∀ j, |c j - 1| ≤ g) :
    |(∑ j, a j * c j) - ∑ j, a j| ≤ g * ∑ j, |a j| := by
  have hsum : (∑ j, a j * c j) - ∑ j, a j = ∑ j, a j * (c j - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  calc
    |∑ j, a j * (c j - 1)| ≤ ∑ j, |a j * (c j - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |a j| * |c j - 1| := by simp only [abs_mul]
    _ ≤ ∑ j, |a j| * g := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hc j) (abs_nonneg _)
    _ = g * ∑ j, |a j| := by rw [Finset.mul_sum]; simp [mul_comm]

private theorem p06_ratio_bound (N D E F : ℝ) (hN : N ≠ 0) (hD : D ≠ 0)
    (hF : |F| / |D| < 1) :
    |N / D - (N + E) / (D + F)| / |N / D| ≤
      (|E| / |N| + |F| / |D|) / (1 - |F| / |D|) := by
  have hDpos : 0 < |D| := abs_pos.mpr hD
  have hFlt : |F| < |D| := (div_lt_one hDpos).mp hF
  have htri : |D| ≤ |D + F| + |F| := by
    have h := abs_add_le (D + F) (-F)
    simpa [add_assoc] using h
  have hDF : D + F ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at htri
    linarith
  have hND : N / D ≠ 0 := div_ne_zero hN hD
  have hmain : (N / D - (N + E) / (D + F)) / (N / D) =
      (F / D - E / N) / (1 + F / D) := by
    field_simp [hN, hD, hDF]
    ring
  have hb : |F / D| < 1 := by simpa only [abs_div, abs_abs] using hF
  have hsmall : 0 < 1 - |F / D| := by linarith
  have hden : 1 - |F / D| ≤ |1 + F / D| := by
    have h := abs_add_le (1 + F / D) (-(F / D))
    simp only [add_neg_cancel_right, abs_one, abs_neg] at h
    linarith
  have hdenpos : 0 < |1 + F / D| := lt_of_lt_of_le hsmall hden
  have hnum : |F / D - E / N| ≤ |F / D| + |E / N| := abs_sub _ _
  rw [← abs_div, hmain, abs_div]
  calc
    |F / D - E / N| / |1 + F / D| ≤
        (|F / D| + |E / N|) / |1 + F / D| :=
      div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (|F / D| + |E / N|) / (1 - |F / D|) :=
      div_le_div_of_nonneg_left (by positivity) hsmall hden
    _ = (|E| / |N| + |F| / |D|) / (1 - |F| / |D|) := by
      simp only [abs_div, add_comm]

private theorem p06_gamma_bounds (k : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hsmall : (k : ℝ) * u ≤ 1 / 2) :
    0 ≤ gamma u k ∧
      gamma u k ≤ 2 * (k : ℝ) * u ∧
      gamma u k ≤ (k : ℝ) * u + 2 * (k : ℝ) ^ 2 * u ^ 2 := by
  let q : ℝ := (k : ℝ) * u
  have hq : 0 ≤ q := mul_nonneg (Nat.cast_nonneg _) hu
  have hqsmall : q ≤ 1 / 2 := hsmall
  have hden : 0 < 1 - q := by linarith
  have hq2 : 2 * q ^ 2 ≤ q := by
    have h := mul_le_mul_of_nonneg_right hqsmall hq
    nlinarith
  have hq3 : 2 * q ^ 3 ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hqsmall (sq_nonneg q)
    nlinarith
  have hqfirst : q / (1 - q) ≤ 2 * q := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hqsecond : q / (1 - q) ≤ q + 2 * q ^ 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  dsimp [gamma, q] at *
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hden.le
  constructor
  · convert hqfirst using 1; ring
  · convert hqsecond using 1; ring

private theorem p06_scalar_bound (u α β α₂ β₂ x y : ℝ)
    (hu : 0 ≤ u) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2)
    (hxlinear : x ≤ 2 * α * u) (hylinear : y ≤ 2 * β * u)
    (hxquadratic : x ≤ α * u + α₂ * u ^ 2)
    (hyquadratic : y ≤ β * u + β₂ * u ^ 2) :
    (x + y) / (1 - y) ≤
      u * (α + β) + (α₂ + β₂ + 8 * (α + β) * β) * u ^ 2 := by
  have hden : 0 < 1 - y := by linarith
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hsum : x + y ≤ 2 * (α + β) * u := by nlinarith
  have hprod : (x + y) * y ≤ (2 * (α + β) * u) * (2 * β * u) := by
    calc
      (x + y) * y ≤ (2 * (α + β) * u) * y :=
        mul_le_mul_of_nonneg_right hsum hy
      _ ≤ (2 * (α + β) * u) * (2 * β * u) :=
        mul_le_mul_of_nonneg_left hylinear (by positivity)
  have hdiv : (x + y) / (1 - y) ≤ (x + y) + 2 * (x + y) * y := by
    apply (div_le_iff₀ hden).2
    have htmp : 0 ≤ (x + y) * y * (1 - 2 * y) :=
      mul_nonneg (mul_nonneg hxy hy) (by linarith)
    nlinarith
  calc
    (x + y) / (1 - y) ≤ (x + y) + 2 * (x + y) * y := hdiv
    _ ≤ u * (α + β) + (α₂ + β₂ + 8 * (α + β) * β) * u ^ 2 := by
      nlinarith [hprod, hxquadratic, hyquadratic]

private theorem p06_computed_eq {n : ℕ}
    (problem : P06SecondBarycentricProblem n) (u : ℝ)
    (execution : P06SecondBarycentricExecution problem u) :
    p06SecondBarycentricComputed execution =
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
          problem.data j * (execution.numeratorCounter j).value) /
      (∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
          (execution.denominatorCounter j).value) := by
  let q := execution.quotientCounter.value
  let rawN := ∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
    (execution.weightCounter j).value * problem.data j *
      (execution.numeratorEvaluationCounter j).value
  let rawD := ∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
    (execution.weightCounter j).value *
      (execution.denominatorEvaluationCounter j).value
  have hN : rawN * q =
      ∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        problem.data j * (execution.numeratorCounter j).value := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [execution.numeratorCounter_eq j]
    dsimp [q, rawN]
    ring
  have hD : rawD =
      ∑ j, p06DirectBarycentricCoefficient problem.nodes problem.x j *
        (execution.denominatorCounter j).value := by
    apply Finset.sum_congr rfl
    intro j _
    rw [execution.denominatorCounter_eq j]
    ring
  change rawN / rawD * q = _
  calc
    rawN / rawD * q = rawN * q / rawD := by ring
    _ = _ := by rw [hN, hD]

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
  let coeff : Fin (n + 1) → ℝ :=
    p06DirectBarycentricCoefficient problem.nodes problem.x
  let a : Fin (n + 1) → ℝ := fun j => coeff j * problem.data j
  let b : Fin (n + 1) → ℝ := fun j => coeff j * 1
  let N : ℝ := ∑ j, a j
  let D : ℝ := ∑ j, b j
  let SN : ℝ := ∑ j, |a j|
  let SD : ℝ := ∑ j, |b j|
  let CN : ℝ := SN / |N|
  let CD : ℝ := SD / |D|
  let A : ℝ := (p06NumeratorCounterLength n : ℝ)
  let B : ℝ := (p06DenominatorCounterLength n : ℝ)
  let α : ℝ := A * CN
  let β : ℝ := B * CD
  let α₂ : ℝ := 2 * A ^ 2 * CN
  let β₂ : ℝ := 2 * B ^ 2 * CD
  let C : ℝ := α₂ + β₂ + 8 * (α + β) * β
  let E : ι → ℝ := fun t =>
    (∑ j, a j * ((run t).numeratorCounter j).value) - N
  let F : ι → ℝ := fun t =>
    (∑ j, b j * ((run t).denominatorCounter j).value) - D
  have hN : N ≠ 0 := by
    simpa [N, a, coeff, p06SecondBarycentricNumerator,
      p06InterpolationValue] using hnumerator
  have hD : D ≠ 0 := by
    simpa [D, b, coeff, p06SecondBarycentricDenominator,
      p06InterpolationValue] using hdenominator
  have hNpos : 0 < |N| := abs_pos.mpr hN
  have hDpos : 0 < |D| := abs_pos.mpr hD
  have hCN : p06SecondBarycentricDataCondition problem = CN := rfl
  have hCD : p06SecondBarycentricOneCondition problem = CD := rfl
  have hExact : p06SecondBarycentricExact problem = N / D := rfl
  have hCNnonneg : 0 ≤ CN := by dsimp [CN, SN]; positivity
  have hCDnonneg : 0 ≤ CD := by dsimp [CD, SD]; positivity
  have hAnonneg : 0 ≤ A := Nat.cast_nonneg _
  have hBnonneg : 0 ≤ B := Nat.cast_nonneg _
  have hαnonneg : 0 ≤ α := mul_nonneg hAnonneg hCNnonneg
  have hβnonneg : 0 ≤ β := mul_nonneg hBnonneg hCDnonneg
  have hCnonneg : 0 ≤ C := by
    dsimp [C, α₂, β₂]
    positivity
  have hE (t : ι) : |E t| ≤ gamma (u t) (p06NumeratorCounterLength n) * SN := by
    simpa only [E, N, SN] using
      (p06_sum_error a (fun j => ((run t).numeratorCounter j).value)
        (gamma (u t) (p06NumeratorCounterLength n))
        (fun j => ((run t).numeratorCounter j).gamma_le
          (run t).numeratorGammaValid))
  have hF (t : ι) : |F t| ≤ gamma (u t) (p06DenominatorCounterLength n) * SD := by
    simpa only [F, D, SD] using
      (p06_sum_error b (fun j => ((run t).denominatorCounter j).value)
        (gamma (u t) (p06DenominatorCounterLength n))
        (fun j => ((run t).denominatorCounter j).gamma_le
          (run t).denominatorGammaValid))
  have hcomp (t : ι) : p06SecondBarycentricComputed (run t) =
      (N + E t) / (D + F t) := by
    rw [p06_computed_eq problem (u t) (run t)]
    have hnum : N + E t =
        ∑ j, a j * ((run t).numeratorCounter j).value := by
      dsimp [E]
      ring
    have hden : D + F t =
        ∑ j, b j * ((run t).denominatorCounter j).value := by
      dsimp [F]
      ring
    rw [hnum, hden]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b, coeff]
    ring
  have hAtend : Filter.Tendsto (fun t => A * u t) l (nhds 0) := by
    simpa using hu.const_mul A
  have hBtend : Filter.Tendsto (fun t => B * u t) l (nhds 0) := by
    simpa using hu.const_mul B
  have hβtend : Filter.Tendsto (fun t => 2 * β * u t) l (nhds 0) := by
    simpa [mul_assoc] using hu.const_mul (2 * β)
  have hAev : ∀ᶠ t in l, A * u t ≤ 1 / 2 :=
    hAtend.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hBev : ∀ᶠ t in l, B * u t ≤ 1 / 2 :=
    hBtend.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hβev : ∀ᶠ t in l, 2 * β * u t ≤ 1 / 2 :=
    hβtend.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨fun t => C * (u t) ^ 2, ?_, ?_⟩
  · exact Asymptotics.isBigO_const_mul_self C (fun t => (u t) ^ 2) l
  filter_upwards [hAev, hBev, hβev] with t hAsmall hBsmall hβsmall
  have hγA := p06_gamma_bounds (p06NumeratorCounterLength n) (u t)
    (run t).u_nonneg hAsmall
  have hγB := p06_gamma_bounds (p06DenominatorCounterLength n) (u t)
    (run t).u_nonneg hBsmall
  let x : ℝ := |E t| / |N|
  let y : ℝ := |F t| / |D|
  have hx : 0 ≤ x := div_nonneg (abs_nonneg _) hNpos.le
  have hy : 0 ≤ y := div_nonneg (abs_nonneg _) hDpos.le
  have hxγ : x ≤ gamma (u t) (p06NumeratorCounterLength n) * CN := by
    calc
      x ≤ (gamma (u t) (p06NumeratorCounterLength n) * SN) / |N| :=
        div_le_div_of_nonneg_right (hE t) hNpos.le
      _ = gamma (u t) (p06NumeratorCounterLength n) * CN := by
        dsimp [CN]
        ring
  have hyγ : y ≤ gamma (u t) (p06DenominatorCounterLength n) * CD := by
    calc
      y ≤ (gamma (u t) (p06DenominatorCounterLength n) * SD) / |D| :=
        div_le_div_of_nonneg_right (hF t) hDpos.le
      _ = gamma (u t) (p06DenominatorCounterLength n) * CD := by
        dsimp [CD]
        ring
  have hxlinear : x ≤ 2 * α * u t := by
    calc
      x ≤ gamma (u t) (p06NumeratorCounterLength n) * CN := hxγ
      _ ≤ (2 * A * u t) * CN :=
        mul_le_mul_of_nonneg_right hγA.2.1 hCNnonneg
      _ = 2 * α * u t := by dsimp [α]; ring
  have hylinear : y ≤ 2 * β * u t := by
    calc
      y ≤ gamma (u t) (p06DenominatorCounterLength n) * CD := hyγ
      _ ≤ (2 * B * u t) * CD :=
        mul_le_mul_of_nonneg_right hγB.2.1 hCDnonneg
      _ = 2 * β * u t := by dsimp [β]; ring
  have hxquadratic : x ≤ α * u t + α₂ * (u t) ^ 2 := by
    calc
      x ≤ gamma (u t) (p06NumeratorCounterLength n) * CN := hxγ
      _ ≤ (A * u t + 2 * A ^ 2 * (u t) ^ 2) * CN :=
        mul_le_mul_of_nonneg_right hγA.2.2 hCNnonneg
      _ = α * u t + α₂ * (u t) ^ 2 := by dsimp [α, α₂]; ring
  have hyquadratic : y ≤ β * u t + β₂ * (u t) ^ 2 := by
    calc
      y ≤ gamma (u t) (p06DenominatorCounterLength n) * CD := hyγ
      _ ≤ (B * u t + 2 * B ^ 2 * (u t) ^ 2) * CD :=
        mul_le_mul_of_nonneg_right hγB.2.2 hCDnonneg
      _ = β * u t + β₂ * (u t) ^ 2 := by dsimp [β, β₂]; ring
  have hysmall : y ≤ 1 / 2 := le_trans hylinear hβsmall
  have hscalar := p06_scalar_bound (u t) α β α₂ β₂ x y
    (run t).u_nonneg hαnonneg hβnonneg hx hy hysmall
    hxlinear hylinear hxquadratic hyquadratic
  have hrelative : p06SecondBarycentricRelativeError (run t) ≤
      u t * (α + β) + C * (u t) ^ 2 := by
    rw [p06SecondBarycentricRelativeError, hExact, hcomp]
    exact (p06_ratio_bound N D (E t) (F t) hN hD (by
      change y < 1
      linarith)).trans (by simpa only [C] using hscalar)
  have hcoeff : p06SecondBarycentricFirstOrderCoefficient n
      (p06SecondBarycentricDataCondition problem)
      (p06SecondBarycentricOneCondition problem) = α + β := by
    rw [hCN, hCD]
    rfl
  rw [hcoeff]
  simpa [abs_mul, abs_pow, abs_of_nonneg hCnonneg,
    abs_of_nonneg (run t).u_nonneg] using hrelative

end VSCLReuse

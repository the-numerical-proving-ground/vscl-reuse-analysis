import VSCLReuse.P11.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Operator

private theorem p11InfNormRect_eq_norm {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect A = ‖A‖ := by
  simp only [p11InfNormRect, Matrix.linfty_opNorm_def]

private theorem p11InfNormRect_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  rw [p11InfNormRect_eq_norm]
  positivity

private theorem p11InfNormRect_add_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11InfNormRect_eq_norm]
  exact norm_add_le A B

private theorem p11InfNormRect_mul_le {m n q : ℕ}
    (A : P11Matrix m n) (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  simp only [p11InfNormRect_eq_norm]
  exact Matrix.linfty_opNorm_mul A B

private theorem p11_error_identity {m n q p : ℕ}
    {semantics : P11FirstOrderSemantics} (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        d.AError * run.B - run.A * d.BError + d.AError * d.BError := by
  have hA : p11StaticAWordApproximation run = run.A - d.AError := by
    rw [d.A_decomposition]
    abel
  have hB : p11StaticBWordApproximation run = run.B - d.BError := by
    rw [d.B_decomposition]
    abel
  unfold p11StaticAccumulationError
  rw [d.retained_partition, hA, hB]
  simp only [Matrix.sub_mul, Matrix.mul_sub]
  abel

private theorem p11_error_basic_bound {m n q p : ℕ}
    {semantics : P11FirstOrderSemantics} (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    p11StaticMultiwordForwardError run ≤
      (2 * p11StaticZeta run + p11StaticZeta run ^ 2 +
        p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
        p11StaticRawAccumulationCoefficient n p d.underflowCount
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticAccumUnderflowEnvelope run.model)) *
        p11InfNormRect run.A * p11InfNormRect run.B +
          |d.omittedRemainder| + |d.accumulationRemainder| := by
  let a := p11InfNormRect run.A
  let b := p11InfNormRect run.B
  let z := p11StaticZeta run
  have ha : 0 ≤ a := p11InfNormRect_nonneg run.A
  have hb : 0 ≤ b := p11InfNormRect_nonneg run.B
  have htri : p11StaticMultiwordForwardError run ≤
      p11InfNormRect (p11StaticAccumulationError run) +
        p11InfNormRect (p11StaticOmittedWordTail run) +
        p11InfNormRect (d.AError * run.B) +
        p11InfNormRect (run.A * d.BError) +
        p11InfNormRect (d.AError * d.BError) := by
    unfold p11StaticMultiwordForwardError
    rw [p11_error_identity run d]
    simp only [p11InfNormRect_eq_norm]
    have h1 := norm_add_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        d.AError * run.B - run.A * d.BError) (d.AError * d.BError)
    have h2 := norm_sub_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        d.AError * run.B) (run.A * d.BError)
    have h3 := norm_sub_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run)
      (d.AError * run.B)
    have h4 := norm_sub_le (p11StaticAccumulationError run)
      (p11StaticOmittedWordTail run)
    linarith
  have hEaB : p11InfNormRect (d.AError * run.B) ≤ z * a * b := by
    calc
      _ ≤ p11InfNormRect d.AError * b := p11InfNormRect_mul_le _ _
      _ ≤ (z * a) * b := mul_le_mul_of_nonneg_right d.A_error_bound hb
      _ = z * a * b := by ring
  have hAEb : p11InfNormRect (run.A * d.BError) ≤ z * a * b := by
    calc
      _ ≤ a * p11InfNormRect d.BError := p11InfNormRect_mul_le _ _
      _ ≤ a * (z * b) := mul_le_mul_of_nonneg_left d.B_error_bound ha
      _ = z * a * b := by ring
  have hEaEb : p11InfNormRect (d.AError * d.BError) ≤ z ^ 2 * a * b := by
    calc
      _ ≤ p11InfNormRect d.AError * p11InfNormRect d.BError :=
        p11InfNormRect_mul_le _ _
      _ ≤ (z * a) * (z * b) := by
        exact mul_le_mul d.A_error_bound d.B_error_bound
          (p11InfNormRect_nonneg d.BError)
          (le_trans (p11InfNormRect_nonneg d.AError) d.A_error_bound)
      _ = z ^ 2 * a * b := by ring
  have htail := d.omitted_tail_bound
  have hacc := d.accumulation_error_bound
  dsimp [p11NormwiseEnvelope] at htail hacc
  dsimp [a, b, z] at *
  nlinarith [htri, hEaB, hAEb, hEaEb, htail, hacc]

private theorem p11_unit_nonneg (precision : ℕ) :
    0 ≤ p11UnitRoundoff precision := by
  unfold p11UnitRoundoff
  positivity

private theorem p11_unit_le_one (precision : ℕ) :
    p11UnitRoundoff precision ≤ 1 := by
  unfold p11UnitRoundoff
  exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem p11_underflow_nonneg (precision : ℕ) (emin : ℤ) (sub : Bool) :
    0 ≤ p11UnderflowEnvelope precision emin sub := by
  cases sub <;> simp only [p11UnderflowEnvelope, p11MinNormal, p11UnitRoundoff] <;>
    positivity

private theorem p11_threshold_nonneg (n : ℕ) (model : P11StaticNearestModel1) :
    0 ≤ p11StaticScalingThreshold n model := by
  unfold p11StaticScalingThreshold p11ScalingThreshold
  apply le_min
  · unfold p11MaxFinite
    have hu := p11_unit_le_one model.inputFormat.precision
    have hpow : 0 ≤ (2 : ℝ) ^ model.inputFormat.maxExponent := by positivity
    nlinarith
  · exact Real.sqrt_nonneg _

private theorem p11_coefficient_bound {m n q p : ℕ}
    {semantics : P11FirstOrderSemantics} (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    2 * p11StaticZeta run +
      p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
      p11StaticRawAccumulationCoefficient n p d.underflowCount
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) ≤
      p11MultiNarrowCoefficient n p
        (p11StaticInputUnitRoundoff run.model)
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticInputUnderflowEnvelope run.model)
        (p11StaticAccumUnderflowEnvelope run.model) := by
  let u := p11StaticInputUnitRoundoff run.model
  let theta := p11StaticScalingThreshold n run.model
  let g := p11StaticInputUnderflowEnvelope run.model
  let G := p11StaticAccumUnderflowEnvelope run.model
  have hu : 0 ≤ u := p11_unit_nonneg _
  have htheta : 0 ≤ theta := p11_threshold_nonneg n run.model
  have hg : 0 ≤ g := p11_underflow_nonneg _ _ _
  have hG : 0 ≤ G := p11_underflow_nonneg _ _ _
  have hpow : 0 ≤ u ^ p := pow_nonneg hu _
  have hunder : 0 ≤ 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * g := by
    positivity
  have hz : p11StaticZeta run ≤
      u ^ p + 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * g := by
    unfold p11StaticZeta
    apply max_le
    · linarith
    · linarith
  have hfactor : 0 ≤ 4 * (n : ℝ) * theta⁻¹ ^ 2 * G := by positivity
  have hraw :
      4 * (d.underflowCount : ℝ) * (n : ℝ) * theta⁻¹ ^ 2 * G ≤
        2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 * theta⁻¹ ^ 2 * G := by
    have h := mul_le_mul_of_nonneg_right d.underflow_count_bound hfactor
    nlinarith only [h]
  dsimp [p11MultiNarrowCoefficient, p11MultiRangeFreeCoefficient,
    p11MultiInputRoundingCoefficient, p11MultiAccumRoundingCoefficient,
    p11MultiInputUnderflowCoefficient, p11MultiAccumUnderflowCoefficient,
    p11StaticOmittedCoefficient, p11StaticRawAccumulationCoefficient]
  dsimp [u, theta, g, G] at hz hraw
  nlinarith only [hz, hraw]

theorem p11_c1_multiword_forward_error
    {m n q p : ℕ} (semantics : P11FirstOrderSemantics) :
    (∀ (run : P11StaticMultiwordRun m n q p),
      P11StaticSection4Derivation semantics run →
        p11FirstOrderLe semantics
          (p11StaticMultiwordForwardError run)
          (p11NormwiseEnvelope
            (p11MultiNarrowCoefficient n p
              (p11StaticInputUnitRoundoff run.model)
              (p11StaticAccumUnitRoundoff run.model)
              (p11StaticScalingThreshold n run.model)
              (p11StaticInputUnderflowEnvelope run.model)
              (p11StaticAccumUnderflowEnvelope run.model))
            run.A run.B)) ∧
      (∀ (run : P11StaticMultiwordRun m n q p),
        P11StaticSection4Derivation semantics run →
          p11FirstOrderLe semantics
            (p11StaticMultiwordForwardError run)
            (p11NormwiseEnvelope
              (p11MultiRangeFreeCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticAccumUnitRoundoff run.model))
              run.A run.B +
            p11NormwiseEnvelope
              (p11MultiInputUnderflowCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model))
              run.A run.B +
            p11NormwiseEnvelope
              (p11MultiAccumUnderflowCoefficient n p
                (p11StaticScalingThreshold n run.model)
                (p11StaticAccumUnderflowEnvelope run.model))
              run.A run.B)) ∧
      (∀ run : P11StaticMultiwordRun m n q p,
        p11MultiInputRoundingCoefficient p
              (p11StaticInputUnitRoundoff run.model) =
            ((((p : ℝ) + 1) / 2) *
                p11StaticInputUnitRoundoff run.model ^ (p - 1)) *
              p11SingleInputRoundingCoefficient
                (p11StaticInputUnitRoundoff run.model) ∧
          (n : ℝ) *
              p11MultiInputUnderflowCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model) =
            p11StaticInputUnitRoundoff run.model ^ (p - 1) *
              p11SingleInputUnderflowCoefficient n
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model)) := by
  -- PROOF_START P11-C1-H001
  have hfirst : ∀ (run : P11StaticMultiwordRun m n q p),
      P11StaticSection4Derivation semantics run →
        p11FirstOrderLe semantics
          (p11StaticMultiwordForwardError run)
          (p11NormwiseEnvelope
            (p11MultiNarrowCoefficient n p
              (p11StaticInputUnitRoundoff run.model)
              (p11StaticAccumUnitRoundoff run.model)
              (p11StaticScalingThreshold n run.model)
              (p11StaticInputUnderflowEnvelope run.model)
              (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B) := by
    intro run d
    let quad := p11StaticZeta run ^ 2 * p11InfNormRect run.A *
      p11InfNormRect run.B
    have hquad : 0 ≤ quad := by
      dsimp [quad]
      exact mul_nonneg
        (mul_nonneg (sq_nonneg _) (p11InfNormRect_nonneg _))
        (p11InfNormRect_nonneg _)
    refine ⟨|quad| + |d.omittedRemainder| + |d.accumulationRemainder|,
      semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder d.quadratic_second_order)
          (semantics.abs_secondOrder d.omitted_remainder_second_order))
        (semantics.abs_secondOrder d.accumulation_remainder_second_order), ?_⟩
    have hbasic := p11_error_basic_bound run d
    have hcoeff := p11_coefficient_bound run d
    have hab : 0 ≤ p11InfNormRect run.A * p11InfNormRect run.B :=
      mul_nonneg (p11InfNormRect_nonneg _) (p11InfNormRect_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hcoeff hab
    dsimp [p11NormwiseEnvelope] at *
    rw [abs_of_nonneg (by positivity :
      0 ≤ |quad| + |d.omittedRemainder| + |d.accumulationRemainder|)]
    rw [abs_of_nonneg hquad]
    dsimp [quad]
    nlinarith only [hbasic, hmul]
  refine ⟨hfirst, ?_, ?_⟩
  · intro run d
    obtain ⟨remainder, hrem, hbound⟩ := hfirst run d
    refine ⟨remainder, hrem, ?_⟩
    convert hbound using 1
    unfold p11NormwiseEnvelope p11MultiNarrowCoefficient
    ring
  · intro run
    constructor
    · let u := p11StaticInputUnitRoundoff run.model
      have hpow : u ^ p = u ^ (p - 1) * u := by
        calc
          u ^ p = u ^ ((p - 1) + 1) := by rw [Nat.sub_add_cancel run.word_count_pos]
          _ = u ^ (p - 1) * u := pow_succ _ _
      dsimp [p11MultiInputRoundingCoefficient,
        p11SingleInputRoundingCoefficient]
      change ((p : ℝ) + 1) * u ^ p =
        ((((p : ℝ) + 1) / 2) * u ^ (p - 1)) * (2 * u)
      rw [hpow]
      ring
    · unfold p11MultiInputUnderflowCoefficient
        p11SingleInputUnderflowCoefficient
      ring

end VSCLReuse

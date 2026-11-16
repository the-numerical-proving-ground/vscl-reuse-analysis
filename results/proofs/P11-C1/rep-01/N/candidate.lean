import VSCLReuse.P11.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Operator

private theorem p11_norm_eq {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect A = ‖A‖ := by
  rw [p11InfNormRect, Matrix.linfty_opNorm_def]

private theorem p11_norm_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  rw [p11_norm_eq]
  exact norm_nonneg _

private theorem p11_norm_add {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact norm_add_le A B

private theorem p11_norm_sub {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A - B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact norm_sub_le A B

private theorem p11_norm_mul {m n q : ℕ} (A : P11Matrix m n)
    (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact Matrix.linfty_opNorm_mul A B

private theorem p11_norm_neg {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect (-A) = p11InfNormRect A := by
  simp [p11_norm_eq]

private theorem p11_input_coeff_identity (p : ℕ) (hp : 0 < p) (u : ℝ) :
    p11MultiInputRoundingCoefficient p u =
      ((((p : ℝ) + 1) / 2) * u ^ (p - 1)) *
        p11SingleInputRoundingCoefficient u := by
  have h : p = (p - 1) + 1 := (Nat.sub_add_cancel hp).symm
  have hpow : u ^ p = u ^ (p - 1) * u := by
    conv_lhs => rw [h, pow_succ]
  simp only [p11MultiInputRoundingCoefficient,
    p11SingleInputRoundingCoefficient, hpow]
  ring

private theorem p11_underflow_coeff_identity (n p : ℕ) (u theta gmin : ℝ) :
    (n : ℝ) * p11MultiInputUnderflowCoefficient n p u theta gmin =
      u ^ (p - 1) * p11SingleInputUnderflowCoefficient n theta gmin := by
  simp only [p11MultiInputUnderflowCoefficient,
    p11SingleInputUnderflowCoefficient]
  ring

private theorem p11_error_identity {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (h : P11StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run) -
        (h.AError * run.B + run.A * h.BError - h.AError * h.BError) := by
  rw [p11StaticAccumulationError, h.retained_partition]
  rw [h.A_decomposition, h.B_decomposition]
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

private theorem p11_error_raw_norm_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (h : P11StaticSection4Derivation semantics run) :
    p11StaticMultiwordForwardError run ≤
      p11InfNormRect (p11StaticAccumulationError run) +
      p11InfNormRect (p11StaticOmittedWordTail run) +
      (2 * p11StaticZeta run + p11StaticZeta run ^ 2) *
        p11InfNormRect run.A * p11InfNormRect run.B := by
  let x := p11InfNormRect run.A
  let y := p11InfNormRect run.B
  let z := p11StaticZeta run
  have hx : 0 ≤ x := p11_norm_nonneg _
  have hy : 0 ≤ y := p11_norm_nonneg _
  have hz : 0 ≤ z := by
    dsimp [z, p11StaticZeta]
    exact le_trans (by
      dsimp [p11StaticInputUnitRoundoff, p11UnitRoundoff]
      positivity : 0 ≤ p11StaticInputUnitRoundoff run.model ^ p) (le_max_left _ _)
  have hA : p11InfNormRect h.AError ≤ z * x := h.A_error_bound
  have hB : p11InfNormRect h.BError ≤ z * y := h.B_error_bound
  have hAB : p11InfNormRect (h.AError * run.B) ≤ z * x * y := by
    calc
      _ ≤ p11InfNormRect h.AError * y := p11_norm_mul _ _
      _ ≤ (z * x) * y := by gcongr
  have hBA : p11InfNormRect (run.A * h.BError) ≤ z * x * y := by
    calc
      _ ≤ x * p11InfNormRect h.BError := p11_norm_mul _ _
      _ ≤ x * (z * y) := by gcongr
      _ = z * x * y := by ring
  have hE : p11InfNormRect (h.AError * h.BError) ≤ z ^ 2 * x * y := by
    calc
      _ ≤ p11InfNormRect h.AError * p11InfNormRect h.BError := p11_norm_mul _ _
      _ ≤ (z * x) * (z * y) := by
        gcongr
        exact p11_norm_nonneg _
      _ = z ^ 2 * x * y := by ring
  have hnorm := p11_norm_sub
    (p11StaticAccumulationError run - p11StaticOmittedWordTail run)
    (h.AError * run.B + run.A * h.BError - h.AError * h.BError)
  have hnorm₁ := p11_norm_sub (p11StaticAccumulationError run)
    (p11StaticOmittedWordTail run)
  have hnorm₂ := p11_norm_sub (h.AError * run.B + run.A * h.BError)
    (h.AError * h.BError)
  have hnorm₃ := p11_norm_add (h.AError * run.B) (run.A * h.BError)
  dsimp [p11StaticMultiwordForwardError]
  rw [p11_error_identity semantics run h]
  dsimp [x, y, z] at *
  nlinarith

private theorem p11_input_underflow_nonneg (model : P11StaticNearestModel1) :
    0 ≤ p11StaticInputUnderflowEnvelope model := by
  unfold p11StaticInputUnderflowEnvelope p11UnderflowEnvelope
  cases model.inputFormat.hasSubnormals <;>
    simp only [p11MinNormal, p11UnitRoundoff] <;> positivity

private theorem p11_accum_underflow_nonneg (model : P11StaticNearestModel1) :
    0 ≤ p11StaticAccumUnderflowEnvelope model := by
  unfold p11StaticAccumUnderflowEnvelope p11UnderflowEnvelope
  cases model.accumulationFormat.hasSubnormals <;>
    simp only [p11MinNormal, p11UnitRoundoff] <;> positivity

private theorem p11_coefficient_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (h : P11StaticSection4Derivation semantics run) :
    2 * p11StaticZeta run +
        p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
        p11StaticRawAccumulationCoefficient n p h.underflowCount
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
  let U := p11StaticAccumUnitRoundoff run.model
  let theta := p11StaticScalingThreshold n run.model
  let g := p11StaticInputUnderflowEnvelope run.model
  let G := p11StaticAccumUnderflowEnvelope run.model
  have hu : 0 ≤ u := by
    dsimp [u, p11StaticInputUnitRoundoff, p11UnitRoundoff]
    positivity
  have htheta : 0 ≤ theta := by
    obtain ⟨hm, hn, _⟩ := run.dimension_pos
    exact le_trans (abs_nonneg _) (run.scaled_A_bound ⟨0, hm⟩ ⟨0, hn⟩)
  have hg : 0 ≤ g := p11_input_underflow_nonneg _
  have hG : 0 ≤ G := p11_accum_underflow_nonneg _
  have hz : p11StaticZeta run ≤
      u ^ p + 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * g := by
    dsimp [p11StaticZeta, u, theta, g]
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (by positivity)
  have hr :
      p11StaticRawAccumulationCoefficient n p h.underflowCount U theta G ≤
        p11StaticAccumulationCoefficient n p U theta G := by
    have hfac : 0 ≤ 4 * (n : ℝ) * (theta⁻¹) ^ 2 * G := by positivity
    have hc := mul_le_mul_of_nonneg_right h.underflow_count_bound hfac
    unfold p11StaticRawAccumulationCoefficient p11StaticAccumulationCoefficient
    unfold p11MultiAccumUnderflowCoefficient
    calc
      p11MultiAccumRoundingCoefficient n p U +
          4 * (h.underflowCount : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * G =
        p11MultiAccumRoundingCoefficient n p U +
          (h.underflowCount : ℝ) *
            (4 * (n : ℝ) * (theta⁻¹) ^ 2 * G) := by ring
      _ ≤
        p11MultiAccumRoundingCoefficient n p U +
          ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) *
            (4 * (n : ℝ) * (theta⁻¹) ^ 2 * G) := by
              simpa only [add_comm] using add_le_add_right hc
                (p11MultiAccumRoundingCoefficient n p U)
      _ = p11MultiAccumRoundingCoefficient n p U +
          2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
            (theta⁻¹) ^ 2 * G := by ring
  have hz2 : 2 * p11StaticZeta run ≤
      2 * u ^ p + p11MultiInputUnderflowCoefficient n p u theta g := by
    unfold p11MultiInputUnderflowCoefficient
    linarith
  calc
    2 * p11StaticZeta run + p11StaticOmittedCoefficient p u +
        p11StaticRawAccumulationCoefficient n p h.underflowCount U theta G ≤
      2 * u ^ p + p11MultiInputUnderflowCoefficient n p u theta g +
        p11StaticOmittedCoefficient p u +
        p11StaticAccumulationCoefficient n p U theta G := by linarith
    _ = p11MultiNarrowCoefficient n p u U theta g G := by
      unfold p11MultiNarrowCoefficient p11MultiRangeFreeCoefficient
        p11MultiInputRoundingCoefficient p11StaticOmittedCoefficient
        p11StaticAccumulationCoefficient
      ring

private theorem p11_envelope_split {m n q : ℕ} (n' p : ℕ)
    (u U theta g G : ℝ) (A : P11Matrix m n) (B : P11Matrix n q) :
    p11NormwiseEnvelope (p11MultiNarrowCoefficient n' p u U theta g G) A B =
      p11NormwiseEnvelope (p11MultiRangeFreeCoefficient n' p u U) A B +
      p11NormwiseEnvelope (p11MultiInputUnderflowCoefficient n' p u theta g) A B +
      p11NormwiseEnvelope (p11MultiAccumUnderflowCoefficient n' p theta G) A B := by
  unfold p11NormwiseEnvelope p11MultiNarrowCoefficient
  ring

private theorem p11_main_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (h : P11StaticSection4Derivation semantics run) :
    p11FirstOrderLe semantics
      (p11StaticMultiwordForwardError run)
      (p11NormwiseEnvelope
        (p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B) := by
  let quad := p11StaticZeta run ^ 2 * p11InfNormRect run.A * p11InfNormRect run.B
  have hquad : semantics.secondOrder quad := h.quadratic_second_order
  have hom : semantics.secondOrder |h.omittedRemainder| :=
    semantics.abs_secondOrder h.omitted_remainder_second_order
  have hac : semantics.secondOrder |h.accumulationRemainder| :=
    semantics.abs_secondOrder h.accumulation_remainder_second_order
  have hrem : semantics.secondOrder
      (|h.omittedRemainder| + |h.accumulationRemainder| + |quad|) :=
    semantics.add_secondOrder (semantics.add_secondOrder hom hac)
      (semantics.abs_secondOrder hquad)
  refine ⟨|h.omittedRemainder| + |h.accumulationRemainder| + |quad|,
    hrem, ?_⟩
  have hx : 0 ≤ p11InfNormRect run.A := p11_norm_nonneg _
  have hy : 0 ≤ p11InfNormRect run.B := p11_norm_nonneg _
  have hxy : 0 ≤ p11InfNormRect run.A * p11InfNormRect run.B :=
    mul_nonneg hx hy
  have hq : 0 ≤ quad := by dsimp [quad]; positivity
  have hc := p11_coefficient_bound semantics run h
  have hcp :
      (2 * p11StaticZeta run +
          p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
          p11StaticRawAccumulationCoefficient n p h.underflowCount
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) *
          p11InfNormRect run.A * p11InfNormRect run.B ≤
        p11NormwiseEnvelope
          (p11MultiNarrowCoefficient n p
            (p11StaticInputUnitRoundoff run.model)
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticInputUnderflowEnvelope run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B := by
    unfold p11NormwiseEnvelope
    calc
      _ = (2 * p11StaticZeta run +
          p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
          p11StaticRawAccumulationCoefficient n p h.underflowCount
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) *
          (p11InfNormRect run.A * p11InfNormRect run.B) := by ring
      _ ≤ p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model) *
          (p11InfNormRect run.A * p11InfNormRect run.B) :=
        mul_le_mul_of_nonneg_right hc hxy
      _ = _ := by ring
  have hraw := p11_error_raw_norm_bound semantics run h
  have htail := h.omitted_tail_bound
  have hacc := h.accumulation_error_bound
  dsimp [p11NormwiseEnvelope] at htail hacc
  change p11StaticMultiwordForwardError run ≤
    p11NormwiseEnvelope
      (p11MultiNarrowCoefficient n p
        (p11StaticInputUnitRoundoff run.model)
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticInputUnderflowEnvelope run.model)
        (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B +
      abs (|h.omittedRemainder| + |h.accumulationRemainder| + |quad|)
  rw [abs_of_nonneg (by positivity :
    0 ≤ |h.omittedRemainder| + |h.accumulationRemainder| + |quad|),
    abs_of_nonneg hq]
  dsimp [quad] at *
  nlinarith

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
  refine ⟨?_, ?_, ?_⟩
  · intro run h
    exact p11_main_bound semantics run h
  · intro run h
    have hmain := p11_main_bound semantics run h
    rw [p11_envelope_split n p
      (p11StaticInputUnitRoundoff run.model)
      (p11StaticAccumUnitRoundoff run.model)
      (p11StaticScalingThreshold n run.model)
      (p11StaticInputUnderflowEnvelope run.model)
      (p11StaticAccumUnderflowEnvelope run.model) run.A run.B] at hmain
    exact hmain
  · intro run
    constructor
    · exact p11_input_coeff_identity p run.word_count_pos
        (p11StaticInputUnitRoundoff run.model)
    · exact p11_underflow_coeff_identity n p
        (p11StaticInputUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticInputUnderflowEnvelope run.model)

end VSCLReuse

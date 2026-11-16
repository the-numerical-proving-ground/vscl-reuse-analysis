import VSCLReuse.P11.Definitions

namespace VSCLReuse

private theorem p11_norm_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  letI : NormedAddCommGroup (P11Matrix m n) := Matrix.linftyOpNormedAddCommGroup
  simpa only [p11InfNormRect, Matrix.linfty_opNorm_def] using (norm_nonneg A)

private theorem p11_norm_add_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  letI : NormedAddCommGroup (P11Matrix m n) := Matrix.linftyOpNormedAddCommGroup
  simpa only [p11InfNormRect, Matrix.linfty_opNorm_def] using (norm_add_le A B)

private theorem p11_norm_neg {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect (-A) = p11InfNormRect A := by
  letI : NormedAddCommGroup (P11Matrix m n) := Matrix.linftyOpNormedAddCommGroup
  simpa only [p11InfNormRect, Matrix.linfty_opNorm_def] using (norm_neg A)

private theorem p11_norm_sub_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A - B) ≤ p11InfNormRect A + p11InfNormRect B := by
  letI : NormedAddCommGroup (P11Matrix m n) := Matrix.linftyOpNormedAddCommGroup
  simpa only [p11InfNormRect, Matrix.linfty_opNorm_def] using (norm_sub_le A B)

private theorem p11_norm_mul_le {m n q : ℕ} (A : P11Matrix m n)
    (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  letI : NormedAddCommGroup (P11Matrix m n) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedAddCommGroup (P11Matrix n q) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedAddCommGroup (P11Matrix m q) := Matrix.linftyOpNormedAddCommGroup
  simpa only [p11InfNormRect, Matrix.linfty_opNorm_def] using Matrix.linfty_opNorm_mul A B

private theorem p11_error_matrix_identity {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics) (run : P11StaticMultiwordRun m n q p)
    (deriv : P11StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        deriv.AError * run.B - run.A * deriv.BError +
          deriv.AError * deriv.BError := by
  have hC : run.computed = p11StaticAccumulationError run +
      p11StaticExactRetainedWordProduct run := by
    simp [p11StaticAccumulationError]
  rw [hC, deriv.retained_partition, deriv.A_decomposition,
    deriv.B_decomposition]
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

private theorem p11_norm_five_le {m q : ℕ} (X Y Z W V : P11Matrix m q) :
    p11InfNormRect (X - Y - Z - W + V) ≤
      p11InfNormRect X + p11InfNormRect Y + p11InfNormRect Z +
        p11InfNormRect W + p11InfNormRect V := by
  have h1 := p11_norm_add_le (X - Y - Z - W) V
  have h2 := p11_norm_sub_le (X - Y - Z) W
  have h3 := p11_norm_sub_le (X - Y) Z
  have h4 := p11_norm_sub_le X Y
  linarith

private theorem p11_zeta_nonneg {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : 0 ≤ p11StaticZeta run := by
  unfold p11StaticZeta
  apply le_trans ?_ (le_max_left _ _)
  change 0 ≤ ((2 : ℝ)⁻¹ ^ run.model.inputFormat.precision) ^ p
  positivity

private theorem p11_forward_norm_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics) (run : P11StaticMultiwordRun m n q p)
    (deriv : P11StaticSection4Derivation semantics run) :
    p11StaticMultiwordForwardError run ≤
      p11InfNormRect (p11StaticAccumulationError run) +
        p11InfNormRect (p11StaticOmittedWordTail run) +
          (2 * p11StaticZeta run + p11StaticZeta run ^ 2) *
            p11InfNormRect run.A * p11InfNormRect run.B := by
  let z := p11StaticZeta run
  let a := p11InfNormRect run.A
  let b := p11InfNormRect run.B
  have hz : 0 ≤ z := p11_zeta_nonneg run
  have ha : 0 ≤ a := p11_norm_nonneg run.A
  have hb : 0 ≤ b := p11_norm_nonneg run.B
  have hAB : p11InfNormRect (deriv.AError * run.B) ≤ z * a * b := by
    calc
      _ ≤ p11InfNormRect deriv.AError * b := p11_norm_mul_le _ _
      _ ≤ (z * a) * b := by gcongr; exact deriv.A_error_bound
  have hBA : p11InfNormRect (run.A * deriv.BError) ≤ z * a * b := by
    calc
      _ ≤ a * p11InfNormRect deriv.BError := p11_norm_mul_le _ _
      _ ≤ a * (z * b) := by gcongr; exact deriv.B_error_bound
      _ = z * a * b := by ring
  have hAA : p11InfNormRect (deriv.AError * deriv.BError) ≤ z ^ 2 * a * b := by
    calc
      _ ≤ p11InfNormRect deriv.AError * p11InfNormRect deriv.BError :=
        p11_norm_mul_le _ _
      _ ≤ (z * a) * (z * b) := by
        gcongr
        · exact p11_norm_nonneg deriv.BError
        · exact deriv.A_error_bound
        · exact deriv.B_error_bound
      _ = z ^ 2 * a * b := by ring
  unfold p11StaticMultiwordForwardError
  calc
    p11InfNormRect (run.computed - run.A * run.B) ≤
        p11InfNormRect (p11StaticAccumulationError run) +
          p11InfNormRect (p11StaticOmittedWordTail run) +
          p11InfNormRect (deriv.AError * run.B) +
          p11InfNormRect (run.A * deriv.BError) +
          p11InfNormRect (deriv.AError * deriv.BError) := by
        rw [p11_error_matrix_identity semantics run deriv]
        exact p11_norm_five_le _ _ _ _ _
    _ ≤ p11InfNormRect (p11StaticAccumulationError run) +
          p11InfNormRect (p11StaticOmittedWordTail run) +
          (2 * z + z ^ 2) * a * b := by
        linarith [hAB, hBA, hAA]

private theorem p11_input_unit_nonneg (model : P11StaticNearestModel1) :
    0 ≤ p11StaticInputUnitRoundoff model := by
  unfold p11StaticInputUnitRoundoff p11UnitRoundoff
  positivity

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

private theorem p11_threshold_nonneg {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    0 ≤ p11StaticScalingThreshold n run.model := by
  let i : Fin m := ⟨0, run.dimension_pos.1⟩
  let j : Fin n := ⟨0, run.dimension_pos.2.1⟩
  exact (abs_nonneg _).trans (run.scaled_A_bound i j)

private theorem p11_zeta_le_sum {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    p11StaticZeta run ≤
      p11StaticInputUnitRoundoff run.model ^ p +
        2 * (n : ℝ) * p11StaticInputUnitRoundoff run.model ^ (p - 1) *
          (p11StaticScalingThreshold n run.model)⁻¹ *
            p11StaticInputUnderflowEnvelope run.model := by
  have hu : 0 ≤ p11StaticInputUnitRoundoff run.model ^ p :=
    pow_nonneg (p11_input_unit_nonneg run.model) _
  have hθ : 0 ≤ (p11StaticScalingThreshold n run.model)⁻¹ :=
    inv_nonneg.mpr (p11_threshold_nonneg run)
  have hg : 0 ≤ p11StaticInputUnderflowEnvelope run.model :=
    p11_input_underflow_nonneg run.model
  have hterm : 0 ≤ 2 * (n : ℝ) *
      p11StaticInputUnitRoundoff run.model ^ (p - 1) *
        (p11StaticScalingThreshold n run.model)⁻¹ *
          p11StaticInputUnderflowEnvelope run.model := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
          (pow_nonneg (p11_input_unit_nonneg run.model) _)) hθ) hg
  unfold p11StaticZeta
  exact max_le (le_add_of_nonneg_right hterm) (le_add_of_nonneg_left hu)

private theorem p11_raw_accum_coeff_le {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics) (run : P11StaticMultiwordRun m n q p)
    (deriv : P11StaticSection4Derivation semantics run) :
    p11StaticRawAccumulationCoefficient n p deriv.underflowCount
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) ≤
      p11StaticAccumulationCoefficient n p
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) := by
  let θ := p11StaticScalingThreshold n run.model
  let G := p11StaticAccumUnderflowEnvelope run.model
  have hfactor : 0 ≤ 4 * (n : ℝ) * (θ⁻¹) ^ 2 * G := by
    have hG : 0 ≤ G := p11_accum_underflow_nonneg run.model
    positivity
  have hcount := mul_le_mul_of_nonneg_right deriv.underflow_count_bound hfactor
  dsimp [p11StaticRawAccumulationCoefficient,
    p11StaticAccumulationCoefficient, p11MultiAccumUnderflowCoefficient]
  nlinarith [hcount]

private theorem p11_coefficient_le_narrow {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics) (run : P11StaticMultiwordRun m n q p)
    (deriv : P11StaticSection4Derivation semantics run) :
    2 * p11StaticZeta run +
      p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
      p11StaticRawAccumulationCoefficient n p deriv.underflowCount
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
  let θ := p11StaticScalingThreshold n run.model
  let g := p11StaticInputUnderflowEnvelope run.model
  let U := p11StaticAccumUnitRoundoff run.model
  let G := p11StaticAccumUnderflowEnvelope run.model
  have hz := p11_zeta_le_sum run
  have hr := p11_raw_accum_coeff_le semantics run deriv
  calc
    2 * p11StaticZeta run + p11StaticOmittedCoefficient p u +
        p11StaticRawAccumulationCoefficient n p deriv.underflowCount U θ G ≤
      2 * (u ^ p + 2 * (n : ℝ) * u ^ (p - 1) * θ⁻¹ * g) +
        p11StaticOmittedCoefficient p u +
          p11StaticAccumulationCoefficient n p U θ G := by
        dsimp [u, θ, g, U, G] at *
        linarith
    _ = p11MultiNarrowCoefficient n p u U θ g G := by
      unfold p11StaticOmittedCoefficient p11StaticAccumulationCoefficient
        p11MultiNarrowCoefficient p11MultiRangeFreeCoefficient
        p11MultiInputRoundingCoefficient p11MultiInputUnderflowCoefficient
      ring

private theorem p11_forward_narrow {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics) (run : P11StaticMultiwordRun m n q p)
    (deriv : P11StaticSection4Derivation semantics run) :
    p11FirstOrderLe semantics (p11StaticMultiwordForwardError run)
      (p11NormwiseEnvelope
        (p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B) := by
  let a := p11InfNormRect run.A
  let b := p11InfNormRect run.B
  let z := p11StaticZeta run
  have ha : 0 ≤ a := p11_norm_nonneg run.A
  have hb : 0 ≤ b := p11_norm_nonneg run.B
  have hforward := p11_forward_norm_bound semantics run deriv
  have htail := deriv.omitted_tail_bound
  have hacc := deriv.accumulation_error_bound
  dsimp [p11NormwiseEnvelope] at htail hacc
  have hraw : p11StaticMultiwordForwardError run ≤
      (2 * z + z ^ 2 +
        p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) +
        p11StaticRawAccumulationCoefficient n p deriv.underflowCount
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticAccumUnderflowEnvelope run.model)) * a * b +
      |deriv.omittedRemainder| + |deriv.accumulationRemainder| := by
    dsimp [a, b, z] at *
    nlinarith [hforward, htail, hacc]
  have hcoef := p11_coefficient_le_narrow semantics run deriv
  have hprod := mul_le_mul_of_nonneg_right hcoef (mul_nonneg ha hb)
  refine ⟨|deriv.omittedRemainder| + |deriv.accumulationRemainder| +
      |z ^ 2 * a * b|, ?_, ?_⟩
  · exact semantics.add_secondOrder
      (semantics.add_secondOrder
        (semantics.abs_secondOrder deriv.omitted_remainder_second_order)
        (semantics.abs_secondOrder deriv.accumulation_remainder_second_order))
      (semantics.abs_secondOrder deriv.quadratic_second_order)
  · have hrem : 0 ≤ |deriv.omittedRemainder| +
        |deriv.accumulationRemainder| + |z ^ 2 * a * b| := by positivity
    rw [abs_of_nonneg hrem]
    dsimp [p11NormwiseEnvelope]
    nlinarith [hraw, hprod, le_abs_self (z ^ 2 * a * b)]

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
  · intro run deriv
    exact p11_forward_narrow semantics run deriv
  · intro run deriv
    have h := p11_forward_narrow semantics run deriv
    simpa only [p11MultiNarrowCoefficient, p11NormwiseEnvelope, add_mul]
      using h
  · intro run
    constructor
    · cases p with
      | zero => exact (Nat.not_lt_zero _ run.word_count_pos).elim
      | succ k =>
          simp only [p11MultiInputRoundingCoefficient,
            p11SingleInputRoundingCoefficient, Nat.succ_sub_one, pow_succ]
          ring
    · unfold p11MultiInputUnderflowCoefficient
        p11SingleInputUnderflowCoefficient
      ring

end VSCLReuse

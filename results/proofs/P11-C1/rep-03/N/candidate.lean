import VSCLReuse.P11.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Operator

private theorem p11_norm_eq {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect A = ‖A‖ := by
  classical
  exact (Matrix.linfty_opNorm_def A).symm

private theorem p11_norm_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  rw [p11_norm_eq]
  positivity

private theorem p11_norm_add_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact norm_add_le A B

private theorem p11_norm_sub_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A - B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact norm_sub_le A B

private theorem p11_norm_mul_le {m n q : ℕ} (A : P11Matrix m n)
    (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  simp only [p11_norm_eq]
  exact Matrix.linfty_opNorm_mul A B

private theorem p11_envelope_mono {m n q : ℕ} (A : P11Matrix m n)
    (B : P11Matrix n q) {c d : ℝ} (h : c ≤ d) :
    p11NormwiseEnvelope c A B ≤ p11NormwiseEnvelope d A B := by
  unfold p11NormwiseEnvelope
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (p11_norm_nonneg A)) (p11_norm_nonneg B)

private theorem p11_error_identity {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    run.computed - run.A * run.B =
      p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        run.A * d.BError - d.AError * run.B + d.AError * d.BError := by
  have hA : p11StaticAWordApproximation run = run.A - d.AError := by
    rw [d.A_decomposition]
    abel
  have hB : p11StaticBWordApproximation run = run.B - d.BError := by
    rw [d.B_decomposition]
    abel
  have hC : run.computed = p11StaticExactRetainedWordProduct run +
      p11StaticAccumulationError run := by
    unfold p11StaticAccumulationError
    abel
  rw [hC, d.retained_partition, hA, hB]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  abel

private theorem p11_zeta_nonneg {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : 0 ≤ p11StaticZeta run := by
  unfold p11StaticZeta
  exact (show 0 ≤ p11StaticInputUnitRoundoff run.model ^ p by
    unfold p11StaticInputUnitRoundoff p11UnitRoundoff
    positivity).trans
    (le_max_left _ _)

private theorem p11_forward_raw_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    p11StaticMultiwordForwardError run ≤
      p11NormwiseEnvelope
        (p11StaticOmittedCoefficient p
            (p11StaticInputUnitRoundoff run.model) +
          p11StaticRawAccumulationCoefficient n p d.underflowCount
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticAccumUnderflowEnvelope run.model) +
          2 * p11StaticZeta run) run.A run.B +
        |d.omittedRemainder| + |d.accumulationRemainder| +
        p11StaticZeta run ^ 2 * p11InfNormRect run.A * p11InfNormRect run.B := by
  let z := p11StaticZeta run
  let a := p11InfNormRect run.A
  let b := p11InfNormRect run.B
  have hz : 0 ≤ z := p11_zeta_nonneg run
  have ha : 0 ≤ a := p11_norm_nonneg run.A
  have hb : 0 ≤ b := p11_norm_nonneg run.B
  have htri : p11StaticMultiwordForwardError run ≤
      p11InfNormRect (p11StaticAccumulationError run) +
        p11InfNormRect (p11StaticOmittedWordTail run) +
        p11InfNormRect (run.A * d.BError) +
        p11InfNormRect (d.AError * run.B) +
        p11InfNormRect (d.AError * d.BError) := by
    rw [p11StaticMultiwordForwardError, p11_error_identity semantics run d]
    have h1 := p11_norm_add_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        run.A * d.BError - d.AError * run.B) (d.AError * d.BError)
    have h2 := p11_norm_sub_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        run.A * d.BError) (d.AError * run.B)
    have h3 := p11_norm_sub_le
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run)
      (run.A * d.BError)
    have h4 := p11_norm_sub_le
      (p11StaticAccumulationError run) (p11StaticOmittedWordTail run)
    linarith
  have hAB : p11InfNormRect (run.A * d.BError) ≤ z * a * b := by
    calc
      _ ≤ a * p11InfNormRect d.BError := p11_norm_mul_le _ _
      _ ≤ a * (z * b) := mul_le_mul_of_nonneg_left d.B_error_bound ha
      _ = z * a * b := by ring
  have hBA : p11InfNormRect (d.AError * run.B) ≤ z * a * b := by
    calc
      _ ≤ p11InfNormRect d.AError * b := p11_norm_mul_le _ _
      _ ≤ (z * a) * b := mul_le_mul_of_nonneg_right d.A_error_bound hb
      _ = z * a * b := by ring
  have hEE : p11InfNormRect (d.AError * d.BError) ≤ z ^ 2 * a * b := by
    calc
      _ ≤ p11InfNormRect d.AError * p11InfNormRect d.BError := p11_norm_mul_le _ _
      _ ≤ (z * a) * p11InfNormRect d.BError :=
        mul_le_mul_of_nonneg_right d.A_error_bound (p11_norm_nonneg d.BError)
      _ ≤ (z * a) * (z * b) :=
        mul_le_mul_of_nonneg_left d.B_error_bound (mul_nonneg hz ha)
      _ = z ^ 2 * a * b := by ring
  dsimp [p11NormwiseEnvelope]
  have htail := d.omitted_tail_bound
  have hacc := d.accumulation_error_bound
  dsimp [p11NormwiseEnvelope] at htail hacc
  dsimp [z, a, b] at *
  nlinarith

private theorem p11_maxfinite_pos (format : P11StaticBinaryFormat) :
    0 < p11MaxFinite format.precision format.maxExponent := by
  have hu : p11UnitRoundoff format.precision < 1 := by
    unfold p11UnitRoundoff
    exact pow_lt_one₀ (by norm_num) (by norm_num)
      (Nat.ne_of_gt format.precision_pos)
  unfold p11MaxFinite
  apply mul_pos
  · positivity
  · linarith

private theorem p11_threshold_pos {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    0 < p11StaticScalingThreshold n run.model := by
  unfold p11StaticScalingThreshold p11ScalingThreshold
  apply lt_min
  · exact p11_maxfinite_pos run.model.inputFormat
  · apply Real.sqrt_pos.2
    apply div_pos
    · exact p11_maxfinite_pos run.model.accumulationFormat
    · exact_mod_cast run.dimension_pos.2.1

private theorem p11_underflow_nonneg (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) :
    0 ≤ p11UnderflowEnvelope precision minExponent hasSubnormals := by
  unfold p11UnderflowEnvelope
  cases hasSubnormals <;>
    simp only [p11MinNormal, p11UnitRoundoff] <;> positivity

private theorem p11_zeta_linear_bound {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    2 * p11StaticZeta run +
        p11StaticOmittedCoefficient p
          (p11StaticInputUnitRoundoff run.model) ≤
      p11MultiInputRoundingCoefficient p
          (p11StaticInputUnitRoundoff run.model) +
        p11MultiInputUnderflowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model) := by
  let u := p11StaticInputUnitRoundoff run.model
  let theta := p11StaticScalingThreshold n run.model
  let g := p11StaticInputUnderflowEnvelope run.model
  let x := u ^ p
  let y := 2 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * g
  have hx : 0 ≤ x := by
    dsimp [x, u, p11StaticInputUnitRoundoff, p11UnitRoundoff]
    positivity
  have htheta : 0 < theta := p11_threshold_pos run
  have hg : 0 ≤ g := p11_underflow_nonneg _ _ _
  have hy : 0 ≤ y := by
    dsimp [y]
    have hu : 0 ≤ u := by
      dsimp [u, p11StaticInputUnitRoundoff, p11UnitRoundoff]
      positivity
    positivity
  have hmax : max x y ≤ x + y :=
    max_le (le_add_of_nonneg_right hy) (le_add_of_nonneg_left hx)
  have hz : p11StaticZeta run = max x y := rfl
  calc
    2 * p11StaticZeta run + p11StaticOmittedCoefficient p u ≤
        2 * (x + y) + p11StaticOmittedCoefficient p u := by
      rw [hz]
      gcongr
    _ = p11MultiInputRoundingCoefficient p u +
          p11MultiInputUnderflowCoefficient n p u theta g := by
      dsimp [x, y, p11StaticOmittedCoefficient,
        p11MultiInputRoundingCoefficient, p11MultiInputUnderflowCoefficient]
      ring

private theorem p11_raw_accum_coeff_le {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    p11StaticRawAccumulationCoefficient n p d.underflowCount
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) ≤
      p11StaticAccumulationCoefficient n p
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) := by
  let U := p11StaticAccumUnitRoundoff run.model
  let theta := p11StaticScalingThreshold n run.model
  let G := p11StaticAccumUnderflowEnvelope run.model
  let k := 4 * (n : ℝ) * (theta⁻¹) ^ 2 * G
  have hG : 0 ≤ G := p11_underflow_nonneg _ _ _
  have hk : 0 ≤ k := by
    dsimp [k]
    positivity
  have hc := mul_le_mul_of_nonneg_right d.underflow_count_bound hk
  calc
    p11StaticRawAccumulationCoefficient n p d.underflowCount U theta G =
        p11MultiAccumRoundingCoefficient n p U + (d.underflowCount : ℝ) * k := by
      dsimp [p11StaticRawAccumulationCoefficient, k]
      ring
    _ ≤ p11MultiAccumRoundingCoefficient n p U +
          ((n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) * k :=
      add_le_add_right hc _
    _ = p11StaticAccumulationCoefficient n p U theta G := by
      dsimp [p11StaticAccumulationCoefficient,
        p11MultiAccumUnderflowCoefficient, k]
      ring

private theorem p11_total_coeff_le {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    p11StaticOmittedCoefficient p
        (p11StaticInputUnitRoundoff run.model) +
      p11StaticRawAccumulationCoefficient n p d.underflowCount
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) +
      2 * p11StaticZeta run ≤
        p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model) := by
  have h1 := p11_zeta_linear_bound run
  have h2 := p11_raw_accum_coeff_le semantics run d
  unfold p11MultiNarrowCoefficient p11MultiRangeFreeCoefficient
  unfold p11StaticAccumulationCoefficient at h2
  linarith

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
  have hmain : ∀ (run : P11StaticMultiwordRun m n q p),
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
            run.A run.B) := by
    intro run d
    let w := |d.omittedRemainder| + |d.accumulationRemainder| +
      p11StaticZeta run ^ 2 * p11InfNormRect run.A * p11InfNormRect run.B
    refine ⟨w, ?_, ?_⟩
    · exact semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder d.omitted_remainder_second_order)
          (semantics.abs_secondOrder d.accumulation_remainder_second_order))
        d.quadratic_second_order
    · have hw : 0 ≤ w := by
        dsimp [w]
        have ha := p11_norm_nonneg run.A
        have hb := p11_norm_nonneg run.B
        positivity
      rw [abs_of_nonneg hw]
      have hraw := p11_forward_raw_bound semantics run d
      have hcoeff := p11_total_coeff_le semantics run d
      have henv := p11_envelope_mono run.A run.B hcoeff
      dsimp [w]
      linarith
  refine ⟨hmain, ?_, ?_⟩
  · intro run d
    obtain ⟨w, hw, hbound⟩ := hmain run d
    refine ⟨w, hw, ?_⟩
    have hsplit :
        p11NormwiseEnvelope
          (p11MultiNarrowCoefficient n p
            (p11StaticInputUnitRoundoff run.model)
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticInputUnderflowEnvelope run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B =
        p11NormwiseEnvelope
          (p11MultiRangeFreeCoefficient n p
            (p11StaticInputUnitRoundoff run.model)
            (p11StaticAccumUnitRoundoff run.model)) run.A run.B +
        p11NormwiseEnvelope
          (p11MultiInputUnderflowCoefficient n p
            (p11StaticInputUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticInputUnderflowEnvelope run.model)) run.A run.B +
        p11NormwiseEnvelope
          (p11MultiAccumUnderflowCoefficient n p
            (p11StaticScalingThreshold n run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B := by
      unfold p11NormwiseEnvelope p11MultiNarrowCoefficient
      ring
    rw [hsplit] at hbound
    exact hbound
  · intro run
    constructor
    · let u := p11StaticInputUnitRoundoff run.model
      have hp : p - 1 + 1 = p :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt run.word_count_pos))
      have hpow : u ^ p = u ^ (p - 1) * u := by
        conv_lhs => rw [← hp, pow_succ]
      unfold p11MultiInputRoundingCoefficient
        p11SingleInputRoundingCoefficient
      rw [hpow]
      ring
    · unfold p11MultiInputUnderflowCoefficient
        p11SingleInputUnderflowCoefficient
      ring

end VSCLReuse

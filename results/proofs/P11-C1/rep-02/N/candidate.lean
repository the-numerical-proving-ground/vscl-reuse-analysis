import VSCLReuse.P11.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Operator

private theorem p11_infNorm_eq_norm {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect A = ‖A‖ := by
  exact (Matrix.linfty_opNorm_def A).symm

private theorem p11_infNorm_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  rw [p11_infNorm_eq_norm]
  exact norm_nonneg _

private theorem p11_infNorm_add {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_infNorm_eq_norm]
  exact norm_add_le _ _

private theorem p11_infNorm_sub {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A - B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simp only [p11_infNorm_eq_norm]
  exact norm_sub_le _ _

private theorem p11_infNorm_mul {m n q : ℕ}
    (A : P11Matrix m n) (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  simp only [p11_infNorm_eq_norm]
  exact Matrix.linfty_opNorm_mul A B

private theorem p11_infNorm_neg {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect (-A) = p11InfNormRect A := by
  simp only [p11_infNorm_eq_norm, norm_neg]

private theorem p11_unitRoundoff_nonneg (t : ℕ) :
    0 ≤ p11UnitRoundoff t := by
  unfold p11UnitRoundoff
  positivity

private theorem p11_unitRoundoff_le_half (t : ℕ) (ht : 0 < t) :
    p11UnitRoundoff t ≤ (1 / 2 : ℝ) := by
  unfold p11UnitRoundoff
  have h := pow_le_pow_of_le_one
    (show 0 ≤ (2 : ℝ)⁻¹ by norm_num)
    (show (2 : ℝ)⁻¹ ≤ 1 by norm_num)
    (Nat.one_le_iff_ne_zero.mpr (by omega : t ≠ 0))
  simpa only [pow_one, inv_eq_one_div] using h

private theorem p11_maxFinite_pos (t : ℕ) (ht : 0 < t) (e : ℤ) :
    0 < p11MaxFinite t e := by
  unfold p11MaxFinite
  have hu := p11_unitRoundoff_le_half t ht
  have he : 0 < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  apply mul_pos he
  linarith

private theorem p11_underflow_nonneg (t : ℕ) (e : ℤ) (s : Bool) :
    0 ≤ p11UnderflowEnvelope t e s := by
  cases s <;> simp only [p11UnderflowEnvelope]
  · unfold p11MinNormal
    positivity
  · exact mul_nonneg (p11_unitRoundoff_nonneg t) (by unfold p11MinNormal; positivity)

private theorem p11_threshold_pos (n : ℕ) (hn : 0 < n)
    (model : P11StaticNearestModel1) :
    0 < p11StaticScalingThreshold n model := by
  unfold p11StaticScalingThreshold p11ScalingThreshold
  apply lt_min
  · exact p11_maxFinite_pos _ model.inputFormat.precision_pos _
  · apply Real.sqrt_pos.2
    apply div_pos
    · exact p11_maxFinite_pos _ model.accumulationFormat.precision_pos _
    · exact_mod_cast hn

private theorem p11_zeta_nonneg {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    0 ≤ p11StaticZeta run := by
  unfold p11StaticZeta
  exact le_trans (pow_nonneg (p11_unitRoundoff_nonneg _) _)
    (le_max_left _ _)

private theorem p11_forward_identity {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
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
  calc
    run.computed - run.A * run.B =
        p11StaticAccumulationError run +
          p11StaticExactRetainedWordProduct run - run.A * run.B := by
          unfold p11StaticAccumulationError
          abel
    _ = p11StaticAccumulationError run +
          (p11StaticAWordApproximation run * p11StaticBWordApproximation run -
            p11StaticOmittedWordTail run) - run.A * run.B := by
          rw [d.retained_partition]
    _ = _ := by
      rw [hA, hB]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      abel

private theorem p11_forward_raw_bound {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    p11StaticMultiwordForwardError run ≤
      (2 * p11StaticZeta run + p11StaticZeta run ^ 2 +
        p11StaticOmittedCoefficient p
          (p11StaticInputUnitRoundoff run.model) +
        p11StaticRawAccumulationCoefficient n p d.underflowCount
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticAccumUnderflowEnvelope run.model)) *
          p11InfNormRect run.A * p11InfNormRect run.B +
        (|d.omittedRemainder| + |d.accumulationRemainder|) := by
  let NA := p11InfNormRect run.A
  let NB := p11InfNormRect run.B
  let z := p11StaticZeta run
  have hNA : 0 ≤ NA := p11_infNorm_nonneg _
  have hNB : 0 ≤ NB := p11_infNorm_nonneg _
  have hz : 0 ≤ z := p11_zeta_nonneg run
  have hAE : p11InfNormRect d.AError ≤ z * NA := d.A_error_bound
  have hBE : p11InfNormRect d.BError ≤ z * NB := d.B_error_bound
  have hAEB : p11InfNormRect (d.AError * run.B) ≤ z * NA * NB := by
    calc
      _ ≤ p11InfNormRect d.AError * NB := p11_infNorm_mul _ _
      _ ≤ (z * NA) * NB := by gcongr
  have hABE : p11InfNormRect (run.A * d.BError) ≤ z * NA * NB := by
    calc
      _ ≤ NA * p11InfNormRect d.BError := p11_infNorm_mul _ _
      _ ≤ NA * (z * NB) := by gcongr
      _ = z * NA * NB := by ring
  have hAEBE : p11InfNormRect (d.AError * d.BError) ≤ z ^ 2 * NA * NB := by
    calc
      _ ≤ p11InfNormRect d.AError * p11InfNormRect d.BError := p11_infNorm_mul _ _
      _ ≤ (z * NA) * (z * NB) := by
        gcongr
        exact p11_infNorm_nonneg _
      _ = z ^ 2 * NA * NB := by ring
  have htri : p11StaticMultiwordForwardError run ≤
      p11InfNormRect (p11StaticAccumulationError run) +
        p11InfNormRect (p11StaticOmittedWordTail run) +
        p11InfNormRect (d.AError * run.B) +
        p11InfNormRect (run.A * d.BError) +
        p11InfNormRect (d.AError * d.BError) := by
    rw [p11StaticMultiwordForwardError, p11_forward_identity semantics run d]
    have h1 := p11_infNorm_add
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        d.AError * run.B - run.A * d.BError) (d.AError * d.BError)
    have h2 := p11_infNorm_sub
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run -
        d.AError * run.B) (run.A * d.BError)
    have h3 := p11_infNorm_sub
      (p11StaticAccumulationError run - p11StaticOmittedWordTail run)
        (d.AError * run.B)
    have h4 := p11_infNorm_sub (p11StaticAccumulationError run)
      (p11StaticOmittedWordTail run)
    linarith
  have hacc := d.accumulation_error_bound
  have homit := d.omitted_tail_bound
  change p11InfNormRect (p11StaticAccumulationError run) ≤
    p11StaticRawAccumulationCoefficient n p d.underflowCount
      (p11StaticAccumUnitRoundoff run.model)
      (p11StaticScalingThreshold n run.model)
      (p11StaticAccumUnderflowEnvelope run.model) * NA * NB +
        |d.accumulationRemainder| at hacc
  change p11InfNormRect (p11StaticOmittedWordTail run) ≤
    p11StaticOmittedCoefficient p (p11StaticInputUnitRoundoff run.model) *
      NA * NB + |d.omittedRemainder| at homit
  change p11StaticMultiwordForwardError run ≤ _
  nlinarith

private theorem p11_zeta_le_sum {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    p11StaticZeta run ≤
      p11StaticInputUnitRoundoff run.model ^ p +
        2 * (n : ℝ) * p11StaticInputUnitRoundoff run.model ^ (p - 1) *
          (p11StaticScalingThreshold n run.model)⁻¹ *
            p11StaticInputUnderflowEnvelope run.model := by
  have hu : 0 ≤ p11StaticInputUnitRoundoff run.model :=
    p11_unitRoundoff_nonneg _
  have ht : 0 < p11StaticScalingThreshold n run.model :=
    p11_threshold_pos n run.dimension_pos.2.1 run.model
  have hg : 0 ≤ p11StaticInputUnderflowEnvelope run.model :=
    p11_underflow_nonneg _ _ _
  have hx : 0 ≤ p11StaticInputUnitRoundoff run.model ^ p := pow_nonneg hu _
  have hy : 0 ≤ 2 * (n : ℝ) *
      p11StaticInputUnitRoundoff run.model ^ (p - 1) *
      (p11StaticScalingThreshold n run.model)⁻¹ *
      p11StaticInputUnderflowEnvelope run.model := by positivity
  unfold p11StaticZeta
  exact max_le (le_add_of_nonneg_right hy) (le_add_of_nonneg_left hx)

private theorem p11_rawAccum_le {m n q p : ℕ}
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
  let theta := p11StaticScalingThreshold n run.model
  let Gmin := p11StaticAccumUnderflowEnvelope run.model
  have hG : 0 ≤ Gmin := p11_underflow_nonneg _ _ _
  have hfactor : 0 ≤ 4 * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin := by positivity
  have hcount := mul_le_mul_of_nonneg_right d.underflow_count_bound hfactor
  unfold p11StaticRawAccumulationCoefficient p11StaticAccumulationCoefficient
    p11MultiAccumUnderflowCoefficient
  dsimp [theta, Gmin] at hcount
  nlinarith

private theorem p11_coefficient_le {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (d : P11StaticSection4Derivation semantics run) :
    2 * p11StaticZeta run +
      p11StaticOmittedCoefficient p
        (p11StaticInputUnitRoundoff run.model) +
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
  have hz := p11_zeta_le_sum run
  have hr := p11_rawAccum_le semantics run d
  unfold p11MultiNarrowCoefficient p11MultiRangeFreeCoefficient
    p11MultiInputRoundingCoefficient p11MultiAccumRoundingCoefficient
    p11MultiInputUnderflowCoefficient p11MultiAccumUnderflowCoefficient
    p11StaticOmittedCoefficient at *
  unfold p11StaticAccumulationCoefficient at hr
  unfold p11MultiAccumRoundingCoefficient p11MultiAccumUnderflowCoefficient at hr
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
  have first : ∀ (run : P11StaticMultiwordRun m n q p),
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
    let remainder := |d.omittedRemainder| + |d.accumulationRemainder| + |quad|
    refine ⟨remainder, ?_, ?_⟩
    · exact semantics.add_secondOrder
        (semantics.add_secondOrder
          (semantics.abs_secondOrder d.omitted_remainder_second_order)
          (semantics.abs_secondOrder d.accumulation_remainder_second_order))
        (semantics.abs_secondOrder d.quadratic_second_order)
    · have hraw := p11_forward_raw_bound semantics run d
      have hcoeff := p11_coefficient_le semantics run d
      have hNA := p11_infNorm_nonneg run.A
      have hNB := p11_infNorm_nonneg run.B
      have hscaled := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff hNA) hNB
      have hquad : 0 ≤ quad := by
        dsimp [quad]
        positivity
      have hrem : 0 ≤ remainder := by
        dsimp [remainder]
        positivity
      change p11StaticMultiwordForwardError run ≤
        p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model) *
          p11InfNormRect run.A * p11InfNormRect run.B + |remainder|
      rw [abs_of_nonneg hrem]
      change p11StaticMultiwordForwardError run ≤
        p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model) *
          p11InfNormRect run.A * p11InfNormRect run.B +
            (|d.omittedRemainder| + |d.accumulationRemainder| + |quad|)
      rw [abs_of_nonneg hquad]
      dsimp [quad]
      nlinarith
  refine ⟨first, ?_, ?_⟩
  · intro run d
    have h := first run d
    have hsplit : p11NormwiseEnvelope
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
    rw [← hsplit]
    exact h
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

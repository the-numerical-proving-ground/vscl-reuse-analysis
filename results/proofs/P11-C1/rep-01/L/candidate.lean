import VSCLReuse.P11.Definitions

namespace VSCLReuse

private theorem p11_norm_nonneg {m n : ℕ} (A : P11Matrix m n) :
    0 ≤ p11InfNormRect A := by
  unfold p11InfNormRect
  exact NNReal.coe_nonneg _

private theorem p11_norm_add_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A + B) ≤ p11InfNormRect A + p11InfNormRect B := by
  letI : SeminormedAddCommGroup (P11Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [Matrix.linfty_opNorm_def, p11InfNormRect] using
    (norm_add_le A B)

private theorem p11_norm_neg {m n : ℕ} (A : P11Matrix m n) :
    p11InfNormRect (-A) = p11InfNormRect A := by
  letI : SeminormedAddCommGroup (P11Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [Matrix.linfty_opNorm_def, p11InfNormRect] using
    (norm_neg A)

private theorem p11_norm_sub_le {m n : ℕ} (A B : P11Matrix m n) :
    p11InfNormRect (A - B) ≤ p11InfNormRect A + p11InfNormRect B := by
  simpa only [sub_eq_add_neg, p11_norm_neg] using p11_norm_add_le A (-B)

private theorem p11_norm_mul_le {m n q : ℕ} (A : P11Matrix m n)
    (B : P11Matrix n q) :
    p11InfNormRect (A * B) ≤ p11InfNormRect A * p11InfNormRect B := by
  letI : SeminormedAddCommGroup (P11Matrix m n) :=
    Matrix.linftyOpSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (P11Matrix n q) :=
    Matrix.linftyOpSeminormedAddCommGroup
  letI : SeminormedAddCommGroup (P11Matrix m q) :=
    Matrix.linftyOpSeminormedAddCommGroup
  simpa only [Matrix.linfty_opNorm_def, p11InfNormRect] using
    (Matrix.linfty_opNorm_mul A B)

private theorem p11_product_error_identity {m n q : ℕ}
    (A A₀ Eₐ : P11Matrix m n) (B B₀ Eᵦ : P11Matrix n q)
    (C T Acc : P11Matrix m q)
    (hA : A = A₀ + Eₐ) (hB : B = B₀ + Eᵦ)
    (hC : C = Acc + (A₀ * B₀ - T)) :
    C - A * B = Acc - T - Eₐ * B - A * Eᵦ + Eₐ * Eᵦ := by
  subst A
  subst B
  subst C
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

private theorem p11_product_error_bound {m n q : ℕ}
    (A A₀ Eₐ : P11Matrix m n) (B B₀ Eᵦ : P11Matrix n q)
    (C T Acc : P11Matrix m q) (z a t rAcc rT : ℝ)
    (hA : A = A₀ + Eₐ) (hB : B = B₀ + Eᵦ)
    (hC : C = Acc + (A₀ * B₀ - T))
    (hz : 0 ≤ z)
    (hEA : p11InfNormRect Eₐ ≤ z * p11InfNormRect A)
    (hEB : p11InfNormRect Eᵦ ≤ z * p11InfNormRect B)
    (hAcc : p11InfNormRect Acc ≤
      a * p11InfNormRect A * p11InfNormRect B + |rAcc|)
    (hT : p11InfNormRect T ≤
      t * p11InfNormRect A * p11InfNormRect B + |rT|) :
    p11InfNormRect (C - A * B) ≤
      (a + t + 2 * z + z ^ 2) * p11InfNormRect A *
          p11InfNormRect B + |rAcc| + |rT| := by
  let x := p11InfNormRect A
  let y := p11InfNormRect B
  have hx : 0 ≤ x := p11_norm_nonneg A
  have hy : 0 ≤ y := p11_norm_nonneg B
  have hEAB : p11InfNormRect (Eₐ * B) ≤ z * x * y := by
    calc
      p11InfNormRect (Eₐ * B) ≤ p11InfNormRect Eₐ * y := p11_norm_mul_le Eₐ B
      _ ≤ (z * x) * y := by gcongr
  have hAEB : p11InfNormRect (A * Eᵦ) ≤ z * x * y := by
    calc
      p11InfNormRect (A * Eᵦ) ≤ x * p11InfNormRect Eᵦ := p11_norm_mul_le A Eᵦ
      _ ≤ x * (z * y) := by gcongr
      _ = z * x * y := by ring
  have hEAEB : p11InfNormRect (Eₐ * Eᵦ) ≤ z ^ 2 * x * y := by
    calc
      p11InfNormRect (Eₐ * Eᵦ) ≤
          p11InfNormRect Eₐ * p11InfNormRect Eᵦ := p11_norm_mul_le Eₐ Eᵦ
      _ ≤ (z * x) * (z * y) := by
        exact mul_le_mul hEA hEB (p11_norm_nonneg Eᵦ) (mul_nonneg hz hx)
      _ = z ^ 2 * x * y := by ring
  have htriangle :
      p11InfNormRect (Acc - T - Eₐ * B - A * Eᵦ + Eₐ * Eᵦ) ≤
        p11InfNormRect Acc + p11InfNormRect T +
          p11InfNormRect (Eₐ * B) + p11InfNormRect (A * Eᵦ) +
            p11InfNormRect (Eₐ * Eᵦ) := by
    calc
      _ ≤ p11InfNormRect (Acc - T - Eₐ * B - A * Eᵦ) +
          p11InfNormRect (Eₐ * Eᵦ) := p11_norm_add_le _ _
      _ ≤ p11InfNormRect (Acc - T - Eₐ * B) +
          p11InfNormRect (A * Eᵦ) + p11InfNormRect (Eₐ * Eᵦ) := by
        linarith [p11_norm_sub_le (Acc - T - Eₐ * B) (A * Eᵦ)]
      _ ≤ p11InfNormRect (Acc - T) + p11InfNormRect (Eₐ * B) +
          p11InfNormRect (A * Eᵦ) + p11InfNormRect (Eₐ * Eᵦ) := by
        linarith [p11_norm_sub_le (Acc - T) (Eₐ * B)]
      _ ≤ _ := by linarith [p11_norm_sub_le Acc T]
  rw [p11_product_error_identity A A₀ Eₐ B B₀ Eᵦ C T Acc hA hB hC]
  calc
    _ ≤ p11InfNormRect Acc + p11InfNormRect T +
          p11InfNormRect (Eₐ * B) + p11InfNormRect (A * Eᵦ) +
            p11InfNormRect (Eₐ * Eᵦ) := htriangle
    _ ≤ (a + t + 2 * z + z ^ 2) * x * y + |rAcc| + |rT| := by
      nlinarith [hEAB, hAEB, hEAEB]

private theorem p11_unit_nonneg (precision : ℕ) :
    0 ≤ p11UnitRoundoff precision := by
  unfold p11UnitRoundoff
  positivity

private theorem p11_unit_le_one (precision : ℕ) :
    p11UnitRoundoff precision ≤ 1 := by
  unfold p11UnitRoundoff
  exact pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1)

private theorem p11_max_finite_nonneg (precision : ℕ) (exponent : ℤ) :
    0 ≤ p11MaxFinite precision exponent := by
  unfold p11MaxFinite
  have hu := p11_unit_le_one precision
  have hpow : 0 ≤ (2 : ℝ) ^ exponent := by positivity
  have hfactor : 0 ≤ 2 - 2 * p11UnitRoundoff precision := by linarith
  exact mul_nonneg hpow hfactor

private theorem p11_min_normal_nonneg (exponent : ℤ) :
    0 ≤ p11MinNormal exponent := by
  unfold p11MinNormal
  positivity

private theorem p11_underflow_nonneg (precision : ℕ) (exponent : ℤ)
    (hasSubnormals : Bool) :
    0 ≤ p11UnderflowEnvelope precision exponent hasSubnormals := by
  cases hasSubnormals <;> simp only [p11UnderflowEnvelope]
  · exact div_nonneg (p11_min_normal_nonneg exponent) (by norm_num)
  · exact mul_nonneg (p11_unit_nonneg precision) (p11_min_normal_nonneg exponent)

private theorem p11_threshold_nonneg (n : ℕ) (model : P11StaticNearestModel1) :
    0 ≤ p11StaticScalingThreshold n model := by
  unfold p11StaticScalingThreshold p11ScalingThreshold
  exact le_min (p11_max_finite_nonneg _ _) (Real.sqrt_nonneg _)

private theorem p11_zeta_bound {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) :
    0 ≤ p11StaticZeta run ∧
      p11StaticZeta run ≤
        p11StaticInputUnitRoundoff run.model ^ p +
          2 * (n : ℝ) * p11StaticInputUnitRoundoff run.model ^ (p - 1) *
            (p11StaticScalingThreshold n run.model)⁻¹ *
              p11StaticInputUnderflowEnvelope run.model := by
  have hu : 0 ≤ p11StaticInputUnitRoundoff run.model :=
    p11_unit_nonneg _
  have htheta : 0 ≤ (p11StaticScalingThreshold n run.model)⁻¹ :=
    inv_nonneg.mpr (p11_threshold_nonneg n run.model)
  have hg : 0 ≤ p11StaticInputUnderflowEnvelope run.model :=
    p11_underflow_nonneg _ _ _
  have huPow : 0 ≤ p11StaticInputUnitRoundoff run.model ^ p :=
    pow_nonneg hu _
  have hunder :
      0 ≤ 2 * (n : ℝ) *
        p11StaticInputUnitRoundoff run.model ^ (p - 1) *
          (p11StaticScalingThreshold n run.model)⁻¹ *
            p11StaticInputUnderflowEnvelope run.model := by positivity
  unfold p11StaticZeta
  constructor
  · exact le_trans huPow (le_max_left _ _)
  · exact max_le (le_add_of_nonneg_right hunder)
      (le_add_of_nonneg_left huPow)

private theorem p11_raw_accumulation_coefficient_le {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) (r : ℕ)
    (hr : (r : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) :
    p11StaticRawAccumulationCoefficient n p r
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) ≤
      p11StaticAccumulationCoefficient n p
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hG : 0 ≤ p11StaticAccumUnderflowEnvelope run.model :=
    p11_underflow_nonneg _ _ _
  have hcount :
      4 * (r : ℝ) * (n : ℝ) ≤
        2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ 4 * (n : ℝ) by positivity)
    nlinarith
  have hfactor :
      0 ≤ (p11StaticScalingThreshold n run.model)⁻¹ ^ 2 *
          p11StaticAccumUnderflowEnvelope run.model := by positivity
  unfold p11StaticRawAccumulationCoefficient p11StaticAccumulationCoefficient
    p11MultiAccumUnderflowCoefficient
  have h := mul_le_mul_of_nonneg_right hcount hfactor
  nlinarith

private theorem p11_narrow_coefficient_bound {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) (r : ℕ)
    (hr : (r : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2) :
    p11StaticRawAccumulationCoefficient n p r
        (p11StaticAccumUnitRoundoff run.model)
        (p11StaticScalingThreshold n run.model)
        (p11StaticAccumUnderflowEnvelope run.model) +
      p11StaticOmittedCoefficient p
        (p11StaticInputUnitRoundoff run.model) +
      2 * p11StaticZeta run ≤
        p11MultiNarrowCoefficient n p
          (p11StaticInputUnitRoundoff run.model)
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticInputUnderflowEnvelope run.model)
          (p11StaticAccumUnderflowEnvelope run.model) := by
  have hz := (p11_zeta_bound run).2
  have hraw := p11_raw_accumulation_coefficient_le run r hr
  calc
    _ ≤ p11StaticAccumulationCoefficient n p
          (p11StaticAccumUnitRoundoff run.model)
          (p11StaticScalingThreshold n run.model)
          (p11StaticAccumUnderflowEnvelope run.model) +
        p11StaticOmittedCoefficient p
          (p11StaticInputUnitRoundoff run.model) +
        2 * (p11StaticInputUnitRoundoff run.model ^ p +
          2 * (n : ℝ) * p11StaticInputUnitRoundoff run.model ^ (p - 1) *
            (p11StaticScalingThreshold n run.model)⁻¹ *
              p11StaticInputUnderflowEnvelope run.model) := by linarith
    _ = _ := by
      unfold p11StaticAccumulationCoefficient p11StaticOmittedCoefficient
        p11MultiNarrowCoefficient p11MultiRangeFreeCoefficient
        p11MultiInputRoundingCoefficient p11MultiAccumRoundingCoefficient
        p11MultiInputUnderflowCoefficient
      ring

private theorem p11_static_narrow_forward_error {m n q p : ℕ}
    (semantics : P11FirstOrderSemantics)
    (run : P11StaticMultiwordRun m n q p)
    (derivation : P11StaticSection4Derivation semantics run) :
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
  let x := p11InfNormRect run.A
  let y := p11InfNormRect run.B
  let z := p11StaticZeta run
  let a := p11StaticRawAccumulationCoefficient n p derivation.underflowCount
    (p11StaticAccumUnitRoundoff run.model)
    (p11StaticScalingThreshold n run.model)
    (p11StaticAccumUnderflowEnvelope run.model)
  let t := p11StaticOmittedCoefficient p
    (p11StaticInputUnitRoundoff run.model)
  let coeff := p11MultiNarrowCoefficient n p
    (p11StaticInputUnitRoundoff run.model)
    (p11StaticAccumUnitRoundoff run.model)
    (p11StaticScalingThreshold n run.model)
    (p11StaticInputUnderflowEnvelope run.model)
    (p11StaticAccumUnderflowEnvelope run.model)
  have hC : run.computed = p11StaticAccumulationError run +
      (p11StaticAWordApproximation run *
          p11StaticBWordApproximation run -
        p11StaticOmittedWordTail run) := by
    unfold p11StaticAccumulationError
    rw [derivation.retained_partition]
    abel
  have hbound : p11StaticMultiwordForwardError run ≤
      (a + t + 2 * z + z ^ 2) * x * y +
        |derivation.accumulationRemainder| +
        |derivation.omittedRemainder| := by
    unfold p11StaticMultiwordForwardError
    exact p11_product_error_bound run.A
      (p11StaticAWordApproximation run) derivation.AError
      run.B (p11StaticBWordApproximation run) derivation.BError
      run.computed (p11StaticOmittedWordTail run)
      (p11StaticAccumulationError run) z a t
      derivation.accumulationRemainder derivation.omittedRemainder
      derivation.A_decomposition derivation.B_decomposition hC
      (p11_zeta_bound run).1 derivation.A_error_bound
      derivation.B_error_bound derivation.accumulation_error_bound
      derivation.omitted_tail_bound
  have hcoeff : a + t + 2 * z ≤ coeff :=
    p11_narrow_coefficient_bound run derivation.underflowCount
      derivation.underflow_count_bound
  have hx : 0 ≤ x := p11_norm_nonneg run.A
  have hy : 0 ≤ y := p11_norm_nonneg run.B
  have hscaled := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hx hy)
  have hquad_nonneg : 0 ≤ z ^ 2 * x * y := by positivity
  let remainder := |derivation.accumulationRemainder| +
    |derivation.omittedRemainder| + z ^ 2 * x * y
  have hrem : semantics.secondOrder remainder := by
    exact semantics.add_secondOrder
      (semantics.add_secondOrder
        (semantics.abs_secondOrder derivation.accumulation_remainder_second_order)
        (semantics.abs_secondOrder derivation.omitted_remainder_second_order))
      derivation.quadratic_second_order
  have hrem_nonneg : 0 ≤ remainder := by
    dsimp [remainder]
    positivity
  unfold p11FirstOrderLe
  refine ⟨remainder, hrem, ?_⟩
  rw [abs_of_nonneg hrem_nonneg]
  dsimp [p11NormwiseEnvelope, remainder]
  nlinarith [hbound, hscaled]

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
  · intro run derivation
    exact p11_static_narrow_forward_error semantics run derivation
  · intro run derivation
    have h := p11_static_narrow_forward_error semantics run derivation
    have heq :
        p11NormwiseEnvelope
          (p11MultiNarrowCoefficient n p
            (p11StaticInputUnitRoundoff run.model)
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticInputUnderflowEnvelope run.model)
            (p11StaticAccumUnderflowEnvelope run.model))
          run.A run.B =
        p11NormwiseEnvelope
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
          run.A run.B := by
      unfold p11MultiNarrowCoefficient p11NormwiseEnvelope
      ring
    rw [heq] at h
    exact h
  · intro run
    have hp : p - 1 + 1 = p := by
      have hpos := run.word_count_pos
      omega
    have hpow :
        p11StaticInputUnitRoundoff run.model ^ p =
          p11StaticInputUnitRoundoff run.model ^ (p - 1) *
            p11StaticInputUnitRoundoff run.model := by
      calc
        _ = p11StaticInputUnitRoundoff run.model ^ (p - 1 + 1) := by rw [hp]
        _ = _ := pow_succ _ _
    constructor
    · unfold p11MultiInputRoundingCoefficient
        p11SingleInputRoundingCoefficient
      rw [hpow]
      ring
    · unfold p11MultiInputUnderflowCoefficient
        p11SingleInputUnderflowCoefficient
      ring

end VSCLReuse

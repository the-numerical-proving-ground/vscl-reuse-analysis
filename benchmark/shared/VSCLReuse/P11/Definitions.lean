import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt

namespace VSCLReuse

open scoped BigOperators

noncomputable def p11InfNormVec {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ((Finset.univ.sup (fun i : Fin n => Real.toNNReal |x i|) : NNReal) : ℝ)

noncomputable def p11ScalingThreshold (n : ℕ) (fmax Fmax : ℝ) : ℝ :=
  min fmax (Real.sqrt (Fmax / (n : ℝ)))

def p11IsPowerOfTwo (lambda : ℝ) : Prop :=
  ∃ exponent : ℤ, lambda = (2 : ℝ) ^ exponent

noncomputable def p11InfNormRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  let rowSum : Fin m → NNReal :=
    fun i => ∑ j : Fin n, ‖A i j‖₊
  ((Finset.univ.sup rowSum : NNReal) : ℝ)

def p11MultiInputRoundingCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) + 1) * u ^ p

def p11SingleInputRoundingCoefficient (u : ℝ) : ℝ :=
  2 * u

noncomputable def p11SingleInputUnderflowCoefficient
    (n : ℕ) (theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) ^ 2 * theta⁻¹ * gmin

def p11MultiAccumRoundingCoefficient (n p : ℕ) (U : ℝ) : ℝ :=
  ((n : ℝ) + (p : ℝ) ^ 2) * U

def p11MultiRangeFreeCoefficient (n p : ℕ) (u U : ℝ) : ℝ :=
  p11MultiInputRoundingCoefficient p u +
    p11MultiAccumRoundingCoefficient n p U

noncomputable def p11MultiInputUnderflowCoefficient
    (n p : ℕ) (u theta gmin : ℝ) : ℝ :=
  4 * (n : ℝ) * u ^ (p - 1) * theta⁻¹ * gmin

noncomputable def p11MultiAccumUnderflowCoefficient
    (n p : ℕ) (theta Gmin : ℝ) : ℝ :=
  2 * (p : ℝ) * ((p : ℝ) + 1) * (n : ℝ) ^ 2 *
    (theta⁻¹) ^ 2 * Gmin

noncomputable def p11MultiNarrowCoefficient
    (n p : ℕ) (u U theta gmin Gmin : ℝ) : ℝ :=
  p11MultiRangeFreeCoefficient n p u U +
    p11MultiInputUnderflowCoefficient n p u theta gmin +
      p11MultiAccumUnderflowCoefficient n p theta Gmin

noncomputable def p11NormwiseEnvelope {m n q : ℕ}
    (coefficient : ℝ) (A : Fin m → Fin n → ℝ)
    (B : Fin n → Fin q → ℝ) : ℝ :=
  coefficient * p11InfNormRect A * p11InfNormRect B

abbrev P11Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p11UnitRoundoff (precision : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ precision

noncomputable def p11MinNormal (minExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ minExponent

noncomputable def p11MaxFinite (precision : ℕ) (maxExponent : ℤ) : ℝ :=
  (2 : ℝ) ^ maxExponent * (2 - 2 * p11UnitRoundoff precision)

noncomputable def p11UnderflowEnvelope (precision : ℕ)
    (minExponent : ℤ) (hasSubnormals : Bool) : ℝ :=
  match hasSubnormals with
  | false => p11MinNormal minExponent / 2
  | true => p11UnitRoundoff precision * p11MinNormal minExponent

def p11ScaleRows {m n : ℕ} (lambda : Fin m → ℝ)
    (A : P11Matrix m n) : P11Matrix m n :=
  fun i j => lambda i * A i j

def p11ScaleColumns {n q : ℕ} (B : P11Matrix n q)
    (mu : Fin q → ℝ) : P11Matrix n q :=
  fun i j => B i j * mu j

def p11MaximalPowerTwoScale (theta vectorNorm lambda : ℝ) : Prop :=
  p11IsPowerOfTwo lambda ∧ 0 < lambda ∧
    ((vectorNorm = 0 ∧ lambda = 1) ∨
      (0 < vectorNorm ∧ theta / (2 * vectorNorm) < lambda ∧
        lambda ≤ theta / vectorNorm))

def p11RetainedWordPairs (p : ℕ) : List (Fin p × Fin p) :=
  (List.ofFn fun i : Fin p =>
    (List.ofFn fun j : Fin p => (i, j)).filter
      (fun pair => decide (pair.1.val + pair.2.val < p))).flatten

noncomputable def p11UnscaleProduct {m q : ℕ} (lambda : Fin m → ℝ)
    (mu : Fin q → ℝ) (C : P11Matrix m q) : P11Matrix m q :=
  fun i j => (lambda i)⁻¹ * C i j * (mu j)⁻¹

structure P11FirstOrderSemantics where
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0
  add_secondOrder : ∀ {x y}, secondOrder x → secondOrder y →
    secondOrder (x + y)
  abs_secondOrder : ∀ {x}, secondOrder x → secondOrder |x|

def p11FirstOrderLe (semantics : P11FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

structure P11StaticBinaryFormat where
  precision : ℕ
  minExponent : ℤ
  maxExponent : ℤ
  hasSubnormals : Bool
  precision_pos : 0 < precision
  exponent_range_nonempty : minExponent ≤ maxExponent

def p11StaticRepresentable (format : P11StaticBinaryFormat)
    (x : ℝ) : Prop :=
  x = 0 ∨
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ significand : ℕ, ∃ exponent : ℤ,
        x = sign * (significand : ℝ) *
            (2 : ℝ) ^
              (exponent - (format.precision - 1 : ℕ)) ∧
          ((2 ^ (format.precision - 1) ≤ significand ∧
              significand < 2 ^ format.precision ∧
              format.minExponent ≤ exponent ∧
              exponent ≤ format.maxExponent) ∨
            (format.hasSubnormals = true ∧
              exponent = format.minExponent ∧
              0 < significand ∧
              significand < 2 ^ (format.precision - 1)))

structure P11StaticNearestModel1 where
  inputFormat : P11StaticBinaryFormat
  accumulationFormat : P11StaticBinaryFormat
  accumulation_precision :
    inputFormat.precision ≤ accumulationFormat.precision
  accumulation_range :
    accumulationFormat.minExponent ≤ inputFormat.minExponent ∧
      inputFormat.maxExponent ≤ accumulationFormat.maxExponent
  inputRound : ℝ → ℝ
  inputDelta : ℝ → ℝ
  inputEta : ℝ → ℝ
  inputNoOverflow : ℝ → Prop
  input_rounding_equation : ∀ {x}, inputNoOverflow x →
    inputRound x = x * (1 + inputDelta x) + inputEta x
  input_delta_bound : ∀ {x}, inputNoOverflow x →
    |inputDelta x| ≤ p11UnitRoundoff inputFormat.precision
  input_eta_bound : ∀ {x}, inputNoOverflow x →
    |inputEta x| ≤
      p11UnderflowEnvelope inputFormat.precision inputFormat.minExponent
        inputFormat.hasSubnormals
  input_error_exclusive : ∀ {x}, inputNoOverflow x →
    inputEta x * inputDelta x = 0
  input_round_representable : ∀ {x}, inputNoOverflow x →
    p11StaticRepresentable inputFormat (inputRound x)
  input_round_nearest : ∀ {x}, inputNoOverflow x →
    ∀ {y}, p11StaticRepresentable inputFormat y →
      |inputRound x - x| ≤ |y - x|
  accumulationRound : ℝ → ℝ
  accumulationDelta : ℝ → ℝ
  accumulationEta : ℝ → ℝ
  accumulationNoOverflow : ℝ → Prop
  accumulation_rounding_equation : ∀ {x}, accumulationNoOverflow x →
    accumulationRound x =
      x * (1 + accumulationDelta x) + accumulationEta x
  accumulation_delta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationDelta x| ≤
      p11UnitRoundoff accumulationFormat.precision
  accumulation_eta_bound : ∀ {x}, accumulationNoOverflow x →
    |accumulationEta x| ≤
      p11UnderflowEnvelope accumulationFormat.precision
        accumulationFormat.minExponent accumulationFormat.hasSubnormals
  accumulation_error_exclusive : ∀ {x}, accumulationNoOverflow x →
    accumulationEta x * accumulationDelta x = 0
  accumulation_round_representable : ∀ {x}, accumulationNoOverflow x →
    p11StaticRepresentable accumulationFormat (accumulationRound x)
  accumulation_round_nearest : ∀ {x}, accumulationNoOverflow x →
    ∀ {y}, p11StaticRepresentable accumulationFormat y →
      |accumulationRound x - x| ≤ |y - x|

noncomputable def p11StaticInputUnitRoundoff
    (model : P11StaticNearestModel1) : ℝ :=
  p11UnitRoundoff model.inputFormat.precision

noncomputable def p11StaticAccumUnitRoundoff
    (model : P11StaticNearestModel1) : ℝ :=
  p11UnitRoundoff model.accumulationFormat.precision

noncomputable def p11StaticInputUnderflowEnvelope
    (model : P11StaticNearestModel1) : ℝ :=
  p11UnderflowEnvelope model.inputFormat.precision
    model.inputFormat.minExponent model.inputFormat.hasSubnormals

noncomputable def p11StaticAccumUnderflowEnvelope
    (model : P11StaticNearestModel1) : ℝ :=
  p11UnderflowEnvelope model.accumulationFormat.precision
    model.accumulationFormat.minExponent
    model.accumulationFormat.hasSubnormals

noncomputable def p11StaticScalingThreshold (n : ℕ)
    (model : P11StaticNearestModel1) : ℝ :=
  p11ScalingThreshold n
    (p11MaxFinite model.inputFormat.precision
      model.inputFormat.maxExponent)
    (p11MaxFinite model.accumulationFormat.precision
      model.accumulationFormat.maxExponent)

def p11RoundedFoldFrom (round : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | acc, [] => acc
  | acc, term :: terms =>
      p11RoundedFoldFrom round (round (acc + term)) terms

def p11RoundedFoldNoOverflowFrom (allowed : ℝ → Prop)
    (round : ℝ → ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | acc, term :: terms =>
      allowed (acc + term) ∧
        p11RoundedFoldNoOverflowFrom allowed round
          (round (acc + term)) terms

noncomputable def p11StaticAccumulatedInnerProduct {n : ℕ}
    (model : P11StaticNearestModel1) (x y : Fin n → ℝ) : ℝ :=
  p11RoundedFoldFrom model.accumulationRound 0
    ((List.ofFn fun k : Fin n =>
      model.accumulationRound (x k * y k)))

def p11StaticInnerProductNoOverflow {n : ℕ}
    (model : P11StaticNearestModel1) (x y : Fin n → ℝ) : Prop :=
  (∀ k, model.accumulationNoOverflow (x k * y k)) ∧
    p11RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        (List.ofFn fun k : Fin n =>
          model.accumulationRound (x k * y k))

noncomputable def p11StaticRetainedWordProduct {m n q p : ℕ}
    (model : P11StaticNearestModel1) (u : ℝ)
    (Aword : Fin p → P11Matrix m n)
    (Bword : Fin p → P11Matrix n q) : P11Matrix m q :=
  fun row col =>
    p11RoundedFoldFrom model.accumulationRound 0
      ((p11RetainedWordPairs p).map (fun pair =>
        u ^ (pair.1.val + pair.2.val) *
          p11StaticAccumulatedInnerProduct model (Aword pair.1 row)
            (fun k => Bword pair.2 k col)))

structure P11StaticMultiwordRun (m n q p : ℕ) where
  dimension_pos : 0 < m ∧ 0 < n ∧ 0 < q
  word_count_pos : 0 < p
  model : P11StaticNearestModel1
  A : P11Matrix m n
  B : P11Matrix n q
  rowScale : Fin m → ℝ
  columnScale : Fin q → ℝ
  row_scaling_rule : ∀ i,
    p11MaximalPowerTwoScale (p11StaticScalingThreshold n model)
      (p11InfNormVec (A i)) (rowScale i)
  column_scaling_rule : ∀ j,
    p11MaximalPowerTwoScale (p11StaticScalingThreshold n model)
      (p11InfNormVec (fun i => B i j)) (columnScale j)
  scaled_A_bound : ∀ i j,
    |p11ScaleRows rowScale A i j| ≤ p11StaticScalingThreshold n model
  scaled_B_bound : ∀ i j,
    |p11ScaleColumns B columnScale i j| ≤
      p11StaticScalingThreshold n model
  Aword : Fin p → P11Matrix m n
  Bword : Fin p → P11Matrix n q
  Aword_equation : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    Aword i row col = model.inputRound
      ((p11ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p11StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p11StaticInputUnitRoundoff model ^ i.val)
  Aword_no_overflow : ∀ (i : Fin p) (row : Fin m) (col : Fin n),
    model.inputNoOverflow
      ((p11ScaleRows rowScale A row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p11StaticInputUnitRoundoff model ^ k.val *
              Aword k row col)) /
        p11StaticInputUnitRoundoff model ^ i.val)
  Bword_equation : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    Bword i row col = model.inputRound
      ((p11ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p11StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p11StaticInputUnitRoundoff model ^ i.val)
  Bword_no_overflow : ∀ (i : Fin p) (row : Fin n) (col : Fin q),
    model.inputNoOverflow
      ((p11ScaleColumns B columnScale row col -
          Finset.sum
            (Finset.univ.filter (fun k : Fin p => k.val < i.val))
            (fun k => p11StaticInputUnitRoundoff model ^ k.val *
              Bword k row col)) /
        p11StaticInputUnitRoundoff model ^ i.val)
  accumulation_no_overflow : ∀ (i j : Fin p),
    i.val + j.val < p → ∀ (row : Fin m) (col : Fin q),
      p11StaticInnerProductNoOverflow model (Aword i row)
        (fun k => Bword j k col)
  retained_sum_no_overflow : ∀ (row : Fin m) (col : Fin q),
    p11RoundedFoldNoOverflowFrom model.accumulationNoOverflow
      model.accumulationRound 0
        ((p11RetainedWordPairs p).map (fun pair =>
          p11StaticInputUnitRoundoff model ^
              (pair.1.val + pair.2.val) *
            p11StaticAccumulatedInnerProduct model (Aword pair.1 row)
              (fun k => Bword pair.2 k col)))
  computed : P11Matrix m q
  computed_equation :
    computed = p11UnscaleProduct rowScale columnScale
      (p11StaticRetainedWordProduct model
        (p11StaticInputUnitRoundoff model) Aword Bword)

noncomputable def p11StaticAWordApproximation {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : P11Matrix m n :=
  fun row col =>
    (run.rowScale row)⁻¹ *
      ∑ i : Fin p,
        p11StaticInputUnitRoundoff run.model ^ i.val *
          run.Aword i row col

noncomputable def p11StaticBWordApproximation {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : P11Matrix n q :=
  fun row col =>
    (∑ i : Fin p,
        p11StaticInputUnitRoundoff run.model ^ i.val *
          run.Bword i row col) *
      (run.columnScale col)⁻¹

noncomputable def p11StaticExactRetainedWordProduct {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : P11Matrix m q :=
  p11UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => i.val + j.val < p))
          (fun j =>
            p11StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

noncomputable def p11StaticOmittedWordTail {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : P11Matrix m q :=
  p11UnscaleProduct run.rowScale run.columnScale
    (fun row col =>
      ∑ i : Fin p,
        Finset.sum
          (Finset.univ.filter (fun j : Fin p => p ≤ i.val + j.val))
          (fun j =>
            p11StaticInputUnitRoundoff run.model ^ (i.val + j.val) *
              (run.Aword i * run.Bword j) row col))

noncomputable def p11StaticAccumulationError {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : P11Matrix m q :=
  run.computed - p11StaticExactRetainedWordProduct run

noncomputable def p11StaticMultiwordForwardError {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : ℝ :=
  p11InfNormRect (run.computed - run.A * run.B)

noncomputable def p11StaticZeta {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) : ℝ :=
  max (p11StaticInputUnitRoundoff run.model ^ p)
    (2 * (n : ℝ) * p11StaticInputUnitRoundoff run.model ^ (p - 1) *
      (p11StaticScalingThreshold n run.model)⁻¹ *
        p11StaticInputUnderflowEnvelope run.model)

def p11StaticOmittedCoefficient (p : ℕ) (u : ℝ) : ℝ :=
  ((p : ℝ) - 1) * u ^ p

noncomputable def p11StaticAccumulationCoefficient
    (n p : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p11MultiAccumRoundingCoefficient n p U +
    p11MultiAccumUnderflowCoefficient n p theta Gmin

noncomputable def p11StaticRawAccumulationCoefficient
    (n p r : ℕ) (U theta Gmin : ℝ) : ℝ :=
  p11MultiAccumRoundingCoefficient n p U +
    4 * (r : ℝ) * (n : ℝ) * (theta⁻¹) ^ 2 * Gmin

structure P11StaticSection4Derivation
    (semantics : P11FirstOrderSemantics) {m n q p : ℕ}
    (run : P11StaticMultiwordRun m n q p) where
  AError : P11Matrix m n
  BError : P11Matrix n q
  A_decomposition :
    run.A = p11StaticAWordApproximation run + AError
  B_decomposition :
    run.B = p11StaticBWordApproximation run + BError
  A_error_bound :
    p11InfNormRect AError ≤ p11StaticZeta run * p11InfNormRect run.A
  B_error_bound :
    p11InfNormRect BError ≤ p11StaticZeta run * p11InfNormRect run.B
  retained_partition :
    p11StaticExactRetainedWordProduct run =
      p11StaticAWordApproximation run *
          p11StaticBWordApproximation run -
        p11StaticOmittedWordTail run
  omittedRemainder : ℝ
  omitted_remainder_second_order :
    semantics.secondOrder omittedRemainder
  omitted_tail_bound :
    p11InfNormRect (p11StaticOmittedWordTail run) ≤
      p11NormwiseEnvelope
          (p11StaticOmittedCoefficient p
            (p11StaticInputUnitRoundoff run.model)) run.A run.B +
        |omittedRemainder|
  accumulationRemainder : ℝ
  accumulation_remainder_second_order :
    semantics.secondOrder accumulationRemainder
  underflowCount : ℕ
  underflow_count_bound :
    (underflowCount : ℝ) ≤
      (n : ℝ) * (p : ℝ) * ((p : ℝ) + 1) / 2
  accumulation_error_bound :
    p11InfNormRect (p11StaticAccumulationError run) ≤
      p11NormwiseEnvelope
          (p11StaticRawAccumulationCoefficient n p underflowCount
            (p11StaticAccumUnitRoundoff run.model)
            (p11StaticScalingThreshold n run.model)
            (p11StaticAccumUnderflowEnvelope run.model)) run.A run.B +
        |accumulationRemainder|
  quadratic_second_order :
    semantics.secondOrder
      (p11StaticZeta run ^ 2 * p11InfNormRect run.A *
        p11InfNormRect run.B)

end VSCLReuse

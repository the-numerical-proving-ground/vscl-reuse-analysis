import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace VSCLReuse

open scoped BigOperators

noncomputable def p03MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p03MatMul {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p03IdMatrix (n : ℕ) : Fin n → Fin n → ℝ :=
  fun i j ↦ if i = j then 1 else 0

noncomputable def p03MatPow {n : ℕ}
    (B : Fin n → Fin n → ℝ) : ℕ → Fin n → Fin n → ℝ
  | 0 => p03IdMatrix n
  | k + 1 => p03MatMul B (p03MatPow B k)

noncomputable def p03AbsAction {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * |x j|

noncomputable def p03AbsProductAction {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) (q : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, |A i j| * p03AbsAction Ainv q j

def p03VecAdd {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i + y i

def p03VecSub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i - y i

def p03VecScale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ a * x i

def p03AbsVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ |x i|

def p03MatAdd {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j + B i j

def p03MatSub {n : ℕ}
    (A B : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A i j - B i j

def p03MatScale {n : ℕ}
    (a : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ a * A i j

def p03AbsMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ |A i j|

def p03MatNonnegative {n : ℕ} (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, 0 ≤ A i j

inductive P03ResidualPrecision where
  | single
  | double
  deriving DecidableEq

def p03ResidualUnitRoundoff (precision : P03ResidualPrecision)
    (u : ℝ) : ℝ :=
  match precision with
  | .single => u
  | .double => u ^ 2

structure P03ColumnPivotedSolveCertificate {n : ℕ}
    (A : Fin n → Fin n → ℝ) (rhs : Fin n → ℝ)
    (C1 : Fin n → Fin n → ℝ) (u : ℝ) where
  output : Fin n → ℝ
  backwardError : Fin n → ℝ
  equation : p03MatVec A output = p03VecAdd rhs backwardError
  backward_error_bound : ∀ i,
    |backwardError i| ≤
      u * p03MatVec C1 (p03AbsAction A output) i

structure P03IterativeRefinementRun (n : ℕ) where
  dimension_pos : 0 < n
  precision : P03ResidualPrecision
  u : ℝ
  u_pos : 0 < u
  dimension_roundoff_small : (n : ℝ) * u ≤ 1 / 100
  A : Fin n → Fin n → ℝ
  Ainv : Fin n → Fin n → ℝ
  inverse_left : p03MatMul Ainv A = p03IdMatrix n
  inverse_right : p03MatMul A Ainv = p03IdMatrix n
  b : Fin n → ℝ
  exactSolution : Fin n → ℝ
  exact_system : p03MatVec A exactSolution = b
  C1 : Fin n → Fin n → ℝ
  C1_nonnegative : p03MatNonnegative C1
  initialSolve : P03ColumnPivotedSolveCertificate A b C1 u
  iterate : ℕ → Fin n → ℝ
  computedResidual : ℕ → Fin n → ℝ
  correction : ℕ → Fin n → ℝ
  iterate_zero : iterate 0 = fun _ ↦ 0
  iterate_one : iterate 1 = initialSolve.output
  residual_zero : computedResidual 0 = fun i ↦ -b i
  correction_zero : correction 0 = fun i ↦ -iterate 1 i
  correctionSolve : ∀ m,
    P03ColumnPivotedSolveCertificate A (computedResidual (m + 1)) C1 u
  correction_output : ∀ m,
    correction (m + 1) = (correctionSolve m).output
  updateError : ℕ → Fin n → ℝ
  update_equation : ∀ m,
    iterate (m + 1) = p03VecAdd (p03VecSub (iterate m) (correction m))
      (updateError (m + 1))
  update_error_bound : ∀ m i,
    |updateError (m + 1) i| ≤ u * |iterate m i - correction m i|

noncomputable def p03ExactResidualAfterCorrection {n : ℕ}
    (run : P03IterativeRefinementRun n) (m : ℕ) : Fin n → ℝ :=
  p03VecSub (p03MatVec run.A
    (p03VecSub (run.iterate m) (run.correction m))) run.b

def p03BasisVector {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i ↦ if i = j then 1 else 0

structure P03AbsoluteMonotoneNorm (n : ℕ) where
  vecNorm : (Fin n → ℝ) → ℝ
  matrixNorm : (Fin n → Fin n → ℝ) → ℝ
  vec_norm_nonnegative : ∀ x, 0 ≤ vecNorm x
  vec_norm_eq_zero : ∀ x, vecNorm x = 0 ↔ x = 0
  vec_norm_add : ∀ x y,
    vecNorm (p03VecAdd x y) ≤ vecNorm x + vecNorm y
  vec_norm_scale : ∀ a x,
    vecNorm (p03VecScale a x) = |a| * vecNorm x
  vec_norm_absolute : ∀ x, vecNorm (p03AbsVec x) = vecNorm x
  vec_norm_monotone : ∀ x y,
    (∀ i, |x i| ≤ |y i|) → vecNorm x ≤ vecNorm y
  basis_normalized : ∀ j, vecNorm (p03BasisVector j) = 1
  matrix_norm_nonnegative : ∀ A, 0 ≤ matrixNorm A
  matrix_action_bound : ∀ A x,
    vecNorm (p03MatVec A x) ≤ matrixNorm A * vecNorm x
  matrix_norm_least : ∀ A c,
    0 ≤ c → (∀ x, vecNorm (p03MatVec A x) ≤ c * vecNorm x) →
      matrixNorm A ≤ c

noncomputable def p03KappaInverse {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n) : ℝ :=
  norm.matrixNorm (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))

noncomputable def p03Lemma43c3 {n : ℕ}
    (run : P03IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single =>
      (1 + run.u) * ((1 + run.u) ^ n - 1) / run.u ^ 2 - n / run.u
  | .double =>
      (1 + run.u) * (1 + run.u ^ 2) *
        ((1 + run.u ^ 2) ^ n - 1) / run.u ^ 2 - n

def p03Lemma43c4 {n : ℕ} (run : P03IterativeRefinementRun n) : ℝ :=
  match run.precision with
  | .single => 0
  | .double => 1 + run.u

structure P03DimensionOnlyConstantBounds where
  scalar : ℕ → ℝ
  matrixEntry : ℕ → ℝ
  scalar_nonnegative : ∀ n, 0 ≤ scalar n
  matrixEntry_nonnegative : ∀ n, 0 ≤ matrixEntry n

structure P03Lemma43Constants {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds) where
  C2 : Fin n → Fin n → ℝ
  C6 : Fin n → Fin n → ℝ
  C7 : Fin n → Fin n → ℝ
  C8 : Fin n → Fin n → ℝ
  C9 : Fin n → Fin n → ℝ
  C10 : Fin n → Fin n → ℝ
  C11 : Fin n → Fin n → ℝ
  C12 : Fin n → Fin n → ℝ
  c1 : ℝ
  c5 : ℝ
  c8 : ℝ
  C2ResolventInv : Fin n → Fin n → ℝ
  C11ResolventInv : Fin n → Fin n → ℝ
  c1_definition : c1 = norm.matrixNorm run.C1
  c5_definition : c5 =
    n + (p03Lemma43c3 run + p03Lemma43c4 run) * run.u ^ 2 /
      p03ResidualUnitRoundoff run.precision run.u
  C2_resolvent_left :
    p03MatMul
      (p03MatSub (p03IdMatrix n)
        (p03MatScale run.u
          (p03MatMul run.C1
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)))))
      C2ResolventInv = p03IdMatrix n
  C2_resolvent_right :
    p03MatMul C2ResolventInv
      (p03MatSub (p03IdMatrix n)
        (p03MatScale run.u
          (p03MatMul run.C1
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))) =
      p03IdMatrix n
  C2_definition : C2 = p03MatMul C2ResolventInv run.C1
  C6_definition : C6 =
    p03MatAdd C2
      (p03MatScale
        (1 + c5 * p03ResidualUnitRoundoff run.precision run.u / run.u)
        (p03MatAdd (p03IdMatrix n)
          (p03MatScale run.u
            (p03MatMul C2
              (p03MatMul (p03AbsMatrix run.A)
                (p03AbsMatrix run.Ainv))))))
  C7_definition : C7 =
    p03MatScale
      (n + p03Lemma43c3 run * run.u ^ 2 /
        p03ResidualUnitRoundoff run.precision run.u) C2
  C8_definition : C8 = p03MatScale (1 + run.u) C6
  c8_definition : c8 = norm.matrixNorm C8
  C9_definition : C9 =
    p03MatAdd C6 (p03MatScale (p03Lemma43c3 run) (p03IdMatrix n))
  C10_definition : C10 =
    p03MatAdd
      (p03MatAdd C6
        (p03MatScale
          (n * p03ResidualUnitRoundoff run.precision run.u / run.u +
            p03Lemma43c3 run * run.u)
          (p03IdMatrix n)))
      (p03MatScale (p03ResidualUnitRoundoff run.precision run.u)
        (p03MatMul C7
          (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))
  C11_resolvent_left :
    p03MatMul
      (p03MatSub (p03IdMatrix n)
        (p03MatScale run.u
          (p03MatMul C8
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)))))
      C11ResolventInv = p03IdMatrix n
  C11_resolvent_right :
    p03MatMul C11ResolventInv
      (p03MatSub (p03IdMatrix n)
        (p03MatScale run.u
          (p03MatMul C8
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))) =
      p03IdMatrix n
  C11_definition : C11 = p03MatMul C11ResolventInv C9
  C12_definition : C12 =
    p03MatMul C11ResolventInv
      (p03MatAdd (p03MatScale n C8) C7)
  C11_fixed_point : C11 =
    p03MatAdd C9
      (p03MatMul
        (p03MatScale run.u
          (p03MatMul C8
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))
        C11)
  C12_fixed_point : C12 =
    p03MatAdd (p03MatAdd (p03MatScale n C8) C7)
      (p03MatMul
        (p03MatScale run.u
          (p03MatMul C8
            (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv))))
        C12)
  C2_nonnegative : p03MatNonnegative C2
  C6_nonnegative : p03MatNonnegative C6
  C7_nonnegative : p03MatNonnegative C7
  C8_nonnegative : p03MatNonnegative C8
  C9_nonnegative : p03MatNonnegative C9
  C10_nonnegative : p03MatNonnegative C10
  C11_nonnegative : p03MatNonnegative C11
  C12_nonnegative : p03MatNonnegative C12
  c1_nonnegative : 0 ≤ c1
  c8_nonnegative : 0 ≤ c8
  c1_le_c8 : c1 ≤ c8
  C1_dimension_bound : ∀ i j, run.C1 i j ≤ dimensionBounds.matrixEntry n
  C2_dimension_bound : ∀ i j, C2 i j ≤ dimensionBounds.matrixEntry n
  C6_dimension_bound : ∀ i j, C6 i j ≤ dimensionBounds.matrixEntry n
  C7_dimension_bound : ∀ i j, C7 i j ≤ dimensionBounds.matrixEntry n
  C8_dimension_bound : ∀ i j, C8 i j ≤ dimensionBounds.matrixEntry n
  C9_dimension_bound : ∀ i j, C9 i j ≤ dimensionBounds.matrixEntry n
  C10_dimension_bound : ∀ i j, C10 i j ≤ dimensionBounds.matrixEntry n
  C11_dimension_bound : ∀ i j, C11 i j ≤ dimensionBounds.matrixEntry n
  C12_dimension_bound : ∀ i j, C12 i j ≤ dimensionBounds.matrixEntry n
  c1_dimension_bound : c1 ≤ dimensionBounds.scalar n
  c5_dimension_bound : c5 ≤ dimensionBounds.scalar n
  c8_dimension_bound : c8 ≤ dimensionBounds.scalar n

noncomputable def p03Lemma43Propagation {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds) :
    Fin n → Fin n → ℝ :=
  p03MatScale run.u
    (p03MatMul constants.C8
      (p03MatMul (p03AbsMatrix run.A) (p03AbsMatrix run.Ainv)))

noncomputable def p03Lemma43InitialVector {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  p03VecScale run.u
    (p03MatVec (p03MatMul constants.C10 (p03AbsMatrix run.A))
      (p03AbsVec run.exactSolution))

noncomputable def p03Lemma43RecurrenceForcing {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let absx := p03AbsVec run.exactSolution
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  p03VecAdd
    (p03VecScale (n * ubar) (p03MatVec absA absx))
    (p03VecAdd
      (p03VecScale (run.u ^ 2)
        (p03MatVec (p03MatMul constants.C9 absA) absx))
      (p03VecScale (ubar * run.u)
        (p03MatVec
          (p03MatMul
            (p03MatMul constants.C7
              (p03MatMul absA absAinv)) absA) absx)))

noncomputable def p03Lemma43StationaryVector {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds) : Fin n → ℝ :=
  let absA := p03AbsMatrix run.A
  let absAinv := p03AbsMatrix run.Ainv
  let absx := p03AbsVec run.exactSolution
  let ubar := p03ResidualUnitRoundoff run.precision run.u
  p03VecAdd
    (p03VecScale (n * ubar) (p03MatVec absA absx))
    (p03VecAdd
      (p03VecScale (run.u ^ 2)
        (p03MatVec (p03MatMul constants.C11 absA) absx))
      (p03VecScale (ubar * run.u)
        (p03MatVec
          (p03MatMul
            (p03MatMul constants.C12
              (p03MatMul absA absAinv)) absA) absx)))

noncomputable def p03Lemma43Bound {n : ℕ}
    {run : P03IterativeRefinementRun n}
    {norm : P03AbsoluteMonotoneNorm n}
    {dimensionBounds : P03DimensionOnlyConstantBounds}
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (m : ℕ) : Fin n → ℝ :=
  p03VecAdd
    (p03MatVec (p03MatPow (p03Lemma43Propagation constants) m)
      (p03Lemma43InitialVector constants))
    (p03Lemma43StationaryVector constants)

structure P03Lemma43RoundoffAnalysis {n : ℕ}
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (constants : P03Lemma43Constants run norm dimensionBounds) where
  residualError : ℕ → Fin n → ℝ
  residual_equation : ∀ m,
    run.computedResidual m =
      p03VecAdd
        (p03VecSub (p03MatVec run.A (run.iterate m)) run.b)
        (residualError m)
  residual_error_bound : ∀ m i,
    |residualError m i| ≤
      (n * p03ResidualUnitRoundoff run.precision run.u +
          p03Lemma43c3 run * run.u ^ 2) *
        p03MatVec (p03AbsMatrix run.A)
          (p03AbsVec run.exactSolution) i +
      constants.c5 * p03ResidualUnitRoundoff run.precision run.u *
        p03MatVec (p03AbsMatrix run.A)
          (p03AbsVec (p03VecSub (run.iterate m) run.exactSolution)) i +
      run.u *
        |p03MatVec run.A
          (p03VecSub (run.iterate m) run.exactSolution) i|
  correctionError : ℕ → Fin n → ℝ
  correction_equation : ∀ m,
    p03MatVec run.A (run.correction m) =
      p03VecAdd (run.computedResidual m) (correctionError m)
  correction_error_bound :
    constants.c1 * run.u * p03KappaInverse run norm ≤ 1 / 2 →
      ∀ m i,
        |correctionError m i| ≤
          run.u * p03MatVec
            (p03MatMul constants.C2 (p03AbsMatrix run.A))
            (p03AbsVec
              (p03VecSub (run.iterate m) run.exactSolution)) i +
          run.u * p03MatVec
            (p03MatMul
              (p03MatMul constants.C2 (p03AbsMatrix run.A))
              (p03AbsMatrix run.Ainv))
            (p03AbsVec (residualError m)) i

end VSCLReuse

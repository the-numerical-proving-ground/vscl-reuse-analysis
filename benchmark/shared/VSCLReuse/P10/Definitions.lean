import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

abbrev P10Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev P10RectMatrix (m k : ℕ) := Matrix (Fin m) (Fin k) ℝ

abbrev P10Vector (n : ℕ) := Fin n → ℝ

noncomputable def p10VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

noncomputable def p10VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p10VecNorm2Sq x)

def p10Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

def p10Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

def p10ModularEnvelope (alpha beta lambda epsilonC epsilonB ug epsilonX : ℝ) : ℝ :=
  alpha * epsilonC + beta * epsilonB + beta * ug + lambda * epsilonX

noncomputable def p10MatVec {n : ℕ} (A : P10Matrix n)
    (x : P10Vector n) : P10Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p10RectMatVec {m k : ℕ} (A : P10RectMatrix m k)
    (x : P10Vector k) : P10Vector m :=
  fun i ↦ ∑ j : Fin k, A i j * x j

noncomputable def p10SquareRectMul {n k : ℕ} (A : P10Matrix n)
    (B : P10RectMatrix n k) : P10RectMatrix n k :=
  fun i j ↦ ∑ q : Fin n, A i q * B q j

noncomputable def p10RectMatMul {m k q : ℕ} (A : P10RectMatrix m k)
    (B : P10RectMatrix k q) : P10RectMatrix m q :=
  fun i j ↦ ∑ r : Fin k, A i r * B r j

noncomputable def p10FrobNorm {m k : ℕ} (A : P10RectMatrix m k) : ℝ :=
  ‖A‖

def p10Column {m k : ℕ} (A : P10RectMatrix m k) (j : Fin k) : P10Vector m :=
  fun i ↦ A i j

noncomputable def p10Augment {n k : ℕ} (b : P10Vector n)
    (C : P10RectMatrix n k) : P10RectMatrix n (k + 1) :=
  fun i ↦ Fin.cases (b i) (fun j ↦ C i j)

def p10ScaledFirstBasisVector {k : ℕ} (beta : ℝ) : P10Vector (k + 1) :=
  fun i ↦ if i.val = 0 then beta else 0

def p10IsUpperHessenberg {k : ℕ}
    (H : P10RectMatrix (k + 1) k) : Prop :=
  ∀ i j, j.val + 1 < i.val → H i j = 0

def p10InversePair {n : ℕ} (A Ainv : P10Matrix n) : Prop :=
  (∀ x : P10Vector n, p10MatVec Ainv (p10MatVec A x) = x) ∧
    ∀ x : P10Vector n, p10MatVec A (p10MatVec Ainv x) = x

def p10IsLeastSquaresSolution {m k : ℕ} (A : P10RectMatrix m k)
    (b : P10Vector m) (y : P10Vector k) : Prop :=
  ∀ z : P10Vector k,
    p10VecNorm2 (b - p10RectMatVec A y) ≤
      p10VecNorm2 (b - p10RectMatVec A z)

def p10FullColumnRank {m k : ℕ} (A : P10RectMatrix m k) : Prop :=
  Function.Injective (p10RectMatVec A)

structure P10SingularValueData {m k : ℕ} (A : P10RectMatrix m k) where
  sigmaMin : ℝ
  sigmaMax : ℝ
  sigmaMin_nonneg : 0 ≤ sigmaMin
  sigmaMax_nonneg : 0 ≤ sigmaMax
  lower_gain : ∀ x : P10Vector k,
    sigmaMin * p10VecNorm2 x ≤ p10VecNorm2 (p10RectMatVec A x)
  upper_gain : ∀ x : P10Vector k,
    p10VecNorm2 (p10RectMatVec A x) ≤ sigmaMax * p10VecNorm2 x
  min_attained : 0 < k → ∃ x : P10Vector k,
    p10VecNorm2 x = 1 ∧ p10VecNorm2 (p10RectMatVec A x) = sigmaMin
  max_attained : 0 < k → ∃ x : P10Vector k,
    p10VecNorm2 x = 1 ∧ p10VecNorm2 (p10RectMatVec A x) = sigmaMax

structure P10PolynomialFactor where
  degreeN : ℕ
  degreeK : ℕ
  coefficient : Fin (degreeN + 1) → Fin (degreeK + 1) → ℝ
  coefficient_nonneg : ∀ i j, 0 ≤ coefficient i j

noncomputable def p10PolynomialFactorValue (c : P10PolynomialFactor)
    (n k : ℕ) : ℝ :=
  ∑ i : Fin (c.degreeN + 1), ∑ j : Fin (c.degreeK + 1),
    c.coefficient i j * (n : ℝ) ^ (i : ℕ) * (k : ℝ) ^ (j : ℕ)

noncomputable def p10RectConditionF2 {m k : ℕ}
    (A : P10RectMatrix m k) (sigmaMin : ℝ) : ℝ :=
  p10FrobNorm A / sigmaMin

noncomputable def p10ConditionNumberF {n : ℕ}
    (A Ainv : P10Matrix n) : ℝ :=
  p10FrobNorm Ainv * p10FrobNorm A

noncomputable def p10ForwardError {n : ℕ}
    (x xHat : P10Vector n) : ℝ :=
  p10VecNorm2 (xHat - x) / p10VecNorm2 x

structure P10FirstOrderSemantics where
  small : ℝ → Prop
  secondOrder : ℝ → Prop
  zero_secondOrder : secondOrder 0

def p10FirstOrderLe (semantics : P10FirstOrderSemantics)
    (lhs rhs : ℝ) : Prop :=
  ∃ remainder : ℝ,
    semantics.secondOrder remainder ∧ lhs ≤ rhs + |remainder|

noncomputable def p10SafeRelativeMagnitude (actual reference : ℝ) : ℝ :=
  if reference = 0 then 0 else actual / reference

abbrev P10Theorem31Dimension (n : ℕ) :=
  {k : ℕ // 0 < k ∧ k ≤ n}

structure P10Theorem31System (n : ℕ) where
  dimension_pos : 0 < n
  A : P10Matrix n
  Ainv : P10Matrix n
  ML : P10Matrix n
  MLinv : P10Matrix n
  b : P10Vector n
  xExact : P10Vector n
  A_inverse : p10InversePair A Ainv
  ML_inverse : p10InversePair ML MLinv
  b_nonzero : b ≠ 0
  exact_solution : p10MatVec A xExact = b

structure P10Theorem31BasisFamily {n : ℕ}
    (system : P10Theorem31System n) where
  basis : (k : ℕ) → P10RectMatrix n k
  full_rank : ∀ k, 0 < k → k ≤ n → p10FullColumnRank (basis k)
  column_prefix : ∀ k, k < n → ∀ i (j : Fin k),
    basis k i j = basis (k + 1) i j.castSucc

noncomputable def p10StaticExactC {n k : ℕ}
    (system : P10Theorem31System n) (Z : P10RectMatrix n k) :
    P10RectMatrix n k :=
  p10SquareRectMul system.MLinv (p10SquareRectMul system.A Z)

noncomputable def p10StaticExactB {n : ℕ}
    (system : P10Theorem31System n) : P10Vector n :=
  p10MatVec system.MLinv system.b

structure P10Algorithm2Iteration {n : ℕ}
    (system : P10Theorem31System n)
    (semantics : P10FirstOrderSemantics)
    (basisFamily : P10Theorem31BasisFamily system)
    (k : P10Theorem31Dimension n) where
  dimensionFactor : ℝ
  dimensionFactor_one_le : 1 ≤ dimensionFactor
  epsilonC : ℝ
  epsilonB : ℝ
  ug : ℝ
  epsilonX : ℝ
  computedC : P10RectMatrix n k.1
  deltaC : P10RectMatrix n k.1
  computation_equation :
    computedC = p10StaticExactC system (basisFamily.basis k.1) + deltaC
  computedB : P10Vector n
  deltaB : P10Vector n
  rhs_equation : computedB = p10StaticExactB system + deltaB
  vHat : P10RectMatrix n k.1
  vHatNext : P10RectMatrix n (k.1 + 1)
  beta : ℝ
  hessenberg : P10RectMatrix (k.1 + 1) k.1
  hessenberg_upper : p10IsUpperHessenberg hessenberg
  mgs_givens_relation :
    p10Augment computedB computedC =
      p10RectMatMul vHatNext
        (p10Augment (p10ScaledFirstBasisVector beta) hessenberg)
  vHat_prefix : ∀ i (j : Fin k.1),
    vHat i j = vHatNext i j.castSucc
  leastSquaresDeltaB : P10Vector n
  leastSquaresDeltaC : P10RectMatrix n k.1
  yHat : P10Vector k.1
  computedCSpectrum : P10SingularValueData computedC
  exactCSpectrum :
    P10SingularValueData
      (p10StaticExactC system (basisFamily.basis k.1))
  xHat : P10Vector n
  deltaX : P10Vector n
  solution_equation :
    xHat = p10RectMatVec (basisFamily.basis k.1) yHat + deltaX
  vHatSpectrum : P10SingularValueData vHat

structure P10Algorithm2Conditions {n : ℕ}
    {system : P10Theorem31System n}
    {semantics : P10FirstOrderSemantics}
    {basisFamily : P10Theorem31BasisFamily system}
    {k : P10Theorem31Dimension n}
    (iteration : P10Algorithm2Iteration system semantics basisFamily k) where
  accuracy_nonneg :
    0 ≤ iteration.epsilonC ∧ 0 ≤ iteration.epsilonB ∧
      0 ≤ iteration.ug ∧ 0 ≤ iteration.epsilonX
  computation_error_bound :
    p10FrobNorm iteration.deltaC ≤
      iteration.epsilonC *
        p10FrobNorm (p10StaticExactC system (basisFamily.basis k.1))
  rhs_error_bound :
    p10VecNorm2 iteration.deltaB ≤
      iteration.epsilonB * p10VecNorm2 (p10StaticExactB system)
  least_squares_solution :
    p10IsLeastSquaresSolution
      (iteration.computedC + iteration.leastSquaresDeltaC)
      (iteration.computedB + iteration.leastSquaresDeltaB) iteration.yHat
  least_squares_column_bound : ∀ j : Fin (k.1 + 1),
    p10VecNorm2
        (p10Column
          (p10Augment iteration.leastSquaresDeltaB
            iteration.leastSquaresDeltaC) j) ≤
      iteration.dimensionFactor * iteration.ug *
        p10VecNorm2
          (p10Column
            (p10Augment iteration.computedB iteration.computedC) j)
  computedC_numerically_nonsingular :
    semantics.small
      (iteration.ug *
        p10RectConditionF2 iteration.computedC
          iteration.computedCSpectrum.sigmaMin)
  combined_model_small :
    semantics.small
      ((iteration.epsilonC + iteration.epsilonB + iteration.ug) *
        p10RectConditionF2
          (p10StaticExactC system (basisFamily.basis k.1))
          iteration.exactCSpectrum.sigmaMin)
  solution_error_bound :
    p10VecNorm2 iteration.deltaX ≤
      iteration.epsilonX *
        p10VecNorm2 (p10RectMatVec (basisFamily.basis k.1) iteration.yHat)
  solution_small : semantics.small iteration.epsilonX

def p10IterationWellConditioned {n : ℕ}
    {system : P10Theorem31System n}
    {semantics : P10FirstOrderSemantics}
    {basisFamily : P10Theorem31BasisFamily system}
    {k : P10Theorem31Dimension n}
    (iteration : P10Algorithm2Iteration system semantics basisFamily k) : Prop :=
  1 / iteration.vHatSpectrum.sigmaMin ≤ 4 / 3 ∧
    iteration.vHatSpectrum.sigmaMax ≤ 4 / 3

def p10NearRankDeficient {m k : ℕ} (A : P10RectMatrix m k)
    (threshold : ℝ) : Prop :=
  ∃ x : P10Vector k,
    p10VecNorm2 x = 1 ∧
      p10VecNorm2 (p10RectMatVec A x) < threshold

def p10MGSNearDependence {n : ℕ}
    {system : P10Theorem31System n}
    {semantics : P10FirstOrderSemantics}
    {basisFamily : P10Theorem31BasisFamily system}
    {k : P10Theorem31Dimension n}
    (iteration : P10Algorithm2Iteration system semantics basisFamily k) : Prop :=
  ∀ phi : ℝ, 0 < phi →
    p10NearRankDeficient
      (p10Augment
        (fun i ↦ p10StaticExactB system i * phi)
        (p10StaticExactC system (basisFamily.basis k.1)))
      (iteration.dimensionFactor * (iteration.ug + iteration.epsilonC) *
        p10FrobNorm
          (p10Augment
            (fun i ↦ p10StaticExactB system i * phi)
            (p10StaticExactC system (basisFamily.basis k.1))))

structure P10Theorem31Family (n : ℕ)
    (semantics : P10FirstOrderSemantics) where
  system : P10Theorem31System n
  basisFamily : P10Theorem31BasisFamily system
  iteration : ∀ k : P10Theorem31Dimension n,
    P10Algorithm2Iteration system semantics basisFamily k

structure P10MGSSelectionLaw {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics) where
  first_dimension_good :
    p10IterationWellConditioned
      (family.iteration
        ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩)
  loss_implies_near_dependence : ∀ (k : ℕ)
      (hkpos : 0 < k) (hklt : k < n),
    let current : P10Theorem31Dimension n :=
      ⟨k, hkpos, Nat.le_of_lt hklt⟩
    let next : P10Theorem31Dimension n :=
      ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
    ¬ p10IterationWellConditioned (family.iteration next) →
      p10MGSNearDependence (family.iteration current)

noncomputable def p10StaticSplitOperator {n : ℕ}
    (system : P10Theorem31System n) (MRinv : P10Matrix n) :
    P10Matrix n :=
  p10SquareRectMul system.MLinv (p10SquareRectMul system.A MRinv)

noncomputable def p10StaticSplitInverse {n : ℕ}
    (system : P10Theorem31System n) (MR : P10Matrix n) :
    P10Matrix n :=
  p10SquareRectMul MR (p10SquareRectMul system.Ainv system.ML)

structure P10StaticRightQuantities {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (k : P10Theorem31Dimension n)
    (MR MRinv : P10Matrix n) where
  mrzSpectrum :
    P10SingularValueData
      (p10SquareRectMul MR (family.basisFamily.basis k.1))
  mrz_sigmaMin_pos : 0 < mrzSpectrum.sigmaMin
  exactC_norm_pos :
    0 < p10FrobNorm
      (p10StaticExactC family.system (family.basisFamily.basis k.1))
  split_operator_norm_pos :
    0 < p10FrobNorm (p10StaticSplitOperator family.system MRinv)
  mr_condition_pos : 0 < p10ConditionNumberF MR MRinv
  split_condition_pos :
    0 < p10ConditionNumberF
      (p10StaticSplitOperator family.system MRinv)
      (p10StaticSplitInverse family.system MR)

noncomputable def p10StaticAlpha {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {k : P10Theorem31Dimension n}
    (MR MRinv : P10Matrix n)
    (q : P10StaticRightQuantities family k MR MRinv) : ℝ :=
  (p10ConditionNumberF MR MRinv / q.mrzSpectrum.sigmaMin) *
    (p10FrobNorm
        (p10StaticExactC family.system (family.basisFamily.basis k.1)) /
      p10FrobNorm (p10StaticSplitOperator family.system MRinv))

noncomputable def p10StaticBeta {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {k : P10Theorem31Dimension n}
    (MR MRinv : P10Matrix n)
    (q : P10StaticRightQuantities family k MR MRinv) : ℝ :=
  max 1
      ((p10FrobNorm
          (p10StaticExactC family.system (family.basisFamily.basis k.1)) /
          p10FrobNorm (p10StaticSplitOperator family.system MRinv)) /
        q.mrzSpectrum.sigmaMin) *
    p10ConditionNumberF MR MRinv

noncomputable def p10StaticLambda {n : ℕ}
    (system : P10Theorem31System n) (MR MRinv : P10Matrix n) : ℝ :=
  1 /
    p10ConditionNumberF
      (p10StaticSplitOperator system MRinv)
      (p10StaticSplitInverse system MR)

noncomputable def p10StaticXi {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {k : P10Theorem31Dimension n}
    (MR MRinv : P10Matrix n)
    (q : P10StaticRightQuantities family k MR MRinv) : ℝ :=
  let run := family.iteration k
  p10ModularEnvelope (p10StaticAlpha MR MRinv q)
    (p10StaticBeta MR MRinv q)
    (p10StaticLambda family.system MR MRinv)
    run.epsilonC run.epsilonB run.ug run.epsilonX

structure P10StaticAppendixAExpansion {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (k : P10Theorem31Dimension n)
    (MR MRinv : P10Matrix n)
    (q : P10StaticRightQuantities family k MR MRinv) where
  computationContribution : P10Vector n
  rhsContribution : P10Vector n
  gmresContribution : P10Vector n
  solutionContribution : P10Vector n
  remainder : P10Vector n
  error_decomposition :
    (family.iteration k).xHat - family.system.xExact =
      computationContribution + rhsContribution + gmresContribution +
        solutionContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p10VecNorm2 remainder / p10VecNorm2 family.system.xExact)
  computation_gain_bound :
    p10VecNorm2 computationContribution /
          p10VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p10ConditionNumberF
          (p10StaticSplitOperator family.system MRinv)
          (p10StaticSplitInverse family.system MR) *
        (p10StaticAlpha MR MRinv q *
          p10SafeRelativeMagnitude
            (p10FrobNorm (family.iteration k).deltaC)
            (p10FrobNorm
              (p10StaticExactC family.system
                (family.basisFamily.basis k.1))))
  rhs_gain_bound :
    p10VecNorm2 rhsContribution / p10VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p10ConditionNumberF
          (p10StaticSplitOperator family.system MRinv)
          (p10StaticSplitInverse family.system MR) *
        (p10StaticBeta MR MRinv q *
          p10SafeRelativeMagnitude
            (p10VecNorm2 (family.iteration k).deltaB)
            (p10VecNorm2 (p10StaticExactB family.system)))
  gmres_gain_bound :
    p10VecNorm2 gmresContribution / p10VecNorm2 family.system.xExact ≤
      (family.iteration k).dimensionFactor *
        p10ConditionNumberF
          (p10StaticSplitOperator family.system MRinv)
          (p10StaticSplitInverse family.system MR) *
        (p10StaticBeta MR MRinv q * (family.iteration k).ug)
  solution_gain_bound :
    p10VecNorm2 solutionContribution /
          p10VecNorm2 family.system.xExact ≤
      p10ConditionNumberF
          (p10StaticSplitOperator family.system MRinv)
          (p10StaticSplitInverse family.system MR) *
        (p10StaticLambda family.system MR MRinv *
          p10SafeRelativeMagnitude
            (p10VecNorm2 (family.iteration k).deltaX)
            (p10VecNorm2
              (p10RectMatVec (family.basisFamily.basis k.1)
                (family.iteration k).yHat)))

structure P10StaticAppendixATheory {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics) where
  rightQuantities : ∀ (k : P10Theorem31Dimension n)
      (MR MRinv : P10Matrix n), p10InversePair MR MRinv →
    P10StaticRightQuantities family k MR MRinv
  expansion : ∀ (k : P10Theorem31Dimension n),
    p10IterationWellConditioned (family.iteration k) →
    (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) →
    P10Algorithm2Conditions (family.iteration k) →
    ∀ (MR MRinv : P10Matrix n) (hMR : p10InversePair MR MRinv),
      P10StaticAppendixAExpansion family k MR MRinv
        (rightQuantities k MR MRinv hMR)

noncomputable def p10OpNorm2 {n : ℕ} (A : Fin n → Fin n → ℝ) : ℝ :=
  @norm (Matrix (Fin n) (Fin n) ℝ)
    Matrix.instL2OpNormedAddCommGroup.toNorm
    (A : Matrix (Fin n) (Fin n) ℝ)

noncomputable def p10Kappa2 {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : ℝ :=
  p10OpNorm2 A * p10OpNorm2 Ainv

noncomputable def p10InitialResidual {n : ℕ} (A : P10Matrix n)
    (b xInitial : P10Vector n) : P10Vector n :=
  b - p10MatVec A xInitial

noncomputable def p10AbsRectMatVec {m k : ℕ} (A : P10RectMatrix m k)
    (x : P10Vector k) : P10Vector m :=
  fun i ↦ ∑ j : Fin k, |A i j| * |x j|

inductive P10StaticSquareKappaChoice where
  | frobenius
  | inducedTwo

noncomputable def p10StaticKappa (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) : ℝ :=
  match choice with
  | .frobenius => p10ConditionNumberF A Ainv
  | .inducedTwo => p10Kappa2 A Ainv

structure P10StaticFixedRightPreconditioner {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics) where
  MR : P10Matrix n
  MRinv : P10Matrix n
  MR_inverse : p10InversePair MR MRinv
  right_operator_inverse :
    p10InversePair (p10SquareRectMul family.system.A MRinv)
      (p10SquareRectMul MR family.system.Ainv)
  nontrivial : MR ≠ 1
  left_preconditioner_identity : family.system.ML = 1
  left_preconditioner_inverse_identity : family.system.MLinv = 1

noncomputable def p10StaticSystemKappa
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics) : ℝ :=
  p10StaticKappa choice family.system.A family.system.Ainv

noncomputable def p10StaticRightPreconditionerKappa
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    (preconditioner : P10StaticFixedRightPreconditioner family) : ℝ :=
  p10StaticKappa choice preconditioner.MR preconditioner.MRinv

noncomputable def p10StaticRightOperatorKappa
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    (preconditioner : P10StaticFixedRightPreconditioner family) : ℝ :=
  p10StaticKappa choice
    (p10SquareRectMul family.system.A preconditioner.MRinv)
    (p10SquareRectMul preconditioner.MR family.system.Ainv)

noncomputable def p10StaticCondition316Value
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  max (ug * p10StaticRightOperatorKappa choice preconditioner)
    (max (ug * p10StaticRightPreconditionerKappa choice preconditioner)
      (max (um * etaR *
          p10StaticRightPreconditionerKappa choice preconditioner)
        (max (ua * p10StaticSystemKappa choice family * rhoAR)
          (ua * p10StaticRightOperatorKappa choice preconditioner *
            p10StaticRightPreconditionerKappa choice preconditioner))))

noncomputable def p10StaticRightAttainableEnvelope
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (ug um ua etaR rhoAR : ℝ) : ℝ :=
  ug * p10StaticRightOperatorKappa choice preconditioner *
      p10StaticRightPreconditionerKappa choice preconditioner +
    um * etaR * p10StaticRightPreconditionerKappa choice preconditioner +
      ua * p10StaticSystemKappa choice family * rhoAR

noncomputable def p10StaticFlexibleAttainableEnvelope
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (ug ua rhoAR : ℝ) : ℝ :=
  ug * p10StaticRightOperatorKappa choice preconditioner *
      p10StaticRightPreconditionerKappa choice preconditioner +
    ua * p10StaticSystemKappa choice family * rhoAR

structure P10StaticFixedRightCore {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (k : P10Theorem31Dimension n) where
  ug : ℝ
  um : ℝ
  ua : ℝ
  etaR : ℝ
  rhoAR : ℝ
  zHat : P10RectMatrix n k.1
  preconditionerDelta : Fin k.1 → P10Matrix n
  preconditioner_application : ∀ j,
    p10Column zHat j =
      p10MatVec (preconditioner.MRinv + preconditionerDelta j)
        (p10Column (family.iteration k).vHat j)
  matrixDelta : Fin k.1 → P10Matrix n
  matrix_application : ∀ j,
    p10Column (family.iteration k).computedC j =
      p10MatVec (family.system.A + matrixDelta j) (p10Column zHat j)
  search_space_equation : ∀ j,
    p10Column (family.basisFamily.basis k.1) j =
      p10Column zHat j +
        p10MatVec family.system.Ainv
          (p10MatVec (matrixDelta j) (p10Column zHat j))
  computation_exact : (family.iteration k).deltaC = 0
  computation_accuracy_zero : (family.iteration k).epsilonC = 0
  rhs_exact : (family.iteration k).deltaB = 0
  rhs_accuracy_zero : (family.iteration k).epsilonB = 0
  gmresMagnitude : ℝ
  basisPreconditionerMagnitude : ℝ
  matrixMagnitude : ℝ

structure P10StaticFixedRightCoreConditions
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {preconditioner : P10StaticFixedRightPreconditioner family}
    {k : P10Theorem31Dimension n}
    (core : P10StaticFixedRightCore family preconditioner k) where
  parameters_nonneg :
    0 ≤ core.ug ∧ 0 ≤ core.um ∧ 0 ≤ core.ua ∧ 0 ≤ core.etaR ∧
      0 ≤ core.rhoAR
  magnitudes_nonneg :
    0 ≤ core.gmresMagnitude ∧ 0 ≤ core.basisPreconditionerMagnitude ∧
      0 ≤ core.matrixMagnitude
  least_squares_solution :
    p10IsLeastSquaresSolution
      ((family.iteration k).computedC +
        (family.iteration k).leastSquaresDeltaC)
      ((family.iteration k).computedB +
        (family.iteration k).leastSquaresDeltaB)
      (family.iteration k).yHat
  least_squares_error_covered : ∀ j : Fin (k.1 + 1),
    p10VecNorm2
        (p10Column
          (p10Augment (family.iteration k).leastSquaresDeltaB
            (family.iteration k).leastSquaresDeltaC) j) ≤
      core.gmresMagnitude *
        p10VecNorm2
          (p10Column
            (p10Augment (family.iteration k).computedB
              (family.iteration k).computedC) j)
  basis_preconditioner_error_covered : ∀ j,
    p10FrobNorm (core.preconditionerDelta j) ≤
      core.basisPreconditionerMagnitude * p10FrobNorm preconditioner.MRinv
  matrix_error_covered : ∀ j i q,
    |core.matrixDelta j i q| ≤ core.matrixMagnitude * |family.system.A i q|
  gmres_magnitude_bound :
    core.gmresMagnitude ≤ (family.iteration k).dimensionFactor * core.ug
  basis_preconditioner_magnitude_bound :
    core.basisPreconditionerMagnitude ≤
      (family.iteration k).dimensionFactor * core.um * core.etaR
  matrix_magnitude_bound :
    core.matrixMagnitude ≤ (family.iteration k).dimensionFactor * core.ua
  rho_denominator_pos :
    0 < p10VecNorm2
      (p10RectMatVec core.zHat (family.iteration k).yHat)
  rho_equation :
    core.rhoAR =
      p10VecNorm2 (p10AbsRectMatVec core.zHat (family.iteration k).yHat) /
        p10VecNorm2 (p10RectMatVec core.zHat (family.iteration k).yHat)
  condition316 :
    semantics.small
      (p10StaticCondition316Value choice preconditioner
        core.ug core.um core.ua core.etaR core.rhoAR)

structure P10StaticRightIteration {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (k : P10Theorem31Dimension n) where
  core : P10StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P10RectMatrix n k.1
  solutionPreconditionerDelta : P10Matrix n
  solution_equation :
    (family.iteration k).xHat =
      p10MatVec (preconditioner.MRinv + solutionPreconditionerDelta)
        (p10RectMatVec
          ((family.iteration k).vHat + solutionBasisDelta)
          (family.iteration k).yHat)
  reapplicationMagnitude : ℝ

structure P10StaticRightConditions
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {preconditioner : P10StaticFixedRightPreconditioner family}
    {k : P10Theorem31Dimension n}
    (iteration : P10StaticRightIteration family preconditioner k) where
  core : P10StaticFixedRightCoreConditions choice iteration.core
  reapplication_magnitude_nonneg : 0 ≤ iteration.reapplicationMagnitude
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |(family.iteration k).vHat i j|
  solution_preconditioner_error_covered :
    p10FrobNorm iteration.solutionPreconditionerDelta ≤
      iteration.reapplicationMagnitude * p10FrobNorm preconditioner.MRinv
  reapplication_magnitude_bound :
    iteration.reapplicationMagnitude ≤
      (family.iteration k).dimensionFactor *
        iteration.core.um * iteration.core.etaR

structure P10StaticFlexibleIteration {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (preconditioner : P10StaticFixedRightPreconditioner family)
    (k : P10Theorem31Dimension n) where
  core : P10StaticFixedRightCore family preconditioner k
  solutionBasisDelta : P10RectMatrix n k.1
  solution_equation :
    (family.iteration k).xHat =
      p10RectMatVec (core.zHat + solutionBasisDelta)
        (family.iteration k).yHat

structure P10StaticFlexibleConditions
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    {family : P10Theorem31Family n semantics}
    {preconditioner : P10StaticFixedRightPreconditioner family}
    {k : P10Theorem31Dimension n}
    (iteration : P10StaticFlexibleIteration family preconditioner k) where
  core : P10StaticFixedRightCoreConditions choice iteration.core
  solution_basis_error_covered : ∀ i j,
    |iteration.solutionBasisDelta i j| ≤
      iteration.core.gmresMagnitude * |iteration.core.zHat i j|

structure P10StaticRightFamily (n : ℕ)
    (semantics : P10FirstOrderSemantics) where
  family : P10Theorem31Family n semantics
  preconditioner : P10StaticFixedRightPreconditioner family
  iteration : ∀ k : P10Theorem31Dimension n,
    P10StaticRightIteration family preconditioner k

structure P10StaticFlexibleFamily (n : ℕ)
    (semantics : P10FirstOrderSemantics) where
  family : P10Theorem31Family n semantics
  preconditioner : P10StaticFixedRightPreconditioner family
  iteration : ∀ k : P10Theorem31Dimension n,
    P10StaticFlexibleIteration family preconditioner k

structure P10StaticRightAppendixCExpansion
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (right : P10StaticRightFamily n semantics)
    (k : P10Theorem31Dimension n) where
  gmresContribution : P10Vector n
  reapplicationContribution : P10Vector n
  matrixContribution : P10Vector n
  remainder : P10Vector n
  error_decomposition :
    (right.family.iteration k).xHat - right.family.system.xExact =
      gmresContribution + reapplicationContribution + matrixContribution +
        remainder
  remainder_second_order :
    semantics.secondOrder
      (p10VecNorm2 remainder / p10VecNorm2 right.family.system.xExact)
  gmres_gain_bound :
    p10VecNorm2 gmresContribution /
          p10VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.gmresMagnitude *
        p10StaticRightOperatorKappa choice right.preconditioner *
          p10StaticRightPreconditionerKappa choice right.preconditioner
  reapplication_gain_bound :
    p10VecNorm2 reapplicationContribution /
          p10VecNorm2 right.family.system.xExact ≤
      (right.iteration k).reapplicationMagnitude *
        p10StaticRightPreconditionerKappa choice right.preconditioner
  matrix_gain_bound :
    p10VecNorm2 matrixContribution /
          p10VecNorm2 right.family.system.xExact ≤
      (right.iteration k).core.matrixMagnitude *
        p10StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR

structure P10StaticFlexibleAppendixDExpansion
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (flexible : P10StaticFlexibleFamily n semantics)
    (k : P10Theorem31Dimension n) where
  gmresContribution : P10Vector n
  matrixContribution : P10Vector n
  remainder : P10Vector n
  error_decomposition :
    (flexible.family.iteration k).xHat - flexible.family.system.xExact =
      gmresContribution + matrixContribution + remainder
  remainder_second_order :
    semantics.secondOrder
      (p10VecNorm2 remainder / p10VecNorm2 flexible.family.system.xExact)
  gmres_gain_bound :
    p10VecNorm2 gmresContribution /
          p10VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.gmresMagnitude *
        p10StaticRightOperatorKappa choice flexible.preconditioner *
          p10StaticRightPreconditionerKappa choice flexible.preconditioner
  matrix_gain_bound :
    p10VecNorm2 matrixContribution /
          p10VecNorm2 flexible.family.system.xExact ≤
      (flexible.iteration k).core.matrixMagnitude *
        p10StaticSystemKappa choice flexible.family *
          (flexible.iteration k).core.rhoAR

structure P10StaticRightAppendixCTheory
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (right : P10StaticRightFamily n semantics) where
  expansion : ∀ (k : P10Theorem31Dimension n),
    p10IterationWellConditioned (right.family.iteration k) →
    (k.1 = n ∨ p10MGSNearDependence (right.family.iteration k)) →
    P10StaticRightConditions choice (right.iteration k) →
      P10StaticRightAppendixCExpansion choice right k

structure P10StaticFlexibleAppendixDTheory
    (choice : P10StaticSquareKappaChoice) {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (flexible : P10StaticFlexibleFamily n semantics) where
  expansion : ∀ (k : P10Theorem31Dimension n),
    p10IterationWellConditioned (flexible.family.iteration k) →
    (k.1 = n ∨ p10MGSNearDependence (flexible.family.iteration k)) →
    P10StaticFlexibleConditions choice (flexible.iteration k) →
      P10StaticFlexibleAppendixDExpansion choice flexible k

end VSCLReuse

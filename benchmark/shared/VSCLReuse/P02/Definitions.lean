import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace VSCLReuse

open scoped BigOperators

noncomputable def p02VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p02FrobNorm {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

noncomputable def p02FiniteId {ι : Type*} [DecidableEq ι] : ι → ι → ℝ :=
  fun i j ↦ if i = j then 1 else 0

noncomputable def p02RectMatMul {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (R : Fin m → Fin n → ℝ) :
    Fin m → Fin n → ℝ :=
  fun i j ↦ ∑ k : Fin m, Q i k * R k j

noncomputable def p02MatVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

def p02RectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Prop :=
  ∀ x, p02VecNorm2 (p02MatVec A x) ≤ L * p02VecNorm2 x

noncomputable def p02HouseholderMatrix {m : ℕ}
    (v : Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun i j ↦ p02FiniteId i j - v i * v j

def p02Orthogonal {m : ℕ} (Q : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j, (∑ k : Fin m, Q k i * Q k j) = p02FiniteId i j

def p02UpperTrapezoidal {m n : ℕ}
    (R : Fin m → Fin n → ℝ) : Prop :=
  ∀ i j, j.val < i.val → R i j = 0

noncomputable def p02GammaTilde (k : ℕ) (lambda u : ℝ) : ℝ :=
  Real.exp
      ((lambda * Real.sqrt (k : ℝ) * u + (k : ℝ) * u ^ 2) /
        (1 - u)) -
    1

noncomputable def p02QRLeadingCoefficient
    (c6 : ℕ) (lambda : ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  (c6 : ℝ) * lambda * Real.sqrt (n : ℝ) *
    p02GammaTilde m lambda u

noncomputable def p02P4 (lambda : ℝ) (m n : ℕ) : ℝ :=
  1 - 2 * (m : ℝ) * (n : ℝ) * Real.exp (-lambda ^ 2)

def p02SecondOrderAtZero (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhds 0] fun u : ℝ ↦ u ^ 2

def p02SecondOrderAtZeroRight (remainder : ℝ → ℝ) : Prop :=
  remainder =O[nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)] fun u : ℝ ↦ u ^ 2

def P02SecondOrderControl (remainder : ℝ → ℝ) (u0 : ℝ) : Prop :=
  ∃ constant : ℝ, 0 ≤ constant ∧
    p02SecondOrderAtZero remainder ∧
    ∀ u, |u| ≤ |u0| → |remainder u| ≤ constant * u ^ 2

def p02PriorErrors {Ω : Type*} {steps : ℕ}
    (error : Fin steps → Ω → ℝ) (k : Fin steps) (omega : Ω) :
    Fin k.val → ℝ :=
  fun i ↦ error ⟨i.val, lt_trans i.isLt k.isLt⟩ omega

def p02MeanIndependent {Ω : Type*} [MeasurableSpace Ω]
    (mu : MeasureTheory.Measure Ω) {steps : ℕ}
    (error : Fin steps → Ω → ℝ) : Prop :=
  ∀ (k : Fin steps) (g : (Fin k.val → ℝ) → ℝ),
    MeasureTheory.Integrable
        (fun omega ↦ g (p02PriorErrors error k omega)) mu →
      MeasureTheory.Integrable
        (fun omega ↦
          g (p02PriorErrors error k omega) * error k omega) mu →
      (∫ omega,
          g (p02PriorErrors error k omega) * error k omega ∂mu) =
        (∫ omega, g (p02PriorErrors error k omega) ∂mu) *
          ∫ omega, error k omega ∂mu

structure P02Model15 (Ω : Type*) [MeasurableSpace Ω] where
  probability : MeasureTheory.Measure Ω
  probability_univ : probability Set.univ = 1
  operationCount : ℕ
  exactValue : Fin operationCount → Ω → ℝ
  computedValue : Fin operationCount → Ω → ℝ
  error : Fin operationCount → Ω → ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  unitRoundoff_lt_one : unitRoundoff < 1
  relative_error : ∀ k omega,
    computedValue k omega = exactValue k omega * (1 + error k omega)
  error_bound : ∀ k omega, |error k omega| ≤ unitRoundoff
  error_measurable : ∀ k, Measurable (error k)
  error_integrable : ∀ k,
    MeasureTheory.Integrable (error k) probability
  error_mean_zero : ∀ k, ∫ omega, error k omega ∂probability = 0
  error_mean_independent : p02MeanIndependent probability error

def p02MatrixFamilyIsBigOAtZero {m : ℕ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ) (scale : ℝ → ℝ) : Prop :=
  ∀ i j, (fun u ↦ A u i j) =O[nhds 0] scale

def p02MatrixSecondOrderAtZero {m : ℕ}
    (remainder : ℝ → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  p02MatrixFamilyIsBigOAtZero remainder fun u ↦ u ^ 2

noncomputable def p02HouseholderProduct {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ) :
    ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | k + 1 => P k * p02HouseholderProduct P k

noncomputable def p02PerturbedHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 1
  | u, omega, k + 1 =>
      (P k + DeltaP u k omega) *
        p02PerturbedHouseholderProduct P DeltaP u omega k

noncomputable def p02FirstOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p02FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega * p02HouseholderProduct P k

noncomputable def p02HigherOrderHouseholderProduct {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ) :
    ℝ → Omega → ℕ → Matrix (Fin m) (Fin m) ℝ
  | _, _, 0 => 0
  | u, omega, k + 1 =>
      P k * p02HigherOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p02FirstOrderHouseholderProduct P DeltaP u omega k +
        DeltaP u k omega *
          p02HigherOrderHouseholderProduct P DeltaP u omega k

noncomputable def p02HouseholderSequenceMatrix {m : ℕ}
    (v : ℕ → Fin m → ℝ) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  p02HouseholderMatrix (v j)

structure P02HouseholderApplicationFamily
    (Omega : Type*) [MeasurableSpace Omega] (m r : ℕ)
    (model : P02Model15 Omega) where
  dimension_pos : 0 < m
  steps_pos : 0 < r
  b : Fin m → ℝ
  householderVector : ℕ → Fin m → ℝ
  localPerturbation :
    ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ
  computed : ℝ → Omega → Fin m → ℝ
  outputIndex : Fin m → Fin model.operationCount
  householder_normalized : ∀ j, j < r →
    ∑ i : Fin m, householderVector j i ^ 2 = 2
  householder_involutory : ∀ j, j < r →
    p02HouseholderSequenceMatrix householderVector j *
        p02HouseholderSequenceMatrix householderVector j = 1
  computed_product : ∀ u omega,
    computed u omega =
      p02MatVec
        (p02PerturbedHouseholderProduct
          (p02HouseholderSequenceMatrix householderVector)
          localPerturbation u omega r)
        b
  output_from_trace : ∀ omega i,
    computed model.unitRoundoff omega i =
      model.computedValue (outputIndex i) omega

structure P02Lemma42VectorAssumption
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) where
  localEvent : Set Omega
  localEvent_measurable : MeasurableSet localEvent
  localEvent_iff : ∀ omega,
    omega ∈ localEvent ↔
      ∀ j : Fin r,
        p02RectOpNorm2Le
          (run.localPerturbation model.unitRoundoff j.val omega)
          ((c5 : ℝ) * p02GammaTilde m lambda model.unitRoundoff)
  local_first_order : ∀ omega, omega ∈ localEvent →
    ∀ j, j < r →
      p02MatrixFamilyIsBigOAtZero
        (fun u ↦ run.localPerturbation u j omega) (fun u ↦ u)
  probability_one : model.probability localEvent = 1

noncomputable def p02ApplicationExactState
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model) : Fin m → ℝ :=
  p02MatVec
    (p02HouseholderProduct
      (p02HouseholderSequenceMatrix run.householderVector) r)
    run.b

noncomputable def p02TransformedHouseholderInsertion
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose (p02HouseholderProduct P (j + 1)) *
    DeltaP u j omega * p02HouseholderProduct P j

noncomputable def p02TransformedHouseholderInsertionSum
    {Omega : Type*} {m : ℕ}
    (P : ℕ → Matrix (Fin m) (Fin m) ℝ)
    (DeltaP : ℝ → ℕ → Omega → Matrix (Fin m) (Fin m) ℝ)
    (u : ℝ) (omega : Omega) (k : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ j ∈ Finset.range k,
    p02TransformedHouseholderInsertion P DeltaP u omega j

noncomputable def p02ApplicationQ
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.transpose
    (p02HouseholderProduct
      (p02HouseholderSequenceMatrix run.householderVector) r)

noncomputable def p02ApplicationFirstOrderMatrix
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p02FirstOrderHouseholderProduct
    (p02HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

noncomputable def p02ApplicationF
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) (j : Fin r) : Matrix (Fin m) (Fin m) ℝ :=
  p02TransformedHouseholderInsertion
    (p02HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega j.val

noncomputable def p02ApplicationFSum
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    {model : P02Model15 Omega}
    (run : P02HouseholderApplicationFamily Omega m r model)
    (u : ℝ) (omega : Omega) : Matrix (Fin m) (Fin m) ℝ :=
  p02TransformedHouseholderInsertionSum
    (p02HouseholderSequenceMatrix run.householderVector)
    run.localPerturbation u omega r

end VSCLReuse

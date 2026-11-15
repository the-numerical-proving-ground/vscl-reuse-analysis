import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace VSCLReuse

open scoped BigOperators

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

noncomputable def p04MatVec {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

def p04Transpose {n : ℕ}
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ A j i

def p04ScaleMatrix {n : ℕ}
    (s : ℝ) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j ↦ s * A i j

def p04IsLeftInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, Ainv i k * A k j = if i = j then 1 else 0

def p04IsRightInverse {n : ℕ}
    (A Ainv : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j, ∑ k : Fin n, A i k * Ainv k j = if i = j then 1 else 0

def p04Orthogonal {n : ℕ} (Q : Fin n → Fin n → ℝ) : Prop :=
  p04IsLeftInverse Q (p04Transpose Q) ∧
    p04IsRightInverse Q (p04Transpose Q)

noncomputable def p04VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ 2

noncomputable def p04VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p04VecNorm2Sq x)

noncomputable def p04Rms {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  p04VecNorm2 x / Real.sqrt (n : ℝ)

noncomputable def p04Max {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

noncomputable def p04VectorSum {m n : ℕ}
    (term : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ ∑ i : Fin m, term i j

noncomputable def p04FourierTransform {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun k ↦ ∑ j : ZMod n, ZMod.stdAddChar (j * k) * x j

theorem p04StdAddChar_positive_exp {n : ℕ} [NeZero n] (j : ZMod n) :
    ZMod.stdAddChar j =
      Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / (n : ℂ)) := by
  rw [← ZMod.natCast_zmod_val j]
  simpa using (ZMod.stdAddChar_coe (N := n) (j.val : ℤ))

def p04ComplexVecAdd {n : ℕ} (x y : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x i + y i

def p04ComplexVecSub {n : ℕ} (x y : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x i - y i

noncomputable def p04ComplexNorm2Sq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  ∑ i : ZMod n, ‖x i‖ ^ 2

noncomputable def p04ComplexNorm2 {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  Real.sqrt (p04ComplexNorm2Sq x)

noncomputable def p04ComplexRms {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  p04ComplexNorm2 x / Real.sqrt (n : ℝ)

noncomputable def p04ComplexMax {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦ ‖x i‖

theorem p04ComplexNorm_le_max {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) (i : ZMod n) :
    ‖x i‖ ≤ p04ComplexMax x := by
  exact Finset.le_sup' (fun j : ZMod n ↦ ‖x j‖) (Finset.mem_univ i)

noncomputable def p04Alpha (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then Real.sqrt 2
  else if q = 4 then 5
  else 2 * Real.sqrt q * ((q : ℝ) + γ)

inductive P04FftVariant
  | cooleyTukey
  | sandeTukey
  deriving DecidableEq

structure P04MixedRadixStage (n : ℕ) [NeZero n] where
  radix : ℕ
  radix_two_le : 2 ≤ radix
  radix_ne_zero : radix ≠ 0
  blockCount : ℕ
  blockCount_ne_zero : blockCount ≠ 0
  order_eq : blockCount * radix = n
  reindex : Fin blockCount × ZMod radix ≃ ZMod n
  permutation : ZMod n ≃ ZMod n
  useTwiddle : Bool
  twiddleExponent : ZMod n → ZMod n

instance p04MixedRadixStageRadixNeZero {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) : NeZero stage.radix :=
  ⟨stage.radix_ne_zero⟩

noncomputable def p04MixedRadixBlockApply {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  exact fun i ↦
    let bi := stage.reindex.symm i
    ∑ j : ZMod stage.radix,
      ZMod.stdAddChar (j * bi.2) * permuted (stage.reindex (bi.1, j))

noncomputable def p04MixedRadixTwiddleApply {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦
    if stage.useTwiddle then
      ZMod.stdAddChar (stage.twiddleExponent i) * x i
    else x i

noncomputable def p04MixedRadixStageApply {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p04MixedRadixTwiddleApply stage (p04MixedRadixBlockApply stage x)

noncomputable def p04ApplyMixedRadixStages {m n : ℕ} [NeZero n]
    (stages : Fin m → P04MixedRadixStage n) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  (List.ofFn stages).foldl (fun state stage ↦ p04MixedRadixStageApply stage state) x

def p04Permute {n : ℕ} (permutation : ZMod n ≃ ZMod n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦ x (permutation i)

structure P04MixedRadixFftPlan (n : ℕ) [NeZero n] where
  stageCount : ℕ
  stageCount_pos : 0 < stageCount
  stage : Fin stageCount → P04MixedRadixStage n
  order_factorization : (∏ i : Fin stageCount, (stage i).radix) = n
  twiddle_pattern : ∀ i : Fin stageCount,
    (stage i).useTwiddle = decide (i.val + 1 < stageCount)
  finalPermutation : ZMod n ≃ ZMod n
  variant : P04FftVariant
  exact_factorization : ∀ x : ZMod n → ℂ,
    p04Permute finalPermutation (p04ApplyMixedRadixStages stage x) =
      p04FourierTransform x
  stage_norm_scaling : ∀ i : Fin stageCount, ∀ x : ZMod n → ℂ,
    p04ComplexNorm2 (p04MixedRadixStageApply (stage i) x) =
      Real.sqrt ((stage i).radix : ℝ) * p04ComplexNorm2 x
  fourier_surjective : Function.Surjective
    (p04FourierTransform : (ZMod n → ℂ) → ZMod n → ℂ)
  fourier_rms_scaling : ∀ x : ZMod n → ℂ,
    p04ComplexRms (p04FourierTransform x) =
      Real.sqrt (n : ℝ) * p04ComplexRms x

noncomputable def p04K {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) : ℝ :=
  (∑ i : Fin plan.stageCount, p04Alpha (plan.stage i).radix γ) +
    ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ)

structure P04WilkinsonModel where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  gamma : ℝ
  gamma_nonneg : 0 ≤ gamma
  flAdd : ℝ → ℝ → ℝ
  flMul : ℝ → ℝ → ℝ
  flSin : ℝ → ℝ
  flCos : ℝ → ℝ
  flInput : ℂ → ℂ
  add_model : ∀ a b : ℝ, ∃ θa θb : ℝ,
    |θa| ≤ 1 ∧ |θb| ≤ 1 ∧
      flAdd a b = a * (1 + θa * epsilon) + b * (1 + θb * epsilon)
  mul_model : ∀ a b : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flMul a b = a * b * (1 + θ * epsilon)
  sin_model : ∀ a : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flSin a = Real.sin a + gamma * θ * epsilon
  cos_model : ∀ a : ℝ, ∃ θ : ℝ,
    |θ| ≤ 1 ∧ flCos a = Real.cos a + gamma * θ * epsilon

noncomputable def p04RootAngle {q : ℕ} [NeZero q] (j : ZMod q) : ℝ :=
  2 * Real.pi * (j.val : ℝ) / (q : ℝ)

noncomputable def p04RoundedRoot {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) : ℂ :=
  ⟨model.flCos (p04RootAngle j), model.flSin (p04RootAngle j)⟩

noncomputable def p04RoundedComplexMul (model : P04WilkinsonModel)
    (x y : ℂ) : ℂ :=
  ⟨model.flAdd (model.flMul x.re y.re) (-model.flMul x.im y.im),
    model.flAdd (model.flMul x.re y.im) (model.flMul x.im y.re)⟩

noncomputable def p04RoundedComplexAdd (model : P04WilkinsonModel)
    (x y : ℂ) : ℂ :=
  ⟨model.flAdd x.re y.re, model.flAdd x.im y.im⟩

noncomputable def p04RoundedComplexSum {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) : ℂ :=
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  ⟨recursiveSum model.flAdd q fun i ↦ (term (index i)).re,
    recursiveSum model.flAdd q fun i ↦ (term (index i)).im⟩

def p04RadixTwoCoefficientApply (j : ZMod 2) (x : ℂ) : ℂ :=
  if j = 0 then x else -x

def p04RadixFourCoefficientApply (j : ZMod 4) (x : ℂ) : ℂ :=
  if j = 0 then x
  else if j = 1 then ⟨-x.im, x.re⟩
  else if j = 2 then -x
  else ⟨x.im, -x.re⟩

noncomputable def p04RoundedRadixTwoBlock (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) : ℂ :=
  p04RoundedComplexSum model fun j ↦
    p04RadixTwoCoefficientApply (j * k) (x j)

noncomputable def p04RoundedRadixFourBlock (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) : ℂ :=
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i ↦
    p04RadixFourCoefficientApply (index i * k) (x (index i))
  p04RoundedComplexAdd model
    (p04RoundedComplexAdd model (term 0) (term 1))
    (p04RoundedComplexAdd model (term 2) (term 3))

theorem p04RoundedRadixTwoBlock_congr
    (model₁ model₂ : P04WilkinsonModel)
    (hadd : model₁.flAdd = model₂.flAdd)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    p04RoundedRadixTwoBlock model₁ x k =
      p04RoundedRadixTwoBlock model₂ x k := by
  simp [p04RoundedRadixTwoBlock, p04RoundedComplexSum, hadd]

theorem p04RoundedRadixFourBlock_congr
    (model₁ model₂ : P04WilkinsonModel)
    (hadd : model₁.flAdd = model₂.flAdd)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    p04RoundedRadixFourBlock model₁ x k =
      p04RoundedRadixFourBlock model₂ x k := by
  simp [p04RoundedRadixFourBlock, p04RoundedComplexAdd, hadd]

noncomputable def p04RoundedGenericRadixBlock {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  p04RoundedComplexSum model fun j ↦
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)

noncomputable def p04RoundedMixedRadixBlockApply {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let permuted : ZMod n → ℂ := fun i ↦ x (stage.permutation i)
  exact fun i ↦
    let bi := stage.reindex.symm i
    if h2 : stage.radix = 2 then
      p04RoundedRadixTwoBlock model
        (fun j : ZMod 2 ↦
          permuted (stage.reindex (bi.1, h2.symm ▸ j)))
        (h2 ▸ bi.2)
    else if h4 : stage.radix = 4 then
      p04RoundedRadixFourBlock model
        (fun j : ZMod 4 ↦
          permuted (stage.reindex (bi.1, h4.symm ▸ j)))
        (h4 ▸ bi.2)
    else
      p04RoundedGenericRadixBlock model
        (fun j ↦ permuted (stage.reindex (bi.1, j))) bi.2

noncomputable def p04RoundedMixedRadixTwiddleApply {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  fun i ↦
    if stage.useTwiddle then
      p04RoundedComplexMul model
        (p04RoundedRoot model (stage.twiddleExponent i)) (x i)
    else x i

noncomputable def p04RoundedMixedRadixStageApply {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p04RoundedMixedRadixTwiddleApply model stage
    (p04RoundedMixedRadixBlockApply model stage x)

noncomputable def p04ApplyRoundedMixedRadixStages {r n : ℕ} [NeZero n]
    (model : P04WilkinsonModel)
    (stages : Fin r → P04MixedRadixStage n) (x : ZMod n → ℂ) :
    ZMod n → ℂ :=
  (List.ofFn stages).foldl
    (fun state stage ↦ p04RoundedMixedRadixStageApply model stage state) x

noncomputable def p04RoundedFftApply {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  p04Permute plan.finalPermutation
    (p04ApplyRoundedMixedRadixStages model plan.stage x)

structure P04MixedRadixFftRun {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel) where
  input : ZMod n → ℂ
  stageState : ℕ → ZMod n → ℂ
  input_exact : ∀ i : ZMod n, model.flInput (input i) = input i
  initial_state : stageState 0 = input
  stage_step : ∀ i : Fin plan.stageCount,
    stageState (i.val + 1) =
      p04RoundedMixedRadixStageApply model (plan.stage i) (stageState i.val)

abbrev P04PositiveEpsilon := {ε : ℝ // 0 < ε}

structure P04FftAxis where
  order : ℕ
  order_pos : 0 < order
  plan : @P04MixedRadixFftPlan order ⟨Nat.ne_of_gt order_pos⟩

instance p04FftAxisOrderNeZero (axis : P04FftAxis) : NeZero axis.order :=
  ⟨Nat.ne_of_gt axis.order_pos⟩

noncomputable def p04AxisK (axis : P04FftAxis) (γ : ℝ) : ℝ :=
  @p04K axis.order ⟨Nat.ne_of_gt axis.order_pos⟩ axis.plan γ

abbrev P04MultiIndex {m : ℕ} (axis : Fin m → P04FftAxis) :=
  (i : Fin m) → ZMod (axis i).order

noncomputable instance p04MultiIndexFintype {m : ℕ}
    (axis : Fin m → P04FftAxis) : Fintype (P04MultiIndex axis) := by
  letI (i : Fin m) : NeZero (axis i).order :=
    ⟨Nat.ne_of_gt (axis i).order_pos⟩
  infer_instance

abbrev P04MultiArray {m : ℕ} (axis : Fin m → P04FftAxis) :=
  P04MultiIndex axis → ℂ

def p04MultiCardinality {m : ℕ} (axis : Fin m → P04FftAxis) : ℕ :=
  ∏ i : Fin m, (axis i).order

noncomputable def p04MultiNorm2 {m : ℕ} {axis : Fin m → P04FftAxis}
    (x : P04MultiArray axis) : ℝ := by
  letI (i : Fin m) : NeZero (axis i).order :=
    ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))‖

noncomputable def p04MultiRms {m : ℕ} {axis : Fin m → P04FftAxis}
    (x : P04MultiArray axis) : ℝ :=
  p04MultiNorm2 x / Real.sqrt (p04MultiCardinality axis : ℝ)

def p04MultiVecAdd {m : ℕ} {axis : Fin m → P04FftAxis}
    (x y : P04MultiArray axis) : P04MultiArray axis :=
  fun index ↦ x index + y index

def p04MultiVecSub {m : ℕ} {axis : Fin m → P04FftAxis}
    (x y : P04MultiArray axis) : P04MultiArray axis :=
  fun index ↦ x index - y index

noncomputable def p04MultiVectorSum {r m : ℕ} {axis : Fin m → P04FftAxis}
    (term : Fin r → P04MultiArray axis) : P04MultiArray axis :=
  fun index ↦ ∑ i : Fin r, term i index

noncomputable def p04CoordinateTransform {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) : P04MultiArray axis := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact fun index ↦ ∑ j : ZMod (axis i).order,
    ZMod.stdAddChar (j * index i) * x (Function.update index i j)

noncomputable def p04RoundedCoordinateTransform {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis) :
    P04MultiArray axis := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  exact fun index ↦
    p04RoundedFftApply (axis i).plan model
      (fun j ↦ x (Function.update index i j)) (index i)

noncomputable def p04CoordinateTransformNat {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : ℕ)
    (x : P04MultiArray axis) : P04MultiArray axis :=
  if hi : i < m then p04CoordinateTransform axis ⟨i, hi⟩ x else x

noncomputable def p04ApplyCoordinatePrefix {m : ℕ}
    (axis : Fin m → P04FftAxis) : ℕ → P04MultiArray axis → P04MultiArray axis
  | 0, x => x
  | i + 1, x =>
      p04ApplyCoordinatePrefix axis i (p04CoordinateTransformNat axis i x)

def p04PrefixOrderProduct {m : ℕ} (axis : Fin m → P04FftAxis)
    (k : ℕ) (hk : k ≤ m) : ℕ :=
  ∏ i : Fin k, (axis (Fin.castLE hk i)).order

structure P04MultidimensionalFftPlan (m : ℕ) [NeZero m] where
  axis : Fin m → P04FftAxis
  prefix_rms_scaling : ∀ (k : ℕ) (hk : k ≤ m) (x : P04MultiArray axis),
    p04MultiRms (p04ApplyCoordinatePrefix axis k x) =
      Real.sqrt (p04PrefixOrderProduct axis k hk : ℝ) * p04MultiRms x

structure P04MultidimensionalFftRun {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (model : P04WilkinsonModel) where
  input : P04MultiArray plan.axis
  computedState : Fin (m + 1) → P04MultiArray plan.axis
  input_exact : ∀ index, model.flInput (input index) = input index
  computed_input : computedState (Fin.last m) = input
  stage_step : ∀ i : Fin m,
    computedState i.castSucc =
      p04RoundedCoordinateTransform plan.axis i model
        (computedState i.succ)

noncomputable def p04AxisLocalError {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) (i : Fin m) :
    P04MultiArray plan.axis :=
  p04MultiVecSub (run.computedState i.castSucc)
    (p04CoordinateTransform plan.axis i (run.computedState i.succ))

noncomputable def p04MultiExactOutput {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) : P04MultiArray plan.axis :=
  p04ApplyCoordinatePrefix plan.axis m run.input

def p04MultiComputedOutput {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) : P04MultiArray plan.axis :=
  run.computedState 0

noncomputable def p04MultiFftRoundoffError {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) : P04MultiArray plan.axis :=
  p04MultiVecSub (p04MultiComputedOutput run) (p04MultiExactOutput run)

noncomputable def p04PropagatedAxisError {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) (i : Fin m) :
    P04MultiArray plan.axis :=
  p04ApplyCoordinatePrefix plan.axis i.val (p04AxisLocalError run i)

noncomputable def p04PropagatedStageInputRms {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) (i : Fin m) : ℝ :=
  p04MultiRms
    (p04ApplyCoordinatePrefix plan.axis (i.val + 1)
      (run.computedState i.succ))

structure P04AsymptoticMultidimensionalFftFamily {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ) where
  gamma_nonneg : 0 ≤ γ
  input : P04MultiArray plan.axis
  model : P04PositiveEpsilon → P04WilkinsonModel
  model_epsilon : ∀ ε, (model ε).epsilon = ε.1
  model_gamma : ∀ ε, (model ε).gamma = γ
  run : ∀ ε, P04MultidimensionalFftRun plan (model ε)
  run_input : ∀ ε, (run ε).input = input

noncomputable def p04FamilyMultiExactOutput {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ) :
    P04MultiArray plan.axis :=
  p04ApplyCoordinatePrefix plan.axis m family.input

noncomputable def p04FamilyMultiFftRoundoffError {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) : P04MultiArray plan.axis :=
  p04MultiVecSub (p04MultiComputedOutput (family.run ε))
    (p04FamilyMultiExactOutput family)

end VSCLReuse

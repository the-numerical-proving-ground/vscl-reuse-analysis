import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace VSCLReuse

open scoped BigOperators

noncomputable def p09Gamma (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ n - 1

noncomputable def p09UnitRoundoff (p : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (p - 1)

noncomputable def p09ExactSum {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i

noncomputable def p09SummationCondition {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  (∑ i, |a i|) / |p09ExactSum a|

structure P09FiniteProbability (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  prob_nonneg : ∀ ω, 0 ≤ prob ω
  prob_sum : ∑ ω, prob ω = 1

noncomputable def p09EventProb {Ω : Type*} [Fintype Ω]
    (P : P09FiniteProbability Ω) (E : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ E then P.prob ω else 0

noncomputable def p09Expectation {Ω : Type*} [Fintype Ω]
    (P : P09FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, P.prob ω * X ω

def p09HistoryMeasurable {m : ℕ} {Ω : Type*}
    (delta : Fin m → Ω → ℝ) (k : Fin m) (X : Ω → ℝ) : Prop :=
  ∀ ω₁ ω₂,
    (∀ j : Fin m, j.val < k.val → delta j ω₁ = delta j ω₂) →
      X ω₁ = X ω₂

structure P09Lemma310Run
    (n : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P09FiniteProbability Ω
  operation_count_pos : 0 < n
  unitRoundoff : ℝ
  biasRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  biasRoundoff_nonneg : 0 ≤ biasRoundoff
  delta : Fin n → Ω → ℝ
  beta : Fin n → Ω → ℝ
  alpha_bound : ∀ k ω, |delta k ω - beta k ω| ≤ unitRoundoff
  beta_bound : ∀ k ω, |beta k ω| ≤ biasRoundoff
  conditional_mean_from_alpha_history : ∀ k X,
    p09HistoryMeasurable (fun j ω => delta j ω - beta j ω) k X →
      p09Expectation probability (fun ω => X ω * delta k ω) =
        p09Expectation probability (fun ω => X ω * beta k ω)

noncomputable def p09ProductAlpha
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09Lemma310Run n Ω) (k : Fin n) (ω : Ω) : ℝ :=
  run.delta k ω - run.beta k ω

def p09SuffixIndexSet {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun k => i.val ≤ k.val

noncomputable def p09Lemma310BiasRemainder
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09Lemma310Run n Ω) (i : Fin n) (ω : Ω) : ℝ :=
  let I := p09SuffixIndexSet i
  ∑ K ∈ I.powerset.erase I,
    (∏ k ∈ K, (1 + p09ProductAlpha run k ω)) *
      ∏ k ∈ I \ K, run.beta k ω

noncomputable def p09RecursiveSum {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) : ℝ :=
  Fin.foldl m
    (fun acc k => (acc + a k.succ) * (1 + delta k))
    (a 0)

noncomputable def p09RecursiveSumBefore {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  Fin.foldl k.val
    (fun acc j =>
      let q : Fin m := ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩
      (acc + a q.succ) * (1 + delta q))
    (a 0)

noncomputable def p09RecursivePreRound {m : ℕ}
    (a : Fin (m + 1) → ℝ) (delta : Fin m → ℝ) (k : Fin m) : ℝ :=
  p09RecursiveSumBefore a delta k + a k.succ

structure P09LimitedPrecisionRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω] where
  probability : P09FiniteProbability Ω
  p : ℕ
  r : ℕ
  p_pos : 0 < p
  r_pos : 0 < r
  a : Fin (m + 1) → ℝ
  delta : Fin m → Ω → ℝ
  beta : Fin m → Ω → ℝ
  truncate : ℝ → ℝ
  delta_bound : ∀ k ω, |delta k ω| ≤ p09UnitRoundoff p
  rounding_factor_nonneg : ∀ k ω, 0 ≤ 1 + delta k ω
  beta_bound : ∀ k ω, |beta k ω| ≤ p09UnitRoundoff (p + r)
  truncation_equation : ∀ k ω,
    truncate (p09RecursivePreRound a (fun j => delta j ω) k) =
      p09RecursivePreRound a (fun j => delta j ω) k * (1 + beta k ω)
  delta_zero : ∀ k ω,
    p09RecursivePreRound a (fun j => delta j ω) k = 0 → delta k ω = 0
  beta_zero : ∀ k ω,
    p09RecursivePreRound a (fun j => delta j ω) k = 0 → beta k ω = 0
  beta_history : ∀ k, p09HistoryMeasurable delta k (beta k)
  conditional_mean : ∀ k X,
    p09HistoryMeasurable delta k X →
      p09Expectation probability (fun ω => X ω * delta k ω) =
        p09Expectation probability (fun ω => X ω * beta k ω)

noncomputable def p09SuffixErrorProduct :
    (m : ℕ) → (Fin m → ℝ) → Fin m → ℝ
  | 0, _ => fun i => i.elim0
  | m + 1, delta =>
      Fin.lastCases (1 + delta (Fin.last m))
        (fun i =>
          p09SuffixErrorProduct m (fun j => delta j.castSucc) i *
            (1 + delta (Fin.last m)))

noncomputable def p09RecursiveCoefficient {m : ℕ}
    (error : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases (∏ k : Fin m, (1 + error k))
    (fun i => p09SuffixErrorProduct m error i)

noncomputable def p09Alpha
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09LimitedPrecisionRecursiveSumRun m Ω)
    (k : Fin m) (ω : Ω) : ℝ :=
  run.delta k ω - run.beta k ω

noncomputable def p09CoefficientRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09LimitedPrecisionRecursiveSumRun m Ω)
    (i : Fin (m + 1)) (ω : Ω) : ℝ :=
  p09RecursiveCoefficient (fun k => run.delta k ω) i -
    p09RecursiveCoefficient (fun k => p09Alpha run k ω) i

noncomputable def p09CenteredSummationError
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1),
    run.a i *
      (p09RecursiveCoefficient (fun k => p09Alpha run k ω) i - 1)

noncomputable def p09LimitedPrecisionRemainder
    {m : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P09LimitedPrecisionRecursiveSumRun m Ω) (ω : Ω) : ℝ :=
  ∑ i : Fin (m + 1), run.a i * p09CoefficientRemainder run i ω

structure P09VarianceRecursiveSumRun
    (m : ℕ) (Ω : Type*) [Fintype Ω]
    extends P09LimitedPrecisionRecursiveSumRun m Ω where
  alpha_bound : ∀ k ω,
    |p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω| ≤
      p09UnitRoundoff p
  alpha_mean_independent : ∀ k X,
    p09HistoryMeasurable
        (fun j ω => p09Alpha toP09LimitedPrecisionRecursiveSumRun j ω) k X →
      p09Expectation probability
        (fun ω => X ω *
          p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω) = 0
  alpha_product_covariance_bound : ∀ i j,
    0 ≤ p09Expectation probability (fun ω =>
        (p09RecursiveCoefficient
              (fun k => p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω) i - 1) *
          (p09RecursiveCoefficient
              (fun k => p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω) j - 1)) ∧
      p09Expectation probability (fun ω =>
          (p09RecursiveCoefficient
                (fun k => p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω) i - 1) *
            (p09RecursiveCoefficient
                (fun k => p09Alpha toP09LimitedPrecisionRecursiveSumRun k ω) j - 1)) ≤
        p09Gamma m ((p09UnitRoundoff p) ^ 2)
  coefficient_remainder_bound : ∀ i ω,
    |p09CoefficientRemainder toP09LimitedPrecisionRecursiveSumRun i ω| ≤
      p09Gamma m
          (p09UnitRoundoff p + p09UnitRoundoff (p + r)) -
        p09Gamma m (p09UnitRoundoff p)

end VSCLReuse

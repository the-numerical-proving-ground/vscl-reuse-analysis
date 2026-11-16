import VSCLReuse.P42.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p42ToFPModel (fp : P42FPModel) : NumStability.FPModel :=
  { NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg with
    fl_add := fp.fl_add
    fl_add_zero := fp.fl_add_zero
    model_add := fp.model_add }

private lemma p42RecursiveSum_eq_library (fp : P42FPModel)
    (n : ℕ) (v : Fin n → ℝ) :
    p42RecursiveSum fp n v =
      NumStability.fl_recursiveSum (p42ToFPModel fp) n v := by
  rfl

private lemma p42PairwiseSum_eq_library (fp : P42FPModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      p42PairwiseSum fp r v =
        NumStability.fl_pairwiseSum (p42ToFPModel fp) r v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      simp only [p42PairwiseSum, NumStability.fl_pairwiseSum]
      rw [ih, ih]
      rfl

/-- Theorem 3.1, recursive-block and pairwise-outer specialization. -/
theorem p42_c3_fabsum_backward_error
    (fp : P42FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ)
    (hb : 0 < b)
    (hbvalid : P42GammaValid fp.u (b - 1))
    (hrvalid : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → Fin b → ℝ,
      (∀ i j, |μ i j| ≤
        p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r) ∧
      p42FABsum fp b r x =
        ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
  -- PROOF_START P42-C3-H001
  let nfp := p42ToFPModel fp
  have hlocalValid : NumStability.gammaValid nfp (b - 1) := by
    exact hbvalid
  have houterValid : NumStability.gammaValid nfp r := by
    exact hrvalid
  have hlocal : ∀ i : Fin (2 ^ r),
      ∃ θ : Fin b → ℝ,
        (∀ j, |θ j| ≤ p42Gamma fp.u (b - 1)) ∧
        p42RecursiveSum fp b (x i) =
          ∑ j : Fin b, x i j * (1 + θ j) := by
    intro i
    obtain ⟨θ, hθ, hsum⟩ :=
      NumStability.recursiveSum_backward_error nfp b (x i) hlocalValid
    refine ⟨θ, ?_, ?_⟩
    · simpa only [NumStability.gamma, p42Gamma, nfp, p42ToFPModel] using hθ
    · simpa only [p42RecursiveSum_eq_library] using hsum
  choose θ hθ hsum using hlocal
  obtain ⟨η, hη', houter⟩ :=
    NumStability.pairwiseSum_backward_error nfp r
      (fun i => p42RecursiveSum fp b (x i)) houterValid
  have hη : ∀ i, |η i| ≤ p42Gamma fp.u r := by
    simpa only [NumStability.gamma, p42Gamma, nfp, p42ToFPModel] using hη'
  have hγb : 0 ≤ p42Gamma fp.u (b - 1) := by
    simpa only [NumStability.gamma, p42Gamma, nfp, p42ToFPModel] using
      NumStability.gamma_nonneg nfp hlocalValid
  let μ : Fin (2 ^ r) → Fin b → ℝ :=
    fun i j => θ i j + η i + θ i j * η i
  refine ⟨μ, ?_, ?_⟩
  · intro i j
    have hprod : |θ i j| * |η i| ≤
        p42Gamma fp.u (b - 1) * p42Gamma fp.u r :=
      mul_le_mul (hθ i j) (hη i) (abs_nonneg _) hγb
    calc
      |μ i j| ≤ |θ i j| + |η i| + |θ i j * η i| := by
        dsimp [μ]
        exact (abs_add_le (θ i j + η i) (θ i j * η i)).trans
          (add_le_add (abs_add_le (θ i j) (η i)) le_rfl)
      _ = |θ i j| + |η i| + |θ i j| * |η i| := by rw [abs_mul]
      _ ≤ p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
            p42Gamma fp.u (b - 1) * p42Gamma fp.u r :=
          add_le_add (add_le_add (hθ i j) (hη i)) hprod
  · calc
      p42FABsum fp b r x =
          ∑ i : Fin (2 ^ r), p42RecursiveSum fp b (x i) * (1 + η i) := by
            simpa only [p42FABsum, p42PairwiseSum_eq_library] using houter
      _ = ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hsum i, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            dsimp [μ]
            ring

end VSCLReuse

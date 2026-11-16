import VSCLReuse.P42.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p42ToFPModel (fp : P42FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, by ring⟩

private theorem p42Pairwise_eq (fp : P42FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    p42PairwiseSum fp r v =
      NumStability.fl_pairwiseSum (p42ToFPModel fp) r v := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [p42PairwiseSum, NumStability.fl_pairwiseSum,
      p42ToFPModel] using congrArg₂ fp.fl_add
        (ih (fun i => v ⟨i.val, by have := i.isLt; simp [pow_succ]; omega⟩))
        (ih (fun i => v ⟨i.val + 2 ^ r,
          by have := i.isLt; simp [pow_succ]; omega⟩))

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
  classical
  have _ : b ≠ 0 := Nat.ne_of_gt hb
  let F := p42ToFPModel fp
  have hbF : NumStability.gammaValid F (b - 1) := by
    simpa [F, NumStability.gammaValid, P42GammaValid, p42ToFPModel] using hbvalid
  have hrF : NumStability.gammaValid F r := by
    simpa [F, NumStability.gammaValid, P42GammaValid, p42ToFPModel] using hrvalid
  obtain ⟨η, hηF, houter⟩ :=
    NumStability.pairwiseSum_backward_error F r
      (fun i => p42RecursiveSum fp b (x i)) hrF
  have hη : ∀ i, |η i| ≤ p42Gamma fp.u r := by
    intro i
    simpa [F, NumStability.gamma, p42Gamma, p42ToFPModel] using hηF i
  have hblocks : ∀ i : Fin (2 ^ r),
      ∃ θ : Fin b → ℝ,
        (∀ j, |θ j| ≤ p42Gamma fp.u (b - 1)) ∧
        p42RecursiveSum fp b (x i) =
          ∑ j : Fin b, x i j * (1 + θ j) := by
    intro i
    obtain ⟨θ, hθF, hsum⟩ :=
      NumStability.recursiveSum_backward_error F b (x i) hbF
    refine ⟨θ, ?_, ?_⟩
    · intro j
      simpa [F, NumStability.gamma, p42Gamma, p42ToFPModel] using hθF j
    · simpa [F, NumStability.fl_recursiveSum, p42RecursiveSum,
        p42ToFPModel] using hsum
  choose θ hθ hblock using hblocks
  let μ : Fin (2 ^ r) → Fin b → ℝ :=
    fun i j => θ i j + η i + θ i j * η i
  have hgamma_nonneg : 0 ≤ p42Gamma fp.u (b - 1) := by
    simpa [F, NumStability.gamma, p42Gamma, p42ToFPModel] using
      (NumStability.gamma_nonneg F hbF)
  refine ⟨μ, ?_, ?_⟩
  · intro i j
    have hprod : |θ i j| * |η i| ≤
        p42Gamma fp.u (b - 1) * p42Gamma fp.u r := by
      calc
        |θ i j| * |η i| ≤ p42Gamma fp.u (b - 1) * |η i| :=
          mul_le_mul_of_nonneg_right (hθ i j) (abs_nonneg _)
        _ ≤ p42Gamma fp.u (b - 1) * p42Gamma fp.u r :=
          mul_le_mul_of_nonneg_left (hη i) hgamma_nonneg
    calc
      |μ i j| = |θ i j + η i + θ i j * η i| := rfl
      _ ≤ |θ i j| + |η i| + |θ i j * η i| := by
        calc
          |θ i j + η i + θ i j * η i| ≤
              |θ i j + η i| + |θ i j * η i| := abs_add_le _ _
          _ ≤ |θ i j| + |η i| + |θ i j * η i| := by
            linarith [abs_add_le (θ i j) (η i)]
      _ = |θ i j| + |η i| + |θ i j| * |η i| := by rw [abs_mul]
      _ ≤ p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r := by
        linarith [hθ i j, hη i, hprod]
  · calc
      p42FABsum fp b r x =
          ∑ i : Fin (2 ^ r), p42RecursiveSum fp b (x i) * (1 + η i) := by
        unfold p42FABsum
        rw [p42Pairwise_eq]
        exact houter
      _ = ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hblock i, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [μ]
        ring

end VSCLReuse

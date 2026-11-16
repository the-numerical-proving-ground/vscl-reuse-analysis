import VSCLReuse.P42.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p42AsFP (fp : P42FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p42_pairwise_eq (fp : P42FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    p42PairwiseSum fp r v =
      NumStability.fl_pairwiseSum (p42AsFP fp) r v := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [p42PairwiseSum, NumStability.fl_pairwiseSum]
    change fp.fl_add (p42PairwiseSum fp r _) (p42PairwiseSum fp r _) =
      fp.fl_add (NumStability.fl_pairwiseSum (p42AsFP fp) r _)
        (NumStability.fl_pairwiseSum (p42AsFP fp) r _)
    rw [ih, ih]

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
  let q := p42AsFP fp
  have hrecvalid : NumStability.gammaValid q (b - 1) := hbvalid
  have hpairvalid : NumStability.gammaValid q r := hrvalid
  have hlocal (i : Fin (2 ^ r)) :
      ∃ θ : Fin b → ℝ,
        (∀ j, |θ j| ≤ p42Gamma fp.u (b - 1)) ∧
        p42RecursiveSum fp b (x i) =
          ∑ j : Fin b, x i j * (1 + θ j) := by
    simpa only [p42RecursiveSum, NumStability.fl_recursiveSum,
      p42Gamma, NumStability.gamma, q, p42AsFP] using
      (NumStability.recursiveSum_backward_error q b (x i) hrecvalid)
  choose θ hθ hinner using hlocal
  obtain ⟨η, hη, houter⟩ :=
    NumStability.pairwiseSum_backward_error q r
      (fun i => p42RecursiveSum fp b (x i)) hpairvalid
  let μ : Fin (2 ^ r) → Fin b → ℝ :=
    fun i j => θ i j + η i + θ i j * η i
  refine ⟨μ, ?_, ?_⟩
  · intro i j
    have hga : 0 ≤ p42Gamma fp.u (b - 1) :=
      NumStability.gamma_nonneg q hrecvalid
    have hprod : |θ i j| * |η i| ≤
        p42Gamma fp.u (b - 1) * p42Gamma fp.u r := by
      calc
        |θ i j| * |η i| ≤ p42Gamma fp.u (b - 1) * |η i| :=
          mul_le_mul_of_nonneg_right (hθ i j) (abs_nonneg _)
        _ ≤ p42Gamma fp.u (b - 1) * p42Gamma fp.u r :=
          mul_le_mul_of_nonneg_left (hη i) hga
    change |θ i j + η i + θ i j * η i| ≤ _
    calc
      |θ i j + η i + θ i j * η i| ≤
          |θ i j| + |η i| + |θ i j * η i| := by
        calc
          |θ i j + η i + θ i j * η i| ≤
              |θ i j + η i| + |θ i j * η i| := abs_add_le _ _
          _ ≤ |θ i j| + |η i| + |θ i j * η i| := by
            gcongr
            exact abs_add_le _ _
      _ = |θ i j| + |η i| + |θ i j| * |η i| := by rw [abs_mul]
      _ ≤ p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r := by
            exact add_le_add (add_le_add (hθ i j) (hη i)) hprod
  · change p42PairwiseSum fp r (fun i => p42RecursiveSum fp b (x i)) = _
    rw [p42_pairwise_eq, houter]
    apply Finset.sum_congr rfl
    intro i _
    rw [hinner i, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [μ]
    ring

end VSCLReuse

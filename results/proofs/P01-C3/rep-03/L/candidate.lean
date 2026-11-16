import VSCLReuse.P01.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def StandardAddModel.toFPModel (fp : StandardAddModel) :
    NumStability.FPModel where
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
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem recursiveSum_eq_library (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum fp.toFPModel n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum,
          Fin.foldl_succ_last, StandardAddModel.toFPModel,
          fp.fl_add_zero]
      · rw [recursiveSum, dif_neg hn]
        change fp.fl_add
          (recursiveSum fp.fl_add n (fun i => v i.castSucc))
          (v (Fin.last n)) =
          Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) 0
        rw [Fin.foldl_succ_last]
        rw [ih]
        rfl

private theorem pairwiseSum_eq_library (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v =
        NumStability.fl_pairwiseSum fp.toFPModel r v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      change fp.fl_add
        (pairwiseSum fp.fl_add r (fun i => v (leftIndex r i)))
        (pairwiseSum fp.fl_add r (fun i => v (rightIndex r i))) =
        fp.fl_add
          (NumStability.fl_pairwiseSum fp.toFPModel r
            (fun i => v ⟨i.val, _⟩))
          (NumStability.fl_pairwiseSum fp.toFPModel r
            (fun i => v ⟨i.val + 2 ^ r, _⟩))
      congr 1
      · rw [ih]
        congr 1
      · rw [ih]
        congr 1

private theorem recursivePreRound_eq_library (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    recursivePreRound fp.fl_add v i =
      NumStability.fl_partialSums fp.toFPModel v i := by
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq_library]

theorem p01_c3_recursive_running_and_pairwise_bounds
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u (2 ^ r - 1)) :
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        fp.u * ∑ i : Fin (2 ^ r), |recursivePreRound fp.fl_add v i| ∧
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  -- PROOF_START P01-C3-H001
  have hv : NumStability.gammaValid fp.toFPModel (2 ^ r - 1) := by
    simpa [NumStability.gammaValid, GammaValid, StandardAddModel.toFPModel]
      using hvalid
  have hrle : r ≤ 2 ^ r - 1 := by
    have h : r < 2 ^ r := Nat.lt_two_pow_self
    omega
  have hrv : NumStability.gammaValid fp.toFPModel r :=
    NumStability.gammaValid_mono fp.toFPModel hrle hv
  constructor
  · simpa only [recursiveSum_eq_library, recursivePreRound_eq_library,
      StandardAddModel.toFPModel] using
      (NumStability.recursiveSum_running_error_bound fp.toFPModel (2 ^ r) v)
  constructor
  · simpa only [recursiveSum_eq_library, gamma, NumStability.gamma,
      StandardAddModel.toFPModel] using
      (NumStability.recursiveSum_forward_error_bound fp.toFPModel (2 ^ r) v hv)
  · simpa only [pairwiseSum_eq_library, gamma, NumStability.gamma,
      StandardAddModel.toFPModel] using
      (NumStability.pairwiseSum_forward_error_bound fp.toFPModel r v hrv)

end VSCLReuse

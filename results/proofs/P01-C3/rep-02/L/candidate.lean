import VSCLReuse.P01.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def standardToFP (fp : StandardAddModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := (· * ·)
  fl_div := (· / ·)
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

private lemma recursiveSum_eq_library (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      recursiveSum fp.fl_add n v =
        NumStability.fl_recursiveSum (standardToFP fp) n v := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
      intro v
      have hfold : NumStability.fl_recursiveSum (standardToFP fp) (n + 1) v =
          fp.fl_add
            (NumStability.fl_recursiveSum (standardToFP fp) n (fun i => v i.castSucc))
            (v (Fin.last n)) := by
        exact Fin.foldl_succ_last _ _
      rw [hfold]
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, NumStability.fl_recursiveSum, standardToFP, fp.fl_add_zero]
      · simp only [recursiveSum, dif_neg hn]
        rw [ih]

private lemma pairwiseSum_eq_library (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      pairwiseSum fp.fl_add r v =
        NumStability.fl_pairwiseSum (standardToFP fp) r v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      change fp.fl_add
        (pairwiseSum fp.fl_add r (fun i => v (leftIndex r i)))
        (pairwiseSum fp.fl_add r (fun i => v (rightIndex r i))) = _
      rw [ih, ih]
      rfl

private lemma recursivePreRound_eq_library (fp : StandardAddModel)
    {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    recursivePreRound fp.fl_add v i =
      NumStability.fl_partialSums (standardToFP fp) v i := by
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq_library]

private lemma gamma_eq_library (fp : StandardAddModel) (n : ℕ) :
    gamma fp.u n = NumStability.gamma (standardToFP fp) n := rfl

private lemma gammaValid_eq_library (fp : StandardAddModel) (n : ℕ) :
    GammaValid fp.u n = NumStability.gammaValid (standardToFP fp) n := rfl

private lemma pow_le_pred (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
      rw [pow_succ]
      omega

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
  let m := standardToFP fp
  have hm : NumStability.gammaValid m (2 ^ r - 1) := by
    simpa only [m, ← gammaValid_eq_library] using hvalid
  have hr : NumStability.gammaValid m r :=
    NumStability.gammaValid_mono m (pow_le_pred r) hm
  constructor
  · have hrun := NumStability.recursiveSum_running_error_bound m (2 ^ r) v
    have hpartial :
        (∑ i : Fin (2 ^ r), |recursivePreRound fp.fl_add v i|) =
          ∑ i : Fin (2 ^ r), |NumStability.fl_partialSums m v i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [recursivePreRound_eq_library]
    rw [recursiveSum_eq_library fp (2 ^ r) v, hpartial]
    exact hrun
  constructor
  · rw [recursiveSum_eq_library fp (2 ^ r) v, gamma_eq_library]
    exact NumStability.recursiveSum_forward_error_bound m (2 ^ r) v hm
  · rw [pairwiseSum_eq_library fp r v, gamma_eq_library]
    exact NumStability.pairwiseSum_forward_error_bound m r v hr

end VSCLReuse

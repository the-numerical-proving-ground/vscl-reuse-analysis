import VSCLReuse.P01.Definitions
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def liftModel (fp : StandardAddModel) : NumStability.FPModel :=
  { (NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg) with
    fl_add := fp.fl_add
    fl_add_zero := fp.fl_add_zero
    model_add := fp.model_add }

private lemma liftModel_u (fp : StandardAddModel) : (liftModel fp).u = fp.u := rfl
private lemma liftModel_fl_add (fp : StandardAddModel) :
    (liftModel fp).fl_add = fp.fl_add := rfl

private lemma recursiveSum_eq (fp : StandardAddModel) (n : ℕ) (v : Fin n → ℝ) :
    recursiveSum fp.fl_add n v = NumStability.fl_recursiveSum (liftModel fp) n v := by
  induction n with
  | zero => simp [recursiveSum, NumStability.fl_recursiveSum]
  | succ n ih =>
    cases n with
    | zero =>
      simp [recursiveSum, NumStability.fl_recursiveSum, Fin.foldl_succ_last,
        liftModel_fl_add, fp.fl_add_zero]
    | succ n =>
      rw [NumStability.fl_recursiveSum, Fin.foldl_succ_last]
      change fp.fl_add
        (recursiveSum fp.fl_add (n + 1) (fun i => v i.castSucc))
        (v (Fin.last (n + 1))) = _
      rw [ih]
      rfl

private lemma pairwiseSum_eq (fp : StandardAddModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    pairwiseSum fp.fl_add r v = NumStability.fl_pairwiseSum (liftModel fp) r v := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [pairwiseSum, NumStability.fl_pairwiseSum, liftModel_fl_add]
    rw [ih, ih]
    rfl

private lemma preRound_eq (fp : StandardAddModel) {n : ℕ} (v : Fin n → ℝ)
    (i : Fin n) :
    recursivePreRound fp.fl_add v i =
      NumStability.fl_partialSums (liftModel fp) v i := by
  unfold recursivePreRound NumStability.fl_partialSums
  rw [recursiveSum_eq]

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
  have hn : NumStability.gammaValid (liftModel fp) (2 ^ r - 1) := hvalid
  have hpow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      omega
  have hr : NumStability.gammaValid (liftModel fp) r :=
    NumStability.gammaValid_mono (liftModel fp) (by have := hpow r; omega) hn
  constructor
  · simpa only [← recursiveSum_eq, liftModel_u, ← preRound_eq] using
      NumStability.recursiveSum_running_error_bound (liftModel fp) (2 ^ r) v
  constructor
  · simpa only [← recursiveSum_eq, liftModel_u, gamma,
      NumStability.gamma] using
      NumStability.recursiveSum_forward_error_bound (liftModel fp) (2 ^ r) v hn
  · simpa only [← pairwiseSum_eq, liftModel_u, gamma,
      NumStability.gamma] using
      NumStability.pairwiseSum_forward_error_bound (liftModel fp) r v hr

end VSCLReuse

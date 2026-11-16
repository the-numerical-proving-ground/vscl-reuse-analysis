import VSCLReuse.P53.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.TreeDotProduct
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p53AsFPModel (fp : P53FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

private lemma p53_as_gamma (fp : P53FPModel) (k : ℕ) :
    NumStability.gamma (p53AsFPModel fp) k = p53Gamma fp.u k := by
  rfl

private lemma p53_as_valid (fp : P53FPModel) (k : ℕ) :
    NumStability.gammaValid (p53AsFPModel fp) k ↔ P53GammaValid fp.u k := by
  rfl

private lemma p53_as_dot (fp : P53FPModel) (n : ℕ) (a x : Fin n → ℝ) :
    NumStability.fl_dotProduct (p53AsFPModel fp) n a x = p53Dot fp n a x := by
  rfl

private lemma p53_as_pairwise (fp : P53FPModel) (r : ℕ) :
    ∀ v : Fin (2 ^ r) → ℝ,
      p53PairwiseSum fp r v =
        (NumStability.SumTree.balancedTree r).eval (p53AsFPModel fp) v := by
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      simp only [p53PairwiseSum, NumStability.SumTree.balancedTree]
      rw [NumStability.SumTree.eval_cast]
      simp only [NumStability.SumTree.eval]
      congr 1
      · rw [ih]
        congr 1
      · rw [ih]
        congr 1
        funext i
        apply congrArg v
        apply Fin.ext
        simp only [Fin.natAdd]
        omega

private lemma p53_mul_zero (fp : P53FPModel) : fp.fl_mul 0 0 = 0 := by
  obtain ⟨δ, _, hδ⟩ := fp.model_mul 0 0
  simpa using hδ

private lemma p53_as_cascade (fp : P53FPModel) (n : ℕ) (a x : Fin n → ℝ) :
    p53CascadeDot fp n a x =
      NumStability.fl_clog2PairwiseDotProduct (p53AsFPModel fp) n a x := by
  unfold p53CascadeDot p53CascadeSum
  rw [p53_as_pairwise]
  unfold NumStability.fl_clog2PairwiseDotProduct NumStability.fl_sumTreeDotProduct
  congr 1
  funext i
  by_cases hi : i.val < n
  · simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi,
      p53AsFPModel]
  · simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi,
      p53AsFPModel, p53_mul_zero]

theorem p53_lemma1_whole (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ)
    (hn : 0 < n)
    (hrec : P53GammaValid fp.u n) :
    (|p53Dot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u n * ∑ i : Fin n, |a i| * |x i|) ∧
    (|p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 n + 1) *
        ∑ i : Fin n, |a i| * |x i|) := by
  -- PROOF_START P53-C3-Lemma1-H001
  constructor
  · have h := NumStability.dotProduct_error_bound
        (p53AsFPModel fp) n a x ((p53_as_valid fp n).2 hrec)
    simpa only [p53_as_dot, p53_as_gamma] using h
  · have hclog : Nat.clog 2 n + 1 ≤ n := by
      have h := NumStability.clog2_le_pred n hn
      omega
    have hvalid : NumStability.gammaValid (p53AsFPModel fp)
        (Nat.clog 2 n + 1) :=
      NumStability.gammaValid_mono (p53AsFPModel fp) hclog
        ((p53_as_valid fp n).2 hrec)
    have h := NumStability.clog2PairwiseDotProduct_error_bound
      (p53AsFPModel fp) n a x hvalid
    simpa only [p53_as_gamma, ← p53_as_cascade] using h

end VSCLReuse

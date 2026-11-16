import VSCLReuse.P53.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Pairwise.Core
import NumStability.Algorithms.TreeDotProduct

namespace VSCLReuse

open scoped BigOperators

noncomputable def p53AsFPModel (fp : P53FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private lemma p53PairwiseSum_eq_balanced (fp : P53FPModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      p53PairwiseSum fp r v =
        (NumStability.SumTree.balancedTree r).eval (p53AsFPModel fp) v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      simp only [NumStability.SumTree.balancedTree,
        NumStability.SumTree.eval_cast, NumStability.SumTree.eval]
      change fp.fl_add _ _ = fp.fl_add _ _
      congr 1
      · simpa only [] using ih (fun i => v ⟨i.val, p53_left_lt r i⟩)
      · convert ih (fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩) using 1
        congr 1
        funext i
        congr 1
        apply Fin.ext
        simp [Fin.natAdd, Nat.add_comm]

private lemma p53CascadeDot_eq_library (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) :
    p53CascadeDot fp n a x =
      NumStability.fl_clog2PairwiseDotProduct (p53AsFPModel fp) n a x := by
  unfold p53CascadeDot p53CascadeSum
  rw [p53PairwiseSum_eq_balanced]
  unfold NumStability.fl_clog2PairwiseDotProduct NumStability.fl_sumTreeDotProduct
  congr 1
  funext i
  by_cases hi : i.val < n
  · simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi,
      p53AsFPModel]
  · obtain ⟨δ, _, hmul⟩ := fp.model_mul 0 0
    have hz : fp.fl_mul 0 0 = 0 := by simpa using hmul
    simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi,
      p53AsFPModel, hz]

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
  let gfp := p53AsFPModel fp
  have hvalid : NumStability.gammaValid gfp n := by
    exact hrec
  have hdepth : Nat.clog 2 n + 1 ≤ n := by
    have hclog := NumStability.clog2_le_pred n hn
    omega
  have hcascade : NumStability.gammaValid gfp (Nat.clog 2 n + 1) :=
    NumStability.gammaValid_mono gfp hdepth hvalid
  constructor
  · have h := NumStability.dotProduct_error_bound gfp n a x hvalid
    simpa [gfp, p53AsFPModel, p53Dot, NumStability.fl_dotProduct,
      p53Gamma, NumStability.gamma] using h
  · have h := NumStability.clog2PairwiseDotProduct_error_bound
      gfp n a x hcascade
    rw [← p53CascadeDot_eq_library] at h
    simpa [gfp, p53AsFPModel, p53Gamma, NumStability.gamma] using h

end VSCLReuse

import VSCLReuse.P38.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p38ToFPModel (fp : P38FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

/-- One fan-in node product error propagated through a left factor. -/
theorem p38_c2_fanin_one_node_propagated_error
    (fp : P38FPModel) (r m n p : ℕ)
    (L : P38Matrix r m) (A : P38Matrix m n) (B : P38Matrix n p)
    (hvalid : P38GammaValid fp.u n) :
    ∀ i : Fin r, ∀ j : Fin p,
      |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| ≤
      p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
  -- PROOF_START P38-C2-H001
  intro i j
  let F := p38ToFPModel fp
  have hvalid' : NumStability.gammaValid F n := by
    simpa [F, p38ToFPModel, NumStability.gammaValid, P38GammaValid] using hvalid
  have hlocal (k : Fin m) :
      |p38RoundedMatMul fp A B k j - p38MatMul A B k j| ≤
        p38Gamma fp.u n * (∑ t : Fin n, |A k t| * |B t j|) := by
    have h := NumStability.dotProduct_error_bound F n (A k) (fun t => B t j) hvalid'
    simpa [F, p38ToFPModel, p38RoundedMatMul, p38RoundedDotProduct,
      p38MatMul, p38Gamma, NumStability.fl_dotProduct, NumStability.gamma] using h
  calc
    |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)|
        ≤ ∑ k : Fin m, |L i k *
            (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin m, |L i k| *
        (p38Gamma fp.u n * (∑ t : Fin n, |A k t| * |B t j|)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hlocal k) (abs_nonneg _)
    _ = p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring

end VSCLReuse

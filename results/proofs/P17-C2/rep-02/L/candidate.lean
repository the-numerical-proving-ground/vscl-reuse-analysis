import VSCLReuse.P17.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p17AsFPModel (fp : P17FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private theorem p17_dotProduct_error (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P17GammaValid fp.u n) :
    |p17RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p17Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  have hv : NumStability.gammaValid (p17AsFPModel fp) n := by
    simpa [NumStability.gammaValid, P17GammaValid, p17AsFPModel] using hvalid
  simpa [p17RoundedDotProduct, NumStability.fl_dotProduct,
    p17Gamma, NumStability.gamma, p17AsFPModel] using
      NumStability.dotProduct_error_bound (p17AsFPModel fp) n x y hv

private theorem p17_matMul_error (fp : P17FPModel) (n : ℕ)
    (A B : P17RealMatrix n) (hvalid : P17GammaValid fp.u n)
    (i j : Fin n) :
    |p17RoundedMatMul fp A B i j - p17MatMul A B i j| ≤
      p17Gamma fp.u n * ∑ k : Fin n, |A i k| * |B k j| := by
  simpa [p17RoundedMatMul, p17MatMul] using
    p17_dotProduct_error fp n (A i) (fun k => B k j) hvalid

/-- P17-C2: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p17_c2_newton_schulz_triple_product_error
    (fp : P17FPModel) (n : ℕ) (X : P17RealMatrix n)
    (hvalid : P17GammaValid fp.u n) :
    ∀ i j,
      |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        p17GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P17-C2-H001
  intro i j
  let C := p17RoundedMatMul fp X (p17Transpose X)
  let E := p17MatMul X (p17Transpose X)
  have hsecond :
      |p17RoundedMatMul fp C X i j - p17MatMul C X i j| ≤
        p17Gamma fp.u n * ∑ k : Fin n, |C i k| * |X k j| :=
    p17_matMul_error fp n C X hvalid i j
  have hfirst (k : Fin n) :
      |C i k - E i k| ≤
        p17Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l| := by
    simpa [C, E, p17Transpose] using
      p17_matMul_error fp n X (p17Transpose X) hvalid i k
  have htransport :
      |p17MatMul C X i j - p17MatMul E X i j| ≤
        p17Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    have hpoint (k : Fin n) :
        |(C i k - E i k) * X k j| ≤
          (p17Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hfirst k) (abs_nonneg _)
    calc
      |p17MatMul C X i j - p17MatMul E X i j| =
          |∑ k : Fin n, (C i k - E i k) * X k j| := by
            simp only [p17MatMul, ← Finset.sum_sub_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ ≤ ∑ k : Fin n, |(C i k - E i k) * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin n,
          (p17Gamma fp.u n * ∑ l : Fin n, |X i l| * |X k l|) * |X k j| :=
        Finset.sum_le_sum (fun k _ => hpoint k)
      _ = ∑ k : Fin n,
          p17Gamma fp.u n * ((∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = p17Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
  calc
    |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| =
        |p17RoundedMatMul fp C X i j - p17MatMul E X i j| := rfl
    _ ≤ |p17RoundedMatMul fp C X i j - p17MatMul C X i j| +
          |p17MatMul C X i j - p17MatMul E X i j| := by
      calc
        |p17RoundedMatMul fp C X i j - p17MatMul E X i j| =
            |(p17RoundedMatMul fp C X i j - p17MatMul C X i j) +
              (p17MatMul C X i j - p17MatMul E X i j)| := by
                congr 1
                ring
        _ ≤ _ := abs_add_le _ _
    _ ≤ p17GramTripleErrorMajorant fp X i j := by
      unfold p17GramTripleErrorMajorant
      dsimp [C] at hsecond
      simpa [C] using add_le_add hsecond htransport

end VSCLReuse

import VSCLReuse.P17.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p17AsFPModel (fp : P17FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private theorem p17RoundedDotProduct_error (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P17GammaValid fp.u n) :
    |p17RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p17Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  simpa [p17RoundedDotProduct, p17Gamma, NumStability.fl_dotProduct,
    NumStability.gamma, p17AsFPModel] using
    (NumStability.dotProduct_error_bound (p17AsFPModel fp) n x y
      (by simpa [P17GammaValid, NumStability.gammaValid, p17AsFPModel] using hvalid))

private theorem p17_sum_mul_error {n : ℕ} (a b x budget : Fin n → ℝ) (γ : ℝ)
    (h : ∀ k, |a k - b k| ≤ γ * budget k) :
    |(∑ k, a k * x k) - (∑ k, b k * x k)| ≤
      γ * ∑ k, budget k * |x k| := by
  have hdiff :
      (∑ k, a k * x k) - (∑ k, b k * x k) =
        ∑ k, (a k - b k) * x k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hdiff]
  calc
    |∑ k, (a k - b k) * x k| ≤
        ∑ k, |(a k - b k) * x k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |a k - b k| * |x k| := by simp only [abs_mul]
    _ ≤ ∑ k, (γ * budget k) * |x k| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (h k) (abs_nonneg _)
    _ = γ * ∑ k, budget k * |x k| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- P17-C2: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p17_c2_newton_schulz_triple_product_error
    (fp : P17FPModel) (n : ℕ) (X : P17RealMatrix n)
    (hvalid : P17GammaValid fp.u n) :
    ∀ i j,
      |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        p17GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P17-C2-H001
  intro i j
  have houter := p17RoundedDotProduct_error fp n
    ((p17RoundedMatMul fp X (p17Transpose X)) i) (fun k => X k j) hvalid
  have hinner (k : Fin n) := p17RoundedDotProduct_error fp n
    (X i) (fun l => p17Transpose X l k) hvalid
  have htransport :
      |(∑ k : Fin n, p17RoundedMatMul fp X (p17Transpose X) i k * X k j) -
        (∑ k : Fin n, (∑ l : Fin n, X i l * X k l) * X k j)| ≤
        p17Gamma fp.u n *
          ∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    apply p17_sum_mul_error
    intro k
    simpa [p17RoundedMatMul, p17Transpose] using hinner k
  unfold p17GramTripleErrorMajorant
  calc
    |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        |p17RoundedGramTriple fp X i j -
          ∑ k : Fin n, p17RoundedMatMul fp X (p17Transpose X) i k * X k j| +
        |(∑ k : Fin n, p17RoundedMatMul fp X (p17Transpose X) i k * X k j) -
          p17ExactGramTriple X i j| := abs_sub_le _ _ _
    _ ≤ p17Gamma fp.u n *
          (∑ k : Fin n,
            |p17RoundedMatMul fp X (p17Transpose X) i k| * |X k j|) +
        p17Gamma fp.u n *
          (∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
      apply add_le_add
      · simpa [p17RoundedGramTriple, p17RoundedMatMul] using houter
      · simpa [p17ExactGramTriple, p17MatMul, p17Transpose] using htransport

end VSCLReuse

import VSCLReuse.P17.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

private noncomputable def p17ToNSModel (fp : P17FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private theorem p17_dot_error (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P17GammaValid fp.u n) :
    |p17RoundedDotProduct fp n x y - ∑ k : Fin n, x k * y k| ≤
      p17Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  simpa [p17RoundedDotProduct, p17Gamma, P17GammaValid,
    p17ToNSModel, NumStability.fl_dotProduct, NumStability.gamma,
    NumStability.gammaValid] using
    (NumStability.dotProduct_error_bound (p17ToNSModel fp) n x y hvalid)

/-- P17-C2: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p17_c2_newton_schulz_triple_product_error
    (fp : P17FPModel) (n : ℕ) (X : P17RealMatrix n)
    (hvalid : P17GammaValid fp.u n) :
    ∀ i j,
      |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        p17GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P17-C2-H001
  intro i j
  let R := p17RoundedMatMul fp X (p17Transpose X)
  let E := p17MatMul X (p17Transpose X)
  let γ := p17Gamma fp.u n
  have houter :
      |p17RoundedGramTriple fp X i j - ∑ k : Fin n, R i k * X k j| ≤
        γ * ∑ k : Fin n, |R i k| * |X k j| := by
    simpa only [p17RoundedGramTriple, p17RoundedMatMul] using
      p17_dot_error fp n (R i) (fun k => X k j) hvalid
  have hinner : ∀ k : Fin n,
      |R i k - E i k| ≤ γ * ∑ l : Fin n, |X i l| * |X k l| := by
    intro k
    simpa [R, E, p17RoundedMatMul, p17MatMul, p17Transpose] using
      p17_dot_error fp n (X i) (fun l => X k l) hvalid
  have htransport :
      |(∑ k : Fin n, R i k * X k j) -
          (∑ k : Fin n, E i k * X k j)| ≤
        γ * ∑ k : Fin n,
          (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ k : Fin n, (R i k * X k j - E i k * X k j)| ≤
          ∑ k : Fin n, |R i k * X k j - E i k * X k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |R i k - E i k| * |X k j| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← sub_mul, abs_mul]
      _ ≤ ∑ k : Fin n,
          (γ * ∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = γ * ∑ k : Fin n,
          (∑ l : Fin n, |X i l| * |X k l|) * |X k j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have htriangle :
      |p17RoundedGramTriple fp X i j - ∑ k : Fin n, E i k * X k j| ≤
        |p17RoundedGramTriple fp X i j - ∑ k : Fin n, R i k * X k j| +
          |(∑ k : Fin n, R i k * X k j) -
            (∑ k : Fin n, E i k * X k j)| := by
    have hsplit :
        p17RoundedGramTriple fp X i j - ∑ k : Fin n, E i k * X k j =
          (p17RoundedGramTriple fp X i j - ∑ k : Fin n, R i k * X k j) +
            ((∑ k : Fin n, R i k * X k j) -
              (∑ k : Fin n, E i k * X k j)) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _
  have hfinal := le_trans htriangle (add_le_add houter htransport)
  simpa [p17ExactGramTriple, p17GramTripleErrorMajorant,
    p17MatMul, E, R, γ] using hfinal

end VSCLReuse

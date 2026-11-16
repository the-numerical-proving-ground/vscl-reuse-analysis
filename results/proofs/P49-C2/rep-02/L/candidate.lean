import VSCLReuse.P49.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p49AsFPModel (fp : P49FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private theorem p49_dot_error (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P49GammaValid fp.u n) :
    |p49RoundedDot fp n x y - ∑ k : Fin n, x k * y k| ≤
      p49Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  have h := NumStability.dotProduct_error_bound (p49AsFPModel fp) n x y hvalid
  simpa [p49RoundedDot, NumStability.fl_dotProduct, p49Gamma,
    NumStability.gamma, p49AsFPModel] using h

private theorem p49_block_mul_entries {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m) :
    ∀ i j, p49BlockMatMul (p49LowerFactor A C) (p49UpperFactor V Delta) i j =
      p49ComputedBlockLU A C V Delta i j := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type]
    | inr j =>
      simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, p49MatMul, Fintype.sum_sum_type]
  | inr i =>
    cases j with
    | inl j =>
      simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type]
    | inr j =>
      simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, p49MatMul, Fintype.sum_sum_type]

private theorem p49_majorant_entries {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) :
    ∀ i j, p49FactorizationMajorant A B C D V i j =
      match i, j with
      | .inl _, .inl _ => 0
      | .inl i, .inr j => (∑ k : Fin n, |A i k| * |V k j|) + |B i j|
      | .inr _, .inl _ => 0
      | .inr i, .inr j => (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [p49FactorizationMajorant, p49BlockMatMul,
        p49BorderedMatrix, Fintype.sum_sum_type]
    | inr j =>
      simp [p49FactorizationMajorant, p49BlockMatMul,
        p49BorderedMatrix, Fintype.sum_sum_type]
  | inr i =>
    cases j with
    | inl j =>
      simp [p49FactorizationMajorant, p49BlockMatMul,
        p49BorderedMatrix, Fintype.sum_sum_type]
    | inr j =>
      simp [p49FactorizationMajorant, p49BlockMatMul,
        p49BorderedMatrix, Fintype.sum_sum_type]

private theorem p49_solve_residual_bound {n m : ℕ}
    (fp : P49FPModel) (A : P49Matrix n n) (B : P49Matrix n m)
    (V : P49Matrix n m) (K₁ : ℝ)
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * fp.u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |p49MatMul A V i j - B i j| ≤
      (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hEq⟩ := hsolve j
  have hsum : p49MatMul A V i j - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    have h := hEq i
    simp_rw [add_mul] at h
    rw [Finset.sum_add_distrib] at h
    dsimp [p49MatMul]
    linarith
  rw [hsum, abs_neg]
  calc
    |∑ k : Fin n, EA i k * V k j| ≤
        ∑ k : Fin n, |EA i k * V k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |EA i k| * |V k j| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul]
    _ ≤ ∑ k : Fin n, (K₁ * fp.u * |A i k|) * |V k j| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hEA i k) (abs_nonneg _)
    _ = (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem p49_gamma_coeff (fp : P49FPModel) (n : ℕ)
    (hvalid : P49GammaValid fp.u (n + 1)) :
    fp.u ≤ p49Gamma fp.u (n + 1) ∧
      p49Gamma fp.u n + fp.u + p49Gamma fp.u n * fp.u ≤
        p49Gamma fp.u (n + 1) := by
  let g := p49AsFPModel fp
  have hv : NumStability.gammaValid g (n + 1) := hvalid
  have hv1 : NumStability.gammaValid g 1 :=
    NumStability.gammaValid_mono g (by omega) hv
  have hgn : 0 ≤ NumStability.gamma g n :=
    NumStability.gamma_nonneg g (NumStability.gammaValid_mono g (by omega) hv)
  have hu1 : g.u ≤ NumStability.gamma g 1 :=
    NumStability.u_le_gamma g (by omega) hv1
  have hun : g.u ≤ NumStability.gamma g (n + 1) :=
    NumStability.u_le_gamma g (by omega) hv
  have hs : NumStability.gamma g n + NumStability.gamma g 1 +
      NumStability.gamma g n * NumStability.gamma g 1 ≤
        NumStability.gamma g (n + 1) := by
    simpa using NumStability.gamma_sum_le g n 1 (by simpa using hv)
  constructor
  · simpa [g, p49AsFPModel, p49Gamma, NumStability.gamma] using hun
  · have hc : NumStability.gamma g n + g.u + NumStability.gamma g n * g.u ≤
        NumStability.gamma g n + NumStability.gamma g 1 +
          NumStability.gamma g n * NumStability.gamma g 1 := by
      gcongr
    simpa [g, p49AsFPModel, p49Gamma, NumStability.gamma] using le_trans hc hs

private theorem p49_schur_residual_bound {n m : ℕ}
    (fp : P49FPModel) (C : P49Matrix m n) (V : P49Matrix n m)
    (D : P49Matrix m m) (hvalid : P49GammaValid fp.u (n + 1))
    (i j : Fin m) :
    |p49MatMul C V i j + p49RoundedSchur fp C V D i j - D i j| ≤
      p49Gamma fp.u (n + 1) *
        ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by
  let T := p49MatMul C V i j
  let R := p49RoundedMatMul fp C V i j
  let S := ∑ k : Fin n, |C i k| * |V k j|
  have hvalidn : P49GammaValid fp.u n := by
    exact NumStability.gammaValid_mono (p49AsFPModel fp) (by omega) hvalid
  have hdot : |R - T| ≤ p49Gamma fp.u n * S := by
    simpa [R, T, S, p49RoundedMatMul, p49MatMul] using
      p49_dot_error fp n (C i) (fun k => V k j) hvalidn
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hT : |T| ≤ S := by
    calc
      |T| ≤ ∑ k : Fin n, |C i k * V k j| := by
        dsimp [T, p49MatMul]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  have hR : |R| ≤ (1 + p49Gamma fp.u n) * S := by
    calc
      |R| ≤ |R - T| + |T| := by
        have h := abs_add_le (R - T) T
        simpa only [sub_add_cancel] using h
      _ ≤ p49Gamma fp.u n * S + S := add_le_add hdot hT
      _ = (1 + p49Gamma fp.u n) * S := by ring
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (D i j) R
  have hDR : |D i j - R| ≤ |D i j| + (1 + p49Gamma fp.u n) * S := by
    calc
      |D i j - R| ≤ |D i j| + |R| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (D i j) 0 R)
      _ ≤ |D i j| + (1 + p49Gamma fp.u n) * S := add_le_add le_rfl hR
  have hγn : 0 ≤ p49Gamma fp.u n := by
    have hv : NumStability.gammaValid (p49AsFPModel fp) n := hvalidn
    simpa [p49Gamma, NumStability.gamma, p49AsFPModel] using
      NumStability.gamma_nonneg (p49AsFPModel fp) hv
  have hDRnonneg : 0 ≤ |D i j| + (1 + p49Gamma fp.u n) * S := by
    positivity
  have hcoeff := p49_gamma_coeff fp n hvalid
  change |T + fp.fl_sub (D i j) R - D i j| ≤ _
  calc
    |T + fp.fl_sub (D i j) R - D i j| =
        |(T - R) + (D i j - R) * δ| := by rw [hsub]; ring
    _ ≤ |T - R| + |D i j - R| * |δ| := by
      calc
        |(T - R) + (D i j - R) * δ| ≤
            |T - R| + |(D i j - R) * δ| := abs_add_le _ _
        _ = |T - R| + |D i j - R| * |δ| := by rw [abs_mul]
    _ ≤ p49Gamma fp.u n * S +
        (|D i j| + (1 + p49Gamma fp.u n) * S) * fp.u := by
      have hdot' : |T - R| ≤ p49Gamma fp.u n * S := by
        simpa [abs_sub_comm] using hdot
      apply add_le_add hdot'
      calc
        |D i j - R| * |δ| ≤
            (|D i j| + (1 + p49Gamma fp.u n) * S) * |δ| :=
          mul_le_mul_of_nonneg_right hDR (abs_nonneg _)
        _ ≤ (|D i j| + (1 + p49Gamma fp.u n) * S) * fp.u :=
          mul_le_mul_of_nonneg_left hδ hDRnonneg
    _ = fp.u * |D i j| +
        (p49Gamma fp.u n + fp.u + p49Gamma fp.u n * fp.u) * S := by ring
    _ ≤ p49Gamma fp.u (n + 1) * |D i j| +
        p49Gamma fp.u (n + 1) * S := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoeff.1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hcoeff.2 hS)
    _ = p49Gamma fp.u (n + 1) * (S + |D i j|) := by ring

/-- P49-C2: full Lemma 1, bordered block factorization error. -/
theorem p49_c2_bordered_block_factorization_error
    {n m : ℕ} (fp : P49FPModel)
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) (K₁ : ℝ)
    (hK₁ : 0 ≤ K₁)
    (hvalid : P49GammaValid fp.u (n + 1))
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * fp.u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j)) :
    let Delta := p49RoundedSchur fp C V D
    let μ₁ := max (K₁ * fp.u) (p49Gamma fp.u (n + 1))
    ∃ E : P49BlockMatrix n m,
      (∀ i j,
        p49BlockMatMul (p49LowerFactor A C)
            (p49UpperFactor V Delta) i j =
          p49BorderedMatrix A B C D i j + E i j) ∧
      (∀ i j,
        |E i j| ≤ μ₁ * p49FactorizationMajorant A B C D V i j) := by
  -- PROOF_START P49-C2-H001
  let Delta := p49RoundedSchur fp C V D
  let μ₁ := max (K₁ * fp.u) (p49Gamma fp.u (n + 1))
  let E : P49BlockMatrix n m :=
    p49BorderedMatrix (fun _ _ => 0)
      (fun i j => p49MatMul A V i j - B i j)
      (fun _ _ => 0)
      (fun i j => p49MatMul C V i j + Delta i j - D i j)
  have hμ : 0 ≤ μ₁ :=
    le_trans (mul_nonneg hK₁ fp.u_nonneg) (le_max_left _ _)
  refine ⟨E, ?_, ?_⟩
  · intro i j
    rw [p49_block_mul_entries A C V Delta i j]
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [p49ComputedBlockLU, p49BorderedMatrix, E]
      | inr j =>
        simp only [p49ComputedBlockLU, p49BorderedMatrix, E]
        ring
    | inr i =>
      cases j with
      | inl j => simp [p49ComputedBlockLU, p49BorderedMatrix, E]
      | inr j =>
        simp only [p49ComputedBlockLU, p49BorderedMatrix, E]
        ring
  · intro i j
    rw [p49_majorant_entries A B C D V i j]
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [E, p49BorderedMatrix]
      | inr j =>
        change |p49MatMul A V i j - B i j| ≤
          μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|)
        have hS : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        calc
          |p49MatMul A V i j - B i j| ≤
              (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| :=
            p49_solve_residual_bound fp A B V K₁ hsolve i j
          _ ≤ μ₁ * ∑ k : Fin n, |A i k| * |V k j| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hS
          _ ≤ μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) := by
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hμ
    | inr i =>
      cases j with
      | inl j => simp [E, p49BorderedMatrix]
      | inr j =>
        change |p49MatMul C V i j + Delta i j - D i j| ≤
          μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|)
        have hS : 0 ≤ (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
          positivity
        calc
          |p49MatMul C V i j + Delta i j - D i j| ≤
              p49Gamma fp.u (n + 1) *
                ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) :=
            p49_schur_residual_bound fp C V D hvalid i j
          _ ≤ μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hS

end VSCLReuse

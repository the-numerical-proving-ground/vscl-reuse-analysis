import VSCLReuse.P49.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p49FPBridge (fp : P49FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩ <;> simp [fp.u_nonneg]
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩ <;> simp [fp.u_nonneg]

private theorem p49_dot_error (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P49GammaValid fp.u n) :
    |p49RoundedDot fp n x y - ∑ k : Fin n, x k * y k| ≤
      p49Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  simpa only [p49RoundedDot, NumStability.fl_dotProduct, p49Gamma,
    NumStability.gamma, p49FPBridge] using
    NumStability.dotProduct_error_bound (p49FPBridge fp) n x y hvalid

private theorem p49_block_product {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m) :
    p49BlockMatMul (p49LowerFactor A C) (p49UpperFactor V Delta) =
      p49ComputedBlockLU A C V Delta := by
  funext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix]
    | inr j => simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, p49MatMul]
  | inr i =>
    cases j with
    | inl j => simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix]
    | inr j => simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
        p49ComputedBlockLU, p49BorderedMatrix, p49MatMul]

private theorem p49_gamma_step (fp : P49FPModel) (n : ℕ)
    (hvalid : P49GammaValid fp.u (n + 1)) :
    p49Gamma fp.u n + fp.u + p49Gamma fp.u n * fp.u ≤
      p49Gamma fp.u (n + 1) := by
  let fp' := p49FPBridge fp
  have hv : NumStability.gammaValid fp' (n + 1) := hvalid
  have hvn : NumStability.gammaValid fp' n :=
    NumStability.gammaValid_mono fp' (Nat.le_succ n) hv
  have hv1 : NumStability.gammaValid fp' 1 :=
    NumStability.gammaValid_mono fp' (by omega) hv
  have hg : 0 ≤ NumStability.gamma fp' n :=
    NumStability.gamma_nonneg fp' hvn
  have hu : fp.u ≤ NumStability.gamma fp' 1 := by
    simpa [fp', p49FPBridge] using NumStability.u_le_gamma fp' (by omega : 0 < 1) hv1
  have hs := NumStability.gamma_sum_le fp' n 1 hv
  have hm : NumStability.gamma fp' n * fp.u ≤
      NumStability.gamma fp' n * NumStability.gamma fp' 1 :=
    mul_le_mul_of_nonneg_left hu hg
  have h : NumStability.gamma fp' n + fp.u +
      NumStability.gamma fp' n * fp.u ≤
      NumStability.gamma fp' (n + 1) := by
    have hs' : NumStability.gamma fp' n + NumStability.gamma fp' 1 +
      NumStability.gamma fp' n * NumStability.gamma fp' 1 ≤
      NumStability.gamma fp' (n + 1) := by simpa using hs
    linarith
  simpa [fp', p49FPBridge, p49Gamma, NumStability.gamma] using h

private theorem p49_schur_error {n m : ℕ} (fp : P49FPModel)
    (C : P49Matrix m n) (V : P49Matrix n m) (D : P49Matrix m m)
    (hvalid : P49GammaValid fp.u (n + 1)) (i j : Fin m) :
    |p49MatMul C V i j + p49RoundedSchur fp C V D i j - D i j| ≤
      p49Gamma fp.u (n + 1) *
        (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) := by
  let t := p49MatMul C V i j
  let r := p49RoundedMatMul fp C V i j
  let s := ∑ k : Fin n, |C i k| * |V k j|
  let g := p49Gamma fp.u n
  let G := p49Gamma fp.u (n + 1)
  have hvn : P49GammaValid fp.u n := by
    unfold P49GammaValid at hvalid ⊢
    have hn : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    nlinarith [mul_le_mul_of_nonneg_right hn fp.u_nonneg]
  have hr : |r - t| ≤ g * s := by
    simpa [r, t, s, g, p49RoundedMatMul, p49MatMul] using
      p49_dot_error fp n (C i) (fun k => V k j) hvn
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have ht : |t| ≤ s := by
    simpa [t, s, p49MatMul, abs_mul] using
      (Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun k : Fin n => C i k * V k j))
  have hg : 0 ≤ g := by
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast n.zero_le) fp.u_nonneg
    · unfold P49GammaValid at hvn
      dsimp [g, p49Gamma]
      linarith
  have hG : 0 ≤ G := by
    apply div_nonneg
    · exact mul_nonneg (by exact_mod_cast (n + 1).zero_le) fp.u_nonneg
    · unfold P49GammaValid at hvalid
      dsimp [G, p49Gamma]
      linarith
  have huG : fp.u ≤ G := by
    have hv : NumStability.gammaValid (p49FPBridge fp) (n + 1) := hvalid
    simpa [G, p49Gamma, NumStability.gamma, p49FPBridge] using
      NumStability.u_le_gamma (p49FPBridge fp) (by omega : 0 < n + 1) hv
  have hstep : g + fp.u + g * fp.u ≤ G := p49_gamma_step fp n hvalid
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (D i j) r
  have hidentity : t + p49RoundedSchur fp C V D i j - D i j =
      (t - r) + (D i j - r) * δ := by
    change t + fp.fl_sub (D i j) r - D i j = _
    rw [hsub]
    ring
  have hrabs : |r| ≤ s + g * s := by
    calc
      |r| = |(r - t) + t| := by ring
      _ ≤ |r - t| + |t| := abs_add_le _ _
      _ ≤ g * s + s := add_le_add hr ht
      _ = s + g * s := by ring
  have hDr : |D i j - r| ≤ |D i j| + s + g * s := by
    calc
      |D i j - r| ≤ |D i j| + |r| := by simpa using abs_sub_le (D i j) 0 r
      _ ≤ |D i j| + (s + g * s) := add_le_add le_rfl hrabs
      _ = |D i j| + s + g * s := by ring
  have hbase : 0 ≤ |D i j| + s + g * s := by
    positivity
  calc
    |p49MatMul C V i j + p49RoundedSchur fp C V D i j - D i j|
        = |(t - r) + (D i j - r) * δ| := by simpa [t] using congrArg abs hidentity
    _ ≤ |t - r| + |(D i j - r) * δ| := abs_add_le _ _
    _ ≤ g * s + (|D i j| + s + g * s) * fp.u := by
      rw [abs_mul]
      apply add_le_add
      · simpa only [abs_sub_comm] using hr
      · exact le_trans
          (mul_le_mul_of_nonneg_right hDr (abs_nonneg δ))
          (mul_le_mul_of_nonneg_left hδ hbase)
    _ = fp.u * |D i j| + (g + fp.u + g * fp.u) * s := by ring
    _ ≤ G * |D i j| + G * s := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right huG (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hstep hs)
    _ = G * (|D i j| + s) := by ring

private theorem p49_solve_error {n m : ℕ} (fp : P49FPModel)
    (A : P49Matrix n n) (B : P49Matrix n m) (V : P49Matrix n m)
    (K₁ : ℝ)
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * fp.u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |p49MatMul A V i j - B i j| ≤
      K₁ * fp.u * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hsol⟩ := hsolve j
  have hdiff : p49MatMul A V i j - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    rw [← hsol i]
    simp only [p49MatMul, add_mul, Finset.sum_add_distrib]
    ring
  calc
    |p49MatMul A V i j - B i j| = |∑ k : Fin n, EA i k * V k j| := by
      rw [hdiff, abs_neg]
    _ ≤ ∑ k : Fin n, |EA i k * V k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n, |EA i k| * |V k j| := by simp_rw [abs_mul]
    _ ≤ ∑ k : Fin n, (K₁ * fp.u * |A i k|) * |V k j| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hEA i k) (abs_nonneg _)
    _ = K₁ * fp.u * ∑ k : Fin n, |A i k| * |V k j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem p49_majorant_topright {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i : Fin n) (j : Fin m) :
    p49FactorizationMajorant A B C D V (.inl i) (.inr j) =
      (∑ k : Fin n, |A i k| * |V k j|) + |B i j| := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix]

private theorem p49_majorant_bottomright {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i j : Fin m) :
    p49FactorizationMajorant A B C D V (.inr i) (.inr j) =
      (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix]

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
  dsimp only
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
    rw [p49_block_product]
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [E, p49ComputedBlockLU, p49BorderedMatrix]
      | inr j =>
        simp only [E, p49ComputedBlockLU, p49BorderedMatrix]
        ring
    | inr i =>
      cases j with
      | inl j => simp [E, p49ComputedBlockLU, p49BorderedMatrix]
      | inr j =>
        simp only [E, p49ComputedBlockLU, p49BorderedMatrix]
        ring
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [E, p49FactorizationMajorant, p49BlockMatMul,
          p49BorderedMatrix]
      | inr j =>
        change |p49MatMul A V i j - B i j| ≤
          μ₁ * p49FactorizationMajorant A B C D V (.inl i) (.inr j)
        rw [p49_majorant_topright]
        have hs : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| :=
          Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        calc
          |p49MatMul A V i j - B i j| ≤
              K₁ * fp.u * ∑ k : Fin n, |A i k| * |V k j| :=
            p49_solve_error fp A B V K₁ hsolve i j
          _ ≤ μ₁ * ∑ k : Fin n, |A i k| * |V k j| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs
          _ ≤ μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hμ
    | inr i =>
      cases j with
      | inl j =>
        simp [E, p49FactorizationMajorant, p49BlockMatMul,
          p49BorderedMatrix]
      | inr j =>
        change |p49MatMul C V i j + Delta i j - D i j| ≤
          μ₁ * p49FactorizationMajorant A B C D V (.inr i) (.inr j)
        rw [p49_majorant_bottomright]
        have hs : 0 ≤ (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
          positivity
        calc
          |p49MatMul C V i j + Delta i j - D i j| ≤
              p49Gamma fp.u (n + 1) *
                (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) :=
            p49_schur_error fp C V D hvalid i j
          _ = p49Gamma fp.u (n + 1) *
              ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by ring
          _ ≤ μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hs

end VSCLReuse

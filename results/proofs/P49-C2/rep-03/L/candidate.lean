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
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p49_rounded_dot_error (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P49GammaValid fp.u n) :
    |p49RoundedDot fp n x y - ∑ k : Fin n, x k * y k| ≤
      p49Gamma fp.u n * ∑ k : Fin n, |x k| * |y k| := by
  let f := p49AsFPModel fp
  have hv : NumStability.gammaValid f n := hvalid
  have h := NumStability.dotProduct_error_bound f n x y hv
  simpa only [p49RoundedDot, NumStability.fl_dotProduct, p49Gamma,
    NumStability.gamma, f, p49AsFPModel] using h

private lemma p49_gamma_step (fp : P49FPModel) (n : ℕ)
    (hvalid : P49GammaValid fp.u (n + 1)) :
    fp.u + (1 + fp.u) * p49Gamma fp.u n ≤ p49Gamma fp.u (n + 1) := by
  let f := p49AsFPModel fp
  have hv : NumStability.gammaValid f (n + 1) := hvalid
  have hv₁ : NumStability.gammaValid f 1 :=
    NumStability.gammaValid_mono f (by omega) hv
  have hvₙ : NumStability.gammaValid f n :=
    NumStability.gammaValid_mono f (Nat.le_succ n) hv
  have hsum := NumStability.gamma_sum_le f 1 n (by simpa [Nat.add_comm] using hv)
  have hu := NumStability.u_le_gamma f Nat.one_pos hv₁
  have hγn := NumStability.gamma_nonneg f hvₙ
  have hmul := mul_le_mul_of_nonneg_right hu hγn
  change f.u + (1 + f.u) * NumStability.gamma f n ≤
    NumStability.gamma f (n + 1)
  have hsum' : NumStability.gamma f 1 + NumStability.gamma f n +
      NumStability.gamma f 1 * NumStability.gamma f n ≤
      NumStability.gamma f (n + 1) := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
  nlinarith [hu, hmul, hsum']

private lemma p49_schur_scalar_error (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (d : ℝ)
    (hvalid : P49GammaValid fp.u (n + 1)) :
    |(∑ k : Fin n, x k * y k) +
        fp.fl_sub d (p49RoundedDot fp n x y) - d| ≤
      p49Gamma fp.u (n + 1) *
        (|d| + ∑ k : Fin n, |x k| * |y k|) := by
  let t : ℝ := ∑ k : Fin n, x k * y k
  let r : ℝ := p49RoundedDot fp n x y
  let s : ℝ := ∑ k : Fin n, |x k| * |y k|
  let g : ℝ := p49Gamma fp.u n
  let g₁ : ℝ := p49Gamma fp.u (n + 1)
  have hs : 0 ≤ s := Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hgn : 0 ≤ g := by
    let f := p49AsFPModel fp
    have hv : NumStability.gammaValid f n :=
      NumStability.gammaValid_mono f (Nat.le_succ n) hvalid
    simpa [g, p49Gamma, NumStability.gamma, f, p49AsFPModel] using
      NumStability.gamma_nonneg f hv
  have hvn : P49GammaValid fp.u n := by
    unfold P49GammaValid at hvalid ⊢
    have hn : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hn fp.u_nonneg) hvalid
  have hdote : |r - t| ≤ g * s := p49_rounded_dot_error fp n x y hvn
  have ht : |t| ≤ s := by
    calc
      |t| ≤ ∑ k : Fin n, |x k * y k| := Finset.abs_sum_le_sum_abs _ _
      _ = s := by simp [s, abs_mul]
  have hr : |r| ≤ (1 + g) * s := by
    calc
      |r| = |(r - t) + t| := by ring
      _ ≤ |r - t| + |t| := abs_add_le _ _
      _ ≤ g * s + s := add_le_add hdote ht
      _ = (1 + g) * s := by ring
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub d r
  have hstep : fp.u + (1 + fp.u) * g ≤ g₁ := p49_gamma_step fp n hvalid
  have hu : fp.u ≤ g₁ := by
    have hprod : 0 ≤ (1 + fp.u) * g :=
      mul_nonneg (by linarith [fp.u_nonneg]) hgn
    linarith
  have htr : |t - r| ≤ g * s := by simpa [abs_sub_comm] using hdote
  have hdiff : |d - r| ≤ |d| + |r| := by
    simpa [sub_eq_add_neg] using (abs_add_le d (-r))
  calc
    |t + fp.fl_sub d r - d| = |(t - r) + (d - r) * δ| := by rw [hsub]; congr 1; ring
    _ ≤ |t - r| + |(d - r) * δ| := abs_add_le _ _
    _ ≤ g * s + fp.u * (|d| + |r|) := by
      have hδmul : |(d - r) * δ| ≤ fp.u * (|d| + |r|) := by
        rw [abs_mul]
        calc
          |d - r| * |δ| ≤ |d - r| * fp.u :=
            mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
          _ ≤ (|d| + |r|) * fp.u :=
            mul_le_mul_of_nonneg_right hdiff fp.u_nonneg
          _ = fp.u * (|d| + |r|) := by ring
      exact add_le_add htr hδmul
    _ ≤ g * s + fp.u * (|d| + (1 + g) * s) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_left
          (mul_le_mul_of_nonneg_left (add_le_add_left hr |d|) fp.u_nonneg) (g * s))
    _ ≤ g₁ * (|d| + s) := by
      have hA : fp.u * |d| ≤ g₁ * |d| :=
        mul_le_mul_of_nonneg_right hu (abs_nonneg d)
      have hB : (g + fp.u * (1 + g)) * s ≤ g₁ * s := by
        apply mul_le_mul_of_nonneg_right _ hs
        nlinarith [hstep]
      nlinarith

private lemma p49_block_product {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m)
    (i j : P49BlockIndex n m) :
    p49BlockMatMul (p49LowerFactor A C) (p49UpperFactor V Delta) i j =
      p49ComputedBlockLU A C V Delta i j := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49BorderedMatrix, p49ComputedBlockLU, p49MatMul,
      Fintype.sum_sum_type, Finset.sum_ite_eq', Finset.sum_ite_eq]

private lemma p49_majorant_entry {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) (i j : P49BlockIndex n m) :
    p49FactorizationMajorant A B C D V i j =
      match i, j with
      | .inl _, .inl _ => 0
      | .inl i, .inr j =>
          (∑ k : Fin n, |A i k| * |V k j|) + |B i j|
      | .inr _, .inl _ => 0
      | .inr i, .inr j =>
          (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [p49FactorizationMajorant, p49BlockMatMul,
      p49BorderedMatrix, Fintype.sum_sum_type,
      Finset.sum_ite_eq']

private lemma p49_solve_column_error {n m : ℕ}
    (fp : P49FPModel) (A : P49Matrix n n) (B : P49Matrix n m)
    (V : P49Matrix n m) (K₁ : ℝ)
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * fp.u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |p49MatMul A V i j - B i j| ≤
      (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hEq⟩ := hsolve j
  have herr : p49MatMul A V i j - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    rw [← hEq i]
    simp only [p49MatMul, add_mul, Finset.sum_add_distrib]
    ring
  rw [herr, abs_neg]
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
  let E : P49BlockMatrix n m := fun i j =>
    p49ComputedBlockLU A C V Delta i j - p49BorderedMatrix A B C D i j
  have hμ : 0 ≤ μ₁ :=
    le_trans (mul_nonneg hK₁ fp.u_nonneg) (le_max_left _ _)
  refine ⟨E, ?_, ?_⟩
  · intro i j
    dsimp [E]
    rw [p49_block_product]
    ring
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entry]
    · have hcol := p49_solve_column_error fp A B V K₁ hsolve i j
      have hs : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have hbound :
          |p49MatMul A V i j - B i j| ≤
            μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) := by
        calc
          |p49MatMul A V i j - B i j| ≤
              (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := hcol
          _ ≤ μ₁ * ∑ k : Fin n, |A i k| * |V k j| :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hs
          _ ≤ μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hμ
      simpa [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entry]
        using hbound
    · simp [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entry]
    · have hschur := p49_schur_scalar_error fp n (C i) (fun k => V k j)
        (D i j) hvalid
      have hs : 0 ≤ |D i j| + ∑ k : Fin n, |C i k| * |V k j| := by
        positivity
      have hbound :
          |p49MatMul C V i j + Delta i j - D i j| ≤
            μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by
        calc
          |p49MatMul C V i j + Delta i j - D i j| ≤
              p49Gamma fp.u (n + 1) *
                (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) := by
              simpa [Delta, p49RoundedSchur, p49RoundedMatMul, p49MatMul] using hschur
          _ ≤ μ₁ * (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hs
          _ = μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by ring
      simpa [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entry]
        using hbound

end VSCLReuse

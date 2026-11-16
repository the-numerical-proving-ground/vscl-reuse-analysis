import VSCLReuse.P49.Definitions

namespace VSCLReuse

open scoped BigOperators



private lemma p49_gamma_step (u r : ℝ) (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hv : (r + 1) * u < 1) :
    r * u / (1 - r * u) * (1 + u) + u ≤
      (r + 1) * u / (1 - (r + 1) * u) := by
  have hd₁ : 0 < 1 - r * u := by nlinarith
  have hd₂ : 0 < 1 - (r + 1) * u := by linarith
  have hn : 0 ≤ (r + 1) * u := mul_nonneg (by linarith) hu
  have heq : r * u / (1 - r * u) * (1 + u) + u =
      (r + 1) * u / (1 - r * u) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ hd₁ hd₂).2
  nlinarith [mul_nonneg hn hu]

private lemma p49_gamma_ge_u (u r : ℝ) (hu : 0 ≤ u) (hr : 1 ≤ r)
    (hv : r * u < 1) : u ≤ r * u / (1 - r * u) := by
  have hd : 0 < 1 - r * u := by linarith
  have hru : u ≤ r * u := by nlinarith
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg hu (show 0 ≤ r * u from mul_nonneg (by linarith) hu)]

private lemma p49_round_step
    (u g G S Q s t q v w : ℝ)
    (hu : 0 ≤ u) (hQ : 0 ≤ Q) (hq : 0 ≤ q)
    (hS : |S| ≤ Q) (ht : |t| ≤ q)
    (hprev : |s - S| ≤ g * Q)
    (hmul : |v - t| ≤ u * |t|)
    (hadd : |w - (s + v)| ≤ u * |s + v|)
    (hcoef : g * (1 + u) + u ≤ G)
    (hcoef' : 2 * u + u ^ 2 ≤ G) :
    |w - (S + t)| ≤ G * (Q + q) := by
  have hs : |s| ≤ |S| + |s - S| := by
    have h := abs_add_le S (s - S)
    convert h using 1 <;> ring
  have hv : |v| ≤ |t| + |v - t| := by
    have h := abs_add_le t (v - t)
    convert h using 1 <;> ring
  have hsv : |s + v| ≤ |s| + |v| := abs_add_le s v
  have hsq : |s + v| ≤ (1 + g) * Q + (1 + u) * q := by
    have ht' : u * |t| ≤ u * q := mul_le_mul_of_nonneg_left ht hu
    nlinarith
  have hlast : |w - (S + t)| ≤
      |w - (s + v)| + |s - S| + |v - t| := by
    calc
      |w - (S + t)| = |(w - (s + v)) + ((s - S) + (v - t))| := by ring
      _ ≤ |w - (s + v)| + |(s - S) + (v - t)| := abs_add_le _ _
      _ ≤ |w - (s + v)| + (|s - S| + |v - t|) :=
        add_le_add_right (abs_add_le _ _) _
      _ = _ := by ring
  have hround : u * |s + v| ≤ u * ((1 + g) * Q + (1 + u) * q) :=
    mul_le_mul_of_nonneg_left hsq hu
  have hmul' : u * |t| ≤ u * q := mul_le_mul_of_nonneg_left ht hu
  have hleft : (g * (1 + u) + u) * Q ≤ G * Q :=
    mul_le_mul_of_nonneg_right hcoef hQ
  have hright : (2 * u + u ^ 2) * q ≤ G * q :=
    mul_le_mul_of_nonneg_right hcoef' hq
  nlinarith

private lemma p49_fl_mul_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul x y
  rw [heq]
  have h : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p49_fl_add_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add x y
  rw [heq]
  have h : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p49_fold_bound (fp : P49FPModel) :
    ∀ n (x y : Fin n → ℝ), P49GammaValid fp.u n →
      |Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 -
        ∑ i : Fin n, x i * y i| ≤
      p49Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  intro n
  induction n with
  | zero =>
      intro x y hv
      simp [p49Gamma]
  | succ n ih =>
      intro x y hv
      by_cases hn : n = 0
      · subst n
        have hm := p49_fl_mul_error fp (x 0) (y 0)
        have huvalid : fp.u < 1 := by simpa [P49GammaValid] using hv
        have hg : fp.u ≤ p49Gamma fp.u 1 := by
          simpa [p49Gamma] using
            p49_gamma_ge_u fp.u 1 fp.u_nonneg le_rfl (by simpa using huvalid)
        have hbound : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p49Gamma fp.u 1 * |x 0 * y 0| :=
          le_trans hm (mul_le_mul_of_nonneg_right hg (abs_nonneg _))
        simpa [Fin.foldl_succ, Fin.sum_univ_one, fp.fl_add_zero] using hbound
      let x' : Fin n → ℝ := fun i => x i.castSucc
      let y' : Fin n → ℝ := fun i => y i.castSucc
      have hv' : P49GammaValid fp.u n := by
        unfold P49GammaValid at hv ⊢
        have hcast : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := by
          push_cast
          nlinarith [fp.u_nonneg]
        exact lt_of_le_of_lt hcast hv
      have hprev := ih x' y' hv'
      let S : ℝ := ∑ i : Fin n, x' i * y' i
      let Q : ℝ := ∑ i : Fin n, |x' i * y' i|
      let s : ℝ := Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x' i) (y' i))) 0
      let t : ℝ := x (Fin.last n) * y (Fin.last n)
      let v : ℝ := fp.fl_mul (x (Fin.last n)) (y (Fin.last n))
      let w : ℝ := fp.fl_add s v
      let g : ℝ := p49Gamma fp.u n
      let G : ℝ := p49Gamma fp.u (n + 1)
      have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i hi => abs_nonneg _)
      have hS : |S| ≤ Q := by
        simpa [S, Q] using
          (Finset.abs_sum_le_sum_abs (fun i : Fin n => x' i * y' i) Finset.univ)
      have hp : |s - S| ≤ g * Q := by simpa [s, S, g, Q] using hprev
      have hm : |v - t| ≤ fp.u * |t| := p49_fl_mul_error fp _ _
      have ha : |w - (s + v)| ≤ fp.u * |s + v| := p49_fl_add_error fp _ _
      have hvstep : ((n : ℝ) + 1) * fp.u < 1 := by
        simpa [P49GammaValid, Nat.cast_add, Nat.cast_one] using hv
      have hc : g * (1 + fp.u) + fp.u ≤ G := by
        simpa [g, G, p49Gamma, Nat.cast_add, Nat.cast_one] using
          p49_gamma_step fp.u (n : ℝ) fp.u_nonneg
            (by positivity) hvstep
      have hc' : 2 * fp.u + fp.u ^ 2 ≤ G := by
        have hge : fp.u ≤ g := by
          apply p49_gamma_ge_u fp.u (n : ℝ) fp.u_nonneg
          · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
          · exact hv'
        have hprod : 0 ≤ (g - fp.u) * (1 + fp.u) :=
          mul_nonneg (sub_nonneg.mpr hge) (add_nonneg zero_le_one fp.u_nonneg)
        nlinarith
      have hstep : |w - (S + t)| ≤ G * (Q + |t|) :=
        p49_round_step fp.u g G S Q s t |t| v w fp.u_nonneg hQ (abs_nonneg _)
          hS le_rfl hp hm ha hc hc'
      simpa [w, v, t, s, S, Q, G, x', y', Fin.foldl_succ_last,
        Fin.sum_univ_castSucc] using hstep

private lemma p49_roundedDot_eq_fold (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p49RoundedDot fp n x y =
      Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 := by
  cases n with
  | zero => simp [p49RoundedDot]
  | succ n =>
      simp [p49RoundedDot, Fin.foldl_succ, fp.fl_add_zero]

private lemma p49_roundedDot_bound (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P49GammaValid fp.u n) :
    |p49RoundedDot fp n x y - ∑ i : Fin n, x i * y i| ≤
      p49Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  rw [p49_roundedDot_eq_fold]
  simpa only [abs_mul] using p49_fold_bound fp n x y hv

private lemma p49_fl_sub_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * |x - y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_sub x y
  rw [heq]
  have h : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x - y))

private lemma p49_sub_step
    (u g G S Q s d w : ℝ)
    (hu : 0 ≤ u) (hQ : 0 ≤ Q) (hS : |S| ≤ Q)
    (hprev : |s - S| ≤ g * Q)
    (hsub : |w - (d - s)| ≤ u * |d - s|)
    (hcoef : g * (1 + u) + u ≤ G) (hug : u ≤ G) :
    |S + w - d| ≤ G * (|d| + Q) := by
  have hs : |s| ≤ |S| + |s - S| := by
    have h := abs_add_le S (s - S)
    convert h using 1 <;> ring
  have hds : |d - s| ≤ |d| + |s| := by
    simpa only [abs_neg] using (abs_add_le d (-s))
  have hdsq : |d - s| ≤ |d| + (1 + g) * Q := by nlinarith
  have herr : |S + w - d| ≤ |s - S| + |w - (d - s)| := by
    calc
      |S + w - d| = |-(s - S) + (w - (d - s))| := by congr 1; abel
      _ ≤ |-(s - S)| + |w - (d - s)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hround : u * |d - s| ≤ u * (|d| + (1 + g) * Q) :=
    mul_le_mul_of_nonneg_left hdsq hu
  have hleft : (g * (1 + u) + u) * Q ≤ G * Q :=
    mul_le_mul_of_nonneg_right hcoef hQ
  have hright : u * |d| ≤ G * |d| :=
    mul_le_mul_of_nonneg_right hug (abs_nonneg _)
  nlinarith

private lemma p49_schur_error (fp : P49FPModel) {n m : ℕ}
    (C : P49Matrix m n) (V : P49Matrix n m) (D : P49Matrix m m)
    (hv : P49GammaValid fp.u (n + 1)) (i j : Fin m) :
    |(∑ k : Fin n, C i k * V k j) + p49RoundedSchur fp C V D i j - D i j| ≤
      p49Gamma fp.u (n + 1) *
        (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) := by
  have hv' : P49GammaValid fp.u n := by
    unfold P49GammaValid at hv ⊢
    have hcast : (n : ℝ) * fp.u ≤ ((n + 1 : ℕ) : ℝ) * fp.u := by
      push_cast
      nlinarith [fp.u_nonneg]
    exact lt_of_le_of_lt hcast hv
  let S : ℝ := ∑ k : Fin n, C i k * V k j
  let Q : ℝ := ∑ k : Fin n, |C i k| * |V k j|
  let s : ℝ := p49RoundedMatMul fp C V i j
  let d : ℝ := D i j
  let w : ℝ := p49RoundedSchur fp C V D i j
  let g : ℝ := p49Gamma fp.u n
  let G : ℝ := p49Gamma fp.u (n + 1)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hS : |S| ≤ Q := by
    simpa [S, Q, abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun k : Fin n => C i k * V k j) Finset.univ)
  have hp : |s - S| ≤ g * Q := by
    simpa [s, S, g, Q, p49RoundedMatMul] using
      p49_roundedDot_bound fp n (C i) (fun k => V k j) hv'
  have hsub : |w - (d - s)| ≤ fp.u * |d - s| := by
    simpa [w, d, s, p49RoundedSchur] using p49_fl_sub_error fp (D i j)
      (p49RoundedMatMul fp C V i j)
  have hvstep : ((n : ℝ) + 1) * fp.u < 1 := by
    simpa [P49GammaValid, Nat.cast_add, Nat.cast_one] using hv
  have hc : g * (1 + fp.u) + fp.u ≤ G := by
    simpa [g, G, p49Gamma, Nat.cast_add, Nat.cast_one] using
      p49_gamma_step fp.u (n : ℝ) fp.u_nonneg (by positivity) hvstep
  have hug : fp.u ≤ G := by
    simpa [G, p49Gamma] using
      p49_gamma_ge_u fp.u (((n + 1 : ℕ) : ℝ)) fp.u_nonneg
        (by exact_mod_cast Nat.le_add_left 1 n) hv
  simpa [S, Q, s, d, w, G] using
    p49_sub_step fp.u g G S Q s d w fp.u_nonneg hQ hS hp hsub hc hug

private lemma p49_block_product {n m : ℕ}
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
            p49BorderedMatrix, p49ComputedBlockLU, Fintype.sum_sum_type,
            mul_ite, ite_mul]
      | inr j =>
          simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
            p49BorderedMatrix, p49ComputedBlockLU, p49MatMul,
            Fintype.sum_sum_type]
  | inr i =>
      cases j with
      | inl j =>
          simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
            p49BorderedMatrix, p49ComputedBlockLU, Fintype.sum_sum_type,
            mul_ite, ite_mul]
      | inr j =>
          simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
            p49BorderedMatrix, p49ComputedBlockLU, p49MatMul,
            Fintype.sum_sum_type, mul_ite, ite_mul]

private lemma p49_majorant_entries {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) :
    ∀ i j, p49FactorizationMajorant A B C D V i j =
      match i, j with
      | .inl _, .inl _ => 0
      | .inl i, .inr j => |B i j| + ∑ k : Fin n, |A i k| * |V k j|
      | .inr _, .inl _ => 0
      | .inr i, .inr j => |D i j| + ∑ k : Fin n, |C i k| * |V k j| := by
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp [p49FactorizationMajorant, p49BlockMatMul,
            p49BorderedMatrix, Fintype.sum_sum_type]
      | inr j =>
          simp [p49FactorizationMajorant, p49BlockMatMul,
            p49BorderedMatrix, Fintype.sum_sum_type, mul_ite, ite_mul, add_comm]
  | inr i =>
      cases j with
      | inl j =>
          simp [p49FactorizationMajorant, p49BlockMatMul,
            p49BorderedMatrix, Fintype.sum_sum_type]
      | inr j =>
          simp [p49FactorizationMajorant, p49BlockMatMul,
            p49BorderedMatrix, Fintype.sum_sum_type, mul_ite, ite_mul, add_comm]

private lemma p49_solver_error {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m) (V : P49Matrix n m)
    (u K₁ : ℝ)
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |(∑ k : Fin n, A i k * V k j) - B i j| ≤
      (K₁ * u) * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hEq⟩ := hsolve j
  have heq : (∑ k : Fin n, A i k * V k j) - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    rw [← hEq i]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring
  rw [heq, abs_neg]
  calc
    |∑ k : Fin n, EA i k * V k j| ≤
        ∑ k : Fin n, |EA i k * V k j| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun k : Fin n => EA i k * V k j) Finset.univ)
    _ ≤ ∑ k : Fin n, (K₁ * u) * (|A i k| * |V k j|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      have h := mul_le_mul_of_nonneg_right (hEA i k) (abs_nonneg (V k j))
      nlinarith
    _ = (K₁ * u) * ∑ k : Fin n, |A i k| * |V k j| := by
      rw [Finset.mul_sum]
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
  refine ⟨fun i j => p49ComputedBlockLU A C V Delta i j -
    p49BorderedMatrix A B C D i j, ?_, ?_⟩
  · intro i j
    rw [p49_block_product]
    ring
  · intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entries]
        | inr j =>
            have h := p49_solver_error A B V fp.u K₁ hsolve i j
            have hsum : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| :=
              Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hcoef : K₁ * fp.u ≤ μ₁ := le_max_left _ _
            have hmu : 0 ≤ μ₁ := le_trans (mul_nonneg hK₁ fp.u_nonneg) hcoef
            have hbound : |(∑ k : Fin n, A i k * V k j) - B i j| ≤
                μ₁ * (|B i j| + ∑ k : Fin n, |A i k| * |V k j|) := by
              calc
                _ ≤ (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := h
                _ ≤ μ₁ * ∑ k : Fin n, |A i k| * |V k j| :=
                  mul_le_mul_of_nonneg_right hcoef hsum
                _ ≤ μ₁ * (|B i j| + ∑ k : Fin n, |A i k| * |V k j|) := by
                  nlinarith [mul_nonneg hmu (abs_nonneg (B i j))]
            simpa [p49ComputedBlockLU, p49BorderedMatrix, p49MatMul,
              p49_majorant_entries] using hbound
    | inr i =>
        cases j with
        | inl j =>
            simp [p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_entries]
        | inr j =>
            have h := p49_schur_error fp C V D hvalid i j
            have hsum : 0 ≤ |D i j| + ∑ k : Fin n, |C i k| * |V k j| := by
              apply add_nonneg (abs_nonneg _)
              exact Finset.sum_nonneg
                (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hcoef : p49Gamma fp.u (n + 1) ≤ μ₁ := le_max_right _ _
            have hbound :
                |(∑ k : Fin n, C i k * V k j) + Delta i j - D i j| ≤
                  μ₁ * (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) :=
              le_trans h (mul_le_mul_of_nonneg_right hcoef hsum)
            simpa [p49ComputedBlockLU, p49BorderedMatrix, p49MatMul,
              p49_majorant_entries, Delta] using hbound

end VSCLReuse

import VSCLReuse.P49.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p49_block_mul_eq {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m) :
    ∀ i j, p49BlockMatMul (p49LowerFactor A C)
        (p49UpperFactor V Delta) i j = p49ComputedBlockLU A C V Delta i j := by
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type,
      p49MatMul, mul_ite, Finset.sum_ite_eq, mul_comm]
  · simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type,
      p49MatMul]
  · simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type,
      p49MatMul, mul_ite, Finset.sum_ite_eq, mul_comm]
  · simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49ComputedBlockLU, p49BorderedMatrix, Fintype.sum_sum_type,
      p49MatMul, mul_ite, Finset.sum_ite_eq, mul_comm]

private theorem p49_majorant_eq {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) :
    (∀ i j, p49FactorizationMajorant A B C D V (.inl i) (.inl j) = 0) ∧
    (∀ i j, p49FactorizationMajorant A B C D V (.inl i) (.inr j) =
      (∑ k : Fin n, |A i k| * |V k j|) + |B i j|) ∧
    (∀ i j, p49FactorizationMajorant A B C D V (.inr i) (.inl j) = 0) ∧
    (∀ i j, p49FactorizationMajorant A B C D V (.inr i) (.inr j) =
      (∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; simp [p49FactorizationMajorant, p49BlockMatMul,
      p49BorderedMatrix, Fintype.sum_sum_type]
  · intros; simp [p49FactorizationMajorant, p49BlockMatMul,
      p49BorderedMatrix, Fintype.sum_sum_type]
  · intros; simp [p49FactorizationMajorant, p49BlockMatMul,
      p49BorderedMatrix, Fintype.sum_sum_type]
  · intros; simp [p49FactorizationMajorant, p49BlockMatMul,
      p49BorderedMatrix, Fintype.sum_sum_type, mul_ite, Finset.sum_ite_eq]

private theorem p49_fl_mul_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hδ (abs_nonneg (x * y))

private theorem p49_fl_sub_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * |x - y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub x y
  rw [hfl]
  have heq : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hδ (abs_nonneg (x - y))

private theorem p49_fl_add_step (fp : P49FPModel)
    (a s r t : ℝ) (hr : |r - t| ≤ fp.u * |t|) :
    |fp.fl_add a r - (s + t)| ≤
      (1 + fp.u) * |a - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |t| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a r
  rw [hfl]
  have heq : (a + r) * (1 + δ) - (s + t) =
      (a - s) + (r - t) + δ * (a + r) := by ring
  rw [heq]
  have h₁ := abs_add_le ((a - s) + (r - t)) (δ * (a + r))
  have h₂ := abs_add_le (a - s) (r - t)
  have h₃ := abs_add_le a r
  have h₄ := abs_add_le (a - s) s
  have h₅ := abs_add_le (r - t) t
  have ha : |a| ≤ |a - s| + |s| := by
    convert h₄ using 1 <;> ring
  have hr' : |r| ≤ |r - t| + |t| := by
    convert h₅ using 1 <;> ring
  have hδmul : |δ * (a + r)| ≤ fp.u * (|a - s| + |s| + fp.u * |t| + |t|) := by
    rw [abs_mul]
    calc
      |δ| * |a + r| ≤ fp.u * |a + r| :=
        mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      _ ≤ fp.u * (|a - s| + |s| + fp.u * |t| + |t|) := by
        apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
        linarith
  nlinarith [sq_nonneg fp.u, abs_nonneg (a - s), abs_nonneg s,
    abs_nonneg t]

private theorem p49_fold_bound_pow (fp : P49FPModel) (q : ℕ)
    (t r : Fin q → ℝ) (b a : ℝ)
    (hinit : |a - b| ≤ fp.u * |b|)
    (hr : ∀ i, |r i - t i| ≤ fp.u * |t i|) :
    |Fin.foldl q (fun acc i => fp.fl_add acc (r i)) a -
      (b + ∑ i : Fin q, t i)| ≤
      ((1 + fp.u) ^ (q + 1) - 1) *
        (|b| + ∑ i : Fin q, |t i|) := by
  induction q generalizing b a with
  | zero =>
      simpa [Fin.foldl_zero] using hinit
  | succ q ih =>
      let t₀ : Fin q → ℝ := fun i => t i.castSucc
      let r₀ : Fin q → ℝ := fun i => r i.castSucc
      let acc := Fin.foldl q (fun z i => fp.fl_add z (r₀ i)) a
      let s := b + ∑ i : Fin q, t₀ i
      let T := |b| + ∑ i : Fin q, |t₀ i|
      let x := t (Fin.last q)
      let y := r (Fin.last q)
      have hprev : |acc - s| ≤ ((1 + fp.u) ^ (q + 1) - 1) * T := by
        exact ih t₀ r₀ b a hinit (fun i => hr i.castSucc)
      have hT : 0 ≤ T := by
        dsimp [T]
        positivity
      have hs : |s| ≤ T := by
        dsimp [s, T]
        calc
          |b + ∑ i : Fin q, t₀ i| ≤ |b| + |∑ i : Fin q, t₀ i| := abs_add_le _ _
          _ ≤ |b| + ∑ i : Fin q, |t₀ i| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs t₀ Finset.univ
      have hstep := p49_fl_add_step fp acc s y x (hr (Fin.last q))
      have hscale := mul_le_mul_of_nonneg_left hprev (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
      have hcoeff : 2 * fp.u + fp.u ^ 2 ≤
          (1 + fp.u) ^ (q + 2) - 1 := by
        have hh := pow_le_pow_right₀ (by linarith [fp.u_nonneg] : (1 : ℝ) ≤ 1 + fp.u)
          (show 2 ≤ q + 2 by omega)
        nlinarith [hh]
      have hcoefscale := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg x)
      have hus := mul_le_mul_of_nonneg_left hs fp.u_nonneg
      have hgoal : |fp.fl_add acc y - (s + x)| ≤
          ((1 + fp.u) ^ (q + 2) - 1) * (T + |x|) := by
        calc
          _ ≤ (1 + fp.u) * |acc - s| + fp.u * |s| +
              (2 * fp.u + fp.u ^ 2) * |x| := hstep
          _ ≤ (1 + fp.u) * (((1 + fp.u) ^ (q + 1) - 1) * T) +
              fp.u * T + ((1 + fp.u) ^ (q + 2) - 1) * |x| := by
                linarith
          _ = ((1 + fp.u) ^ (q + 2) - 1) * (T + |x|) := by
                rw [show q + 2 = q + 1 + 1 by omega, pow_succ]
                ring
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        add_assoc, t₀, r₀, acc, s, T, x, y] using hgoal

private theorem p49_pow_gamma_aux (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) ^ k * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤ 1 := by
  induction k with
  | zero =>
      simp
      linarith
  | succ k ih =>
      have hprev : ((k + 1 : ℕ) : ℝ) * u < 1 := by
        have hk' : ((k + 2 : ℕ) : ℝ) * u < 1 := by
          convert hk using 1 <;> norm_num
        have hkcoeff : ((k + 1 : ℕ) : ℝ) * u ≤ ((k + 2 : ℕ) : ℝ) * u := by
          gcongr
          omega
        linarith
      have hstep : (1 + u) * (1 - ((k + 2 : ℕ) : ℝ) * u) ≤
          1 - ((k + 1 : ℕ) : ℝ) * u := by
        have hsq := mul_nonneg (show (0 : ℝ) ≤ (k + 2 : ℕ) by positivity) (sq_nonneg u)
        push_cast at hsq ⊢
        nlinarith
      have hscale := mul_le_mul_of_nonneg_left hstep
        (pow_nonneg (show 0 ≤ 1 + u by linarith) k)
      have hih := ih hprev
      rw [pow_succ]
      convert le_trans hscale hih using 1 <;> push_cast <;> ring

private theorem p49_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P49GammaValid u (k + 1)) :
    (1 + u) ^ k - 1 ≤ p49Gamma u (k + 1) := by
  have hd : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    dsimp [P49GammaValid] at hk
    linarith
  have hh := p49_pow_gamma_aux u hu k hk
  unfold p49Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private theorem p49_rounded_dot_bound (fp : P49FPModel) (n : ℕ)
    (hvalid : P49GammaValid fp.u (n + 1)) (x y : Fin n → ℝ) :
    |p49RoundedDot fp n x y - ∑ k : Fin n, x k * y k| ≤
      p49Gamma fp.u (n + 1) * ∑ k : Fin n, |x k * y k| := by
  cases n with
  | zero =>
      simp [p49RoundedDot]
  | succ q =>
      let t : Fin q → ℝ := fun i => x i.succ * y i.succ
      let r : Fin q → ℝ := fun i => fp.fl_mul (x i.succ) (y i.succ)
      have hpow := p49_fold_bound_pow fp q t r (x 0 * y 0)
        (fp.fl_mul (x 0) (y 0)) (p49_fl_mul_error fp (x 0) (y 0))
        (fun i => p49_fl_mul_error fp (x i.succ) (y i.succ))
      have hgamma := p49_pow_le_gamma fp.u fp.u_nonneg (q + 1) hvalid
      have hsum : 0 ≤ |x 0 * y 0| + ∑ i : Fin q, |t i| := by positivity
      have hscaled := mul_le_mul_of_nonneg_right hgamma hsum
      have htotal := le_trans hpow hscaled
      simpa only [p49RoundedDot, Fin.sum_univ_succ, t, r,
        show q + 1 + 1 = q + 2 by omega] using htotal

private theorem p49_pow_gamma_aux_exact (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : (k : ℝ) * u < 1) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev : (k : ℝ) * u < 1 := by
        have hle : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
          gcongr
          omega
        linarith
      have hstep : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
          1 - (k : ℝ) * u := by
        have hsq := mul_nonneg (show (0 : ℝ) ≤ (k + 1 : ℕ) by positivity) (sq_nonneg u)
        push_cast at hsq ⊢
        nlinarith
      have hscale := mul_le_mul_of_nonneg_left hstep
        (pow_nonneg (show 0 ≤ 1 + u by linarith) k)
      have hih := ih hprev
      rw [pow_succ]
      convert le_trans hscale hih using 1 <;> push_cast <;> ring

private theorem p49_pow_le_gamma_exact (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P49GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p49Gamma u k := by
  have hd : 0 < 1 - (k : ℝ) * u := by
    dsimp [P49GammaValid] at hk
    linarith
  have hh := p49_pow_gamma_aux_exact u hu k hk
  unfold p49Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private theorem p49_rounded_dot_bound_pow (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    |p49RoundedDot fp n x y - ∑ k : Fin n, x k * y k| ≤
      ((1 + fp.u) ^ n - 1) * ∑ k : Fin n, |x k * y k| := by
  cases n with
  | zero => simp [p49RoundedDot]
  | succ q =>
      let t : Fin q → ℝ := fun i => x i.succ * y i.succ
      let r : Fin q → ℝ := fun i => fp.fl_mul (x i.succ) (y i.succ)
      have hpow := p49_fold_bound_pow fp q t r (x 0 * y 0)
        (fp.fl_mul (x 0) (y 0)) (p49_fl_mul_error fp (x 0) (y 0))
        (fun i => p49_fl_mul_error fp (x i.succ) (y i.succ))
      simpa only [p49RoundedDot, Fin.sum_univ_succ, t, r] using hpow

private theorem p49_schur_scalar_bound (fp : P49FPModel) (n : ℕ)
    (hvalid : P49GammaValid fp.u (n + 1))
    (x y : Fin n → ℝ) (d : ℝ) :
    |(∑ k : Fin n, x k * y k) +
        fp.fl_sub d (p49RoundedDot fp n x y) - d| ≤
      p49Gamma fp.u (n + 1) *
        ((∑ k : Fin n, |x k * y k|) + |d|) := by
  let s := ∑ k : Fin n, x k * y k
  let T := ∑ k : Fin n, |x k * y k|
  let r := p49RoundedDot fp n x y
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hs : |s| ≤ T := by
    exact Finset.abs_sum_le_sum_abs (fun k : Fin n => x k * y k) Finset.univ
  have hr : |r - s| ≤ ((1 + fp.u) ^ n - 1) * T :=
    p49_rounded_dot_bound_pow fp n x y
  have hrabs : |r| ≤ T + |r - s| := by
    have hh := abs_add_le (r - s) s
    have hh' : r - s + s = r := by ring
    rw [hh'] at hh
    linarith
  have hds : |d - r| ≤ |d| + T + |r - s| := by
    have hh : |d - r| ≤ |d| + |r| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le d (-r)
    linarith
  have hsub := p49_fl_sub_error fp d r
  have hmul := mul_le_mul_of_nonneg_left hds fp.u_nonneg
  have htri : |s + fp.fl_sub d r - d| ≤
      |r - s| + |fp.fl_sub d r - (d - r)| := by
    have hh := abs_add_le (s - r) (fp.fl_sub d r - (d - r))
    have heq : s - r + (fp.fl_sub d r - (d - r)) =
        s + fp.fl_sub d r - d := by ring
    rw [heq, abs_sub_comm s r] at hh
    exact hh
  have hbound : |s + fp.fl_sub d r - d| ≤
      ((1 + fp.u) ^ (n + 1) - 1) * T + fp.u * |d| := by
    have hscaled := mul_le_mul_of_nonneg_left hr
      (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
    have hrough : |s + fp.fl_sub d r - d| ≤
        (1 + fp.u) * |r - s| + fp.u * (|d| + T) := by
      linarith
    calc
      _ ≤ (1 + fp.u) * |r - s| + fp.u * (|d| + T) := hrough
      _ ≤ (1 + fp.u) * (((1 + fp.u) ^ n - 1) * T) +
          fp.u * (|d| + T) := by linarith
      _ = ((1 + fp.u) ^ (n + 1) - 1) * T + fp.u * |d| := by
        rw [pow_succ]
        ring
  have hgamma := p49_pow_le_gamma_exact fp.u fp.u_nonneg (n + 1) hvalid
  have hu_le : fp.u ≤ p49Gamma fp.u (n + 1) := by
    have hpow := pow_le_pow_right₀
      (show (1 : ℝ) ≤ 1 + fp.u by linarith [fp.u_nonneg])
      (show 1 ≤ n + 1 by omega)
    norm_num at hpow
    linarith
  have hscaleT := mul_le_mul_of_nonneg_right hgamma hT
  have hscaled := mul_le_mul_of_nonneg_right hu_le (abs_nonneg d)
  dsimp [s, T, r] at *
  calc
    _ ≤ ((1 + fp.u) ^ (n + 1) - 1) * (∑ k : Fin n, |x k * y k|) +
        fp.u * |d| := hbound
    _ ≤ p49Gamma fp.u (n + 1) *
        ((∑ k : Fin n, |x k * y k|) + |d|) := by
      rw [mul_add]
      linarith

private theorem p49_solve_block_bound {n m : ℕ}
    (fp : P49FPModel) (A : P49Matrix n n) (B : P49Matrix n m)
    (V : P49Matrix n m) (K₁ : ℝ)
    (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * fp.u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |(∑ k : Fin n, A i k * V k j) - B i j| ≤
      (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hcol⟩ := hsolve j
  have heq : (∑ k : Fin n, A i k * V k j) - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    have hh := hcol i
    simp_rw [add_mul] at hh
    rw [Finset.sum_add_distrib] at hh
    linarith
  rw [heq, abs_neg]
  calc
    |∑ k : Fin n, EA i k * V k j| ≤
        ∑ k : Fin n, |EA i k * V k j| :=
      Finset.abs_sum_le_sum_abs (fun k : Fin n => EA i k * V k j) Finset.univ
    _ ≤ ∑ k : Fin n, (K₁ * fp.u) * (|A i k| * |V k j|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      have hh := mul_le_mul_of_nonneg_right (hEA i k) (abs_nonneg (V k j))
      nlinarith
    _ = (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := by
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
  let E : P49BlockMatrix n m := fun i j =>
    match i, j with
    | .inl _, .inl _ => 0
    | .inl i, .inr j => p49MatMul A V i j - B i j
    | .inr _, .inl _ => 0
    | .inr i, .inr j => p49MatMul C V i j + Delta i j - D i j
  refine ⟨E, ?_, ?_⟩
  · intro i j
    rw [p49_block_mul_eq]
    rcases i with i | i <;> rcases j with j | j
    · simp [p49ComputedBlockLU, p49BorderedMatrix, E]
    · simp [p49ComputedBlockLU, p49BorderedMatrix, E]
    · simp [p49ComputedBlockLU, p49BorderedMatrix, E]
    · simp [p49ComputedBlockLU, p49BorderedMatrix, E]
      ring
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp [E, (p49_majorant_eq A B C D V).1 i j]
    · rw [(p49_majorant_eq A B C D V).2.1 i j]
      change |p49MatMul A V i j - B i j| ≤
        max (K₁ * fp.u) (p49Gamma fp.u (n + 1)) *
          ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|)
      have hsolve' := p49_solve_block_bound fp A B V K₁ hsolve i j
      have hS : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| := by positivity
      have hμ : 0 ≤ max (K₁ * fp.u) (p49Gamma fp.u (n + 1)) := by
        exact le_trans (mul_nonneg hK₁ fp.u_nonneg) (le_max_left _ _)
      have hscale := mul_le_mul_of_nonneg_right
        (le_max_left (K₁ * fp.u) (p49Gamma fp.u (n + 1))) hS
      calc
        _ ≤ (K₁ * fp.u) * (∑ k : Fin n, |A i k| * |V k j|) := hsolve'
        _ ≤ max (K₁ * fp.u) (p49Gamma fp.u (n + 1)) *
            ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) := by
          nlinarith [mul_nonneg hμ (abs_nonneg (B i j))]
    · simp [E, (p49_majorant_eq A B C D V).2.2.1 i j]
    · rw [(p49_majorant_eq A B C D V).2.2.2 i j]
      change |p49MatMul C V i j + Delta i j - D i j| ≤
        max (K₁ * fp.u) (p49Gamma fp.u (n + 1)) *
          ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|)
      have hschur := p49_schur_scalar_bound fp n hvalid (C i)
        (fun k => V k j) (D i j)
      have hS : 0 ≤ (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
        positivity
      have hscale := mul_le_mul_of_nonneg_right
        (le_max_right (K₁ * fp.u) (p49Gamma fp.u (n + 1))) hS
      dsimp [p49MatMul, Delta, p49RoundedSchur, p49RoundedMatMul] at *
      simp_rw [abs_mul] at hschur
      exact le_trans hschur hscale

end VSCLReuse

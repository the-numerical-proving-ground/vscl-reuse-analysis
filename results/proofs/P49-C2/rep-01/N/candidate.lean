import VSCLReuse.P49.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p49_mul_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x * y| * |δ| ≤ |x * y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

private lemma p49_add_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x + y| * |δ| ≤ (|x| + |y|) * |δ| :=
      mul_le_mul_of_nonneg_right (abs_add_le x y) (abs_nonneg _)
    _ ≤ (|x| + |y|) * fp.u :=
      mul_le_mul_of_nonneg_left hδ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

private lemma p49_sub_error (fp : P49FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub x y
  rw [hfl]
  have heq : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x - y| * |δ| ≤ (|x| + |y|) * |δ| :=
      mul_le_mul_of_nonneg_right (abs_sub x y) (abs_nonneg _)
    _ ≤ (|x| + |y|) * fp.u :=
      mul_le_mul_of_nonneg_left hδ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

private lemma p49RoundedDot_succ_succ (fp : P49FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p49RoundedDot fp (n + 2) x y =
      fp.fl_add
        (p49RoundedDot fp (n + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  simp only [p49RoundedDot, Fin.foldl_succ_last]
  rfl

private lemma p49_gamma_step_real (u t : ℝ)
    (hu : 0 ≤ u) (hut : u ≤ t) (hvalid : t + u < 1) :
    t / (1 - t) + u * (1 + t / (1 - t)) ≤
        (t + u) / (1 - t - u) ∧
      u * (2 + u) ≤ (t + u) / (1 - t - u) := by
  have ht : 0 ≤ t := le_trans hu hut
  have hd1 : 0 < 1 - t := by linarith
  have hd2 : 0 < 1 - t - u := by linarith
  have hd3 : 0 < 1 - 2 * u := by linarith
  have hsum : 0 ≤ t + u := add_nonneg ht hu
  have hstep : t / (1 - t) + u * (1 + t / (1 - t)) =
      (t + u) / (1 - t) := by
    field_simp
    ring
  have hfrac : (t + u) / (1 - t) ≤ (t + u) / (1 - t - u) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    nlinarith [mul_nonneg hsum hu]
  have htwo : u * (2 + u) ≤ 2 * u / (1 - 2 * u) := by
    apply (le_div_iff₀ hd3).2
    nlinarith [mul_nonneg (sq_nonneg u) hu]
  have hmono : 2 * u / (1 - 2 * u) ≤ (t + u) / (1 - t - u) := by
    apply (div_le_div_iff₀ hd3 hd2).2
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hut),
      mul_nonneg (sub_nonneg.mpr hut) (by linarith : 0 ≤ 1 - 2 * u)]
  exact ⟨hstep ▸ hfrac, le_trans htwo hmono⟩

private lemma p49_gamma_step_nat (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hv : P49GammaValid u (k + 1)) :
    p49Gamma u k + u * (1 + p49Gamma u k) ≤ p49Gamma u (k + 1) ∧
      u * (2 + u) ≤ p49Gamma u (k + 1) := by
  have hkc : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hut : u ≤ (k : ℝ) * u := by nlinarith [mul_nonneg (sub_nonneg.mpr hkc) hu]
  have hval : (k : ℝ) * u + u < 1 := by
    simpa only [P49GammaValid, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hv
  simpa only [p49Gamma, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
    sub_add_eq_sub_sub] using p49_gamma_step_real u ((k : ℝ) * u) hu hut hval

private lemma p49_rounded_step (fp : P49FPModel)
    (acc s x y S g : ℝ)
    (hs : |s| ≤ S) (hacc : |acc - s| ≤ g * S) :
    |fp.fl_add acc (fp.fl_mul x y) - (s + x * y)| ≤
      (g + fp.u * (1 + g)) * S +
        fp.u * (2 + fp.u) * |x * y| := by
  let q := fp.fl_mul x y
  have hq : |q - x * y| ≤ fp.u * |x * y| := p49_mul_error fp x y
  have hqabs : |q| ≤ (1 + fp.u) * |x * y| := by
    calc
      |q| = |(q - x * y) + x * y| := by ring
      _ ≤ |q - x * y| + |x * y| := abs_add_le _ _
      _ ≤ fp.u * |x * y| + |x * y| := add_le_add hq le_rfl
      _ = _ := by ring
  have haccabs : |acc| ≤ (1 + g) * S := by
    calc
      |acc| = |(acc - s) + s| := by ring
      _ ≤ |acc - s| + |s| := abs_add_le _ _
      _ ≤ g * S + S := add_le_add hacc hs
      _ = _ := by ring
  have hadd := p49_add_error fp acc q
  have hsum : |acc| + |q| ≤ (1 + g) * S + (1 + fp.u) * |x * y| :=
    add_le_add haccabs hqabs
  have hmul : fp.u * (|acc| + |q|) ≤
      fp.u * ((1 + g) * S + (1 + fp.u) * |x * y|) :=
    mul_le_mul_of_nonneg_left hsum fp.u_nonneg
  have htri : |fp.fl_add acc q - (s + x * y)| ≤
      |fp.fl_add acc q - (acc + q)| + |acc - s| + |q - x * y| := by
    have heq : fp.fl_add acc q - (s + x * y) =
        (fp.fl_add acc q - (acc + q)) + (acc - s) + (q - x * y) := by ring
    rw [heq]
    exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  calc
    |fp.fl_add acc q - (s + x * y)| ≤
        |fp.fl_add acc q - (acc + q)| + |acc - s| + |q - x * y| := htri
    _ ≤ fp.u * (|acc| + |q|) + g * S + fp.u * |x * y| :=
      add_le_add (add_le_add hadd hacc) hq
    _ ≤ fp.u * ((1 + g) * S + (1 + fp.u) * |x * y|) +
        g * S + fp.u * |x * y| :=
      add_le_add (add_le_add hmul le_rfl) le_rfl
    _ = _ := by ring

private lemma p49RoundedDot_error_pos (fp : P49FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    P49GammaValid fp.u (n + 1) →
      |p49RoundedDot fp (n + 1) x y - ∑ i : Fin (n + 1), x i * y i| ≤
        p49Gamma fp.u (n + 1) * ∑ i : Fin (n + 1), |x i * y i| := by
  induction n with
  | zero =>
      intro hv
      have hvu : fp.u < 1 := by simpa [P49GammaValid] using hv
      have hd : 0 < 1 - fp.u := by linarith
      have hγ : fp.u ≤ p49Gamma fp.u 1 := by
        simp only [p49Gamma, Nat.cast_one, one_mul]
        apply (le_div_iff₀ hd).2
        have hu := fp.u_nonneg
        nlinarith [sq_nonneg fp.u]
      have hmul := p49_mul_error fp (x 0) (y 0)
      have hbound := mul_le_mul_of_nonneg_right hγ (abs_nonneg (x 0 * y 0))
      simpa [p49RoundedDot, Fin.sum_univ_succ] using le_trans hmul hbound
  | succ n ih =>
      intro hv
      let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
      let s : ℝ := ∑ i : Fin (n + 1), x' i * y' i
      let S : ℝ := ∑ i : Fin (n + 1), |x' i * y' i|
      let a : ℝ := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
      have hvprev : P49GammaValid fp.u (n + 1) := by
        have hc : (n + 1 : ℝ) ≤ (n + 2 : ℝ) := by norm_num
        have hm := mul_le_mul_of_nonneg_right hc fp.u_nonneg
        have hm' : ((n + 1 : ℕ) : ℝ) * fp.u ≤ ((n + 2 : ℕ) : ℝ) * fp.u := by
          simpa [Nat.cast_add] using hm
        exact lt_of_le_of_lt hm'
          (by simpa [P49GammaValid, Nat.add_assoc] using hv)
      have hprev : |p49RoundedDot fp (n + 1) x' y' - s| ≤
          p49Gamma fp.u (n + 1) * S := ih x' y' hvprev
      have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => abs_nonneg _)
      have hs : |s| ≤ S := by
        dsimp [s, S]
        exact Finset.abs_sum_le_sum_abs _ _
      have hγstep := p49_gamma_step_nat fp.u (n + 1) fp.u_nonneg
        (by omega) (by simpa [Nat.add_assoc] using hv)
      have hraw := p49_rounded_step fp (p49RoundedDot fp (n + 1) x' y')
        s (x (Fin.last (n + 1))) (y (Fin.last (n + 1))) S
        (p49Gamma fp.u (n + 1)) hs hprev
      have hb1 := mul_le_mul_of_nonneg_right hγstep.1 hS
      have hb2 := mul_le_mul_of_nonneg_right hγstep.2 (abs_nonneg a)
      have hfinal : |fp.fl_add (p49RoundedDot fp (n + 1) x' y')
          (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) -
          (s + a)| ≤ p49Gamma fp.u (n + 2) * (S + |a|) := by
        calc
          _ ≤ (p49Gamma fp.u (n + 1) + fp.u * (1 + p49Gamma fp.u (n + 1))) * S +
              fp.u * (2 + fp.u) * |a| := hraw
          _ ≤ p49Gamma fp.u (n + 2) * S + p49Gamma fp.u (n + 2) * |a| :=
            add_le_add hb1 hb2
          _ = _ := by ring
      have hsum : (∑ i : Fin (n + 2), x i * y i) = s + a := by
        simp [s, a, x', y', Fin.sum_univ_castSucc]
      have habssum : (∑ i : Fin (n + 2), |x i * y i|) = S + |a| := by
        simp [S, a, x', y', Fin.sum_univ_castSucc]
      simpa only [p49RoundedDot_succ_succ, hsum, habssum, Nat.add_assoc] using hfinal

private lemma p49RoundedDot_error (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P49GammaValid fp.u n) :
    |p49RoundedDot fp n x y - ∑ i : Fin n, x i * y i| ≤
      p49Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero => simp [p49RoundedDot]
  | succ n => exact p49RoundedDot_error_pos fp n x y hv

private lemma p49_gamma_step_all (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P49GammaValid u (n + 1)) :
    p49Gamma u n + u * (1 + p49Gamma u n) ≤ p49Gamma u (n + 1) ∧
      u ≤ p49Gamma u (n + 1) := by
  cases n with
  | zero =>
      have hvu : u < 1 := by simpa [P49GammaValid] using hv
      have hd : 0 < 1 - u := by linarith
      have hγ : u ≤ p49Gamma u 1 := by
        simp only [p49Gamma, Nat.cast_one, one_mul]
        apply (le_div_iff₀ hd).2
        nlinarith [sq_nonneg u]
      simpa [p49Gamma] using (And.intro hγ hγ)
  | succ k =>
      have hstep := p49_gamma_step_nat u (k + 1) hu (by omega)
        (by simpa [Nat.add_assoc] using hv)
      have hsmall : u ≤ u * (2 + u) := by nlinarith [sq_nonneg u]
      exact ⟨hstep.1, le_trans hsmall hstep.2⟩

private lemma p49RoundedSchur_error (fp : P49FPModel) {n m : ℕ}
    (C : P49Matrix m n) (V : P49Matrix n m) (D : P49Matrix m m)
    (hv : P49GammaValid fp.u (n + 1)) (i j : Fin m) :
    |p49MatMul C V i j + p49RoundedSchur fp C V D i j - D i j| ≤
      p49Gamma fp.u (n + 1) *
        (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) := by
  let p : ℝ := ∑ k : Fin n, C i k * V k j
  let S : ℝ := ∑ k : Fin n, |C i k * V k j|
  let r : ℝ := p49RoundedDot fp n (C i) (fun k => V k j)
  have hvprod : P49GammaValid fp.u n := by
    have hc : (n : ℝ) ≤ (n + 1 : ℝ) := by norm_num
    have hm := mul_le_mul_of_nonneg_right hc fp.u_nonneg
    exact lt_of_le_of_lt hm (by simpa [P49GammaValid, Nat.cast_add] using hv)
  have hdot : |r - p| ≤ p49Gamma fp.u n * S :=
    p49RoundedDot_error fp n (C i) (fun k => V k j) hvprod
  have hs : |p| ≤ S := by
    dsimp [p, S]
    exact Finset.abs_sum_le_sum_abs _ _
  have hrabs : |r| ≤ (1 + p49Gamma fp.u n) * S := by
    calc
      |r| = |(r - p) + p| := by ring
      _ ≤ |r - p| + |p| := abs_add_le _ _
      _ ≤ p49Gamma fp.u n * S + S := add_le_add hdot hs
      _ = _ := by ring
  have hsub := p49_sub_error fp (D i j) r
  have hsub' : |fp.fl_sub (D i j) r - (D i j - r)| ≤
      fp.u * (|D i j| + (1 + p49Gamma fp.u n) * S) :=
    le_trans hsub (mul_le_mul_of_nonneg_left (add_le_add le_rfl hrabs) fp.u_nonneg)
  have htri : |p + fp.fl_sub (D i j) r - D i j| ≤
      |r - p| + |fp.fl_sub (D i j) r - (D i j - r)| := by
    have heq : p + fp.fl_sub (D i j) r - D i j =
        (p - r) + (fp.fl_sub (D i j) r - (D i j - r)) := by ring
    rw [heq]
    calc
      _ ≤ |p - r| + |fp.fl_sub (D i j) r - (D i j - r)| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm p r]
  have hstep := p49_gamma_step_all fp.u n fp.u_nonneg hv
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k hk => abs_nonneg _)
  have hD : 0 ≤ |D i j| := abs_nonneg _
  have hbound : |p + fp.fl_sub (D i j) r - D i j| ≤
      p49Gamma fp.u (n + 1) * (|D i j| + S) := by
    calc
      _ ≤ |r - p| + |fp.fl_sub (D i j) r - (D i j - r)| := htri
      _ ≤ p49Gamma fp.u n * S +
          fp.u * (|D i j| + (1 + p49Gamma fp.u n) * S) :=
        add_le_add hdot hsub'
      _ = fp.u * |D i j| +
          (p49Gamma fp.u n + fp.u * (1 + p49Gamma fp.u n)) * S := by ring
      _ ≤ p49Gamma fp.u (n + 1) * |D i j| +
          p49Gamma fp.u (n + 1) * S :=
        add_le_add
          (mul_le_mul_of_nonneg_right hstep.2 hD)
          (mul_le_mul_of_nonneg_right hstep.1 hS)
      _ = _ := by ring
  dsimp [p, S, r] at hbound
  simpa only [p49MatMul, p49RoundedSchur, p49RoundedMatMul, abs_mul] using hbound

private lemma p49_solve_block_error {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m) (V : P49Matrix n m)
    (u K₁ : ℝ) (hsolve : ∀ j : Fin m, ∃ EA : P49Matrix n n,
      (∀ i k, |EA i k| ≤ K₁ * u * |A i k|) ∧
      (∀ i, (∑ k : Fin n, (A i k + EA i k) * V k j) = B i j))
    (i : Fin n) (j : Fin m) :
    |p49MatMul A V i j - B i j| ≤
      (K₁ * u) * ∑ k : Fin n, |A i k| * |V k j| := by
  obtain ⟨EA, hEA, hsol⟩ := hsolve j
  have hsol' : (∑ k : Fin n, A i k * V k j) +
      (∑ k : Fin n, EA i k * V k j) = B i j := by
    simpa only [add_mul, ← Finset.sum_add_distrib] using hsol i
  have heq : p49MatMul A V i j - B i j =
      -(∑ k : Fin n, EA i k * V k j) := by
    dsimp [p49MatMul]
    linarith
  rw [heq, abs_neg]
  calc
    |∑ k : Fin n, EA i k * V k j| ≤
        ∑ k : Fin n, |EA i k * V k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, (K₁ * u * |A i k|) * |V k j| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hEA i k) (abs_nonneg _)
    _ = _ := by simp_rw [mul_assoc, ← Finset.mul_sum]

private lemma p49_block_mul_eq_computed {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m)
    (i j : P49BlockIndex n m) :
    p49BlockMatMul (p49LowerFactor A C) (p49UpperFactor V Delta) i j =
      p49ComputedBlockLU A C V Delta i j := by
  cases i <;> cases j <;>
    simp [p49BlockMatMul, p49LowerFactor, p49UpperFactor,
      p49ComputedBlockLU, p49BorderedMatrix, p49MatMul,
      Fintype.sum_sum_type, mul_ite]

private lemma p49_majorant_ul {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i j : Fin n) :
    p49FactorizationMajorant A B C D V (.inl i) (.inl j) = 0 := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix,
    Fintype.sum_sum_type]

private lemma p49_majorant_ur {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i : Fin n) (j : Fin m) :
    p49FactorizationMajorant A B C D V (.inl i) (.inr j) =
      (∑ k : Fin n, |A i k| * |V k j|) + |B i j| := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix,
    Fintype.sum_sum_type]

private lemma p49_majorant_ll {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i : Fin m) (j : Fin n) :
    p49FactorizationMajorant A B C D V (.inr i) (.inl j) = 0 := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix,
    Fintype.sum_sum_type]

private lemma p49_majorant_lr {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) (V : P49Matrix n m)
    (i j : Fin m) :
    p49FactorizationMajorant A B C D V (.inr i) (.inr j) =
      (∑ k : Fin n, |C i k| * |V k j|) + |D i j| := by
  simp [p49FactorizationMajorant, p49BlockMatMul, p49BorderedMatrix,
    Fintype.sum_sum_type]

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
  refine ⟨E, ?_, ?_⟩
  · intro i j
    rw [p49_block_mul_eq_computed]
    dsimp [E]
    ring
  · intro i j
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_ul]
        | inr j =>
            have hS : 0 ≤ ∑ k : Fin n, |A i k| * |V k j| :=
              Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hμ : K₁ * fp.u ≤ μ₁ := le_max_left _ _
            have hμnonneg : 0 ≤ μ₁ :=
              le_trans (mul_nonneg hK₁ fp.u_nonneg) hμ
            have hb := p49_solve_block_error A B V fp.u K₁ hsolve i j
            have hgoal : |p49MatMul A V i j - B i j| ≤
                μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) := by
              calc
                _ ≤ (K₁ * fp.u) * ∑ k : Fin n, |A i k| * |V k j| := hb
                _ ≤ μ₁ * ∑ k : Fin n, |A i k| * |V k j| :=
                  mul_le_mul_of_nonneg_right hμ hS
                _ ≤ μ₁ * ((∑ k : Fin n, |A i k| * |V k j|) + |B i j|) :=
                  mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_right (abs_nonneg _)) hμnonneg
            simpa only [E, p49ComputedBlockLU, p49BorderedMatrix,
              p49_majorant_ur] using hgoal
    | inr i =>
        cases j with
        | inl j =>
            simp [E, p49ComputedBlockLU, p49BorderedMatrix, p49_majorant_ll]
        | inr j =>
            have hS : 0 ≤ ∑ k : Fin n, |C i k| * |V k j| :=
              Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            have hγ : p49Gamma fp.u (n + 1) ≤ μ₁ := le_max_right _ _
            have hb := p49RoundedSchur_error fp C V D hvalid i j
            have hgoal : |p49MatMul C V i j + Delta i j - D i j| ≤
                μ₁ * ((∑ k : Fin n, |C i k| * |V k j|) + |D i j|) := by
              calc
                _ ≤ p49Gamma fp.u (n + 1) *
                    (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) := hb
                _ ≤ μ₁ * (|D i j| + ∑ k : Fin n, |C i k| * |V k j|) :=
                  mul_le_mul_of_nonneg_right hγ
                    (add_nonneg (abs_nonneg _) hS)
                _ = _ := by ring
            simpa only [E, p49ComputedBlockLU, p49BorderedMatrix,
              p49_majorant_lr] using hgoal

end VSCLReuse

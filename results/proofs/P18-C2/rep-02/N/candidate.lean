import VSCLReuse.P18.Definitions

namespace VSCLReuse


private lemma p18_gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P18GammaValid u (n + 1)) :
    u + (1 + u) * p18Gamma u n ≤ p18Gamma u (n + 1) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hden : 0 < 1 - (n : ℝ) * u := by
    unfold P18GammaValid at hv
    push_cast at hv
    nlinarith
  have hden' : 0 < 1 - ((n : ℝ) + 1) * u := by
    unfold P18GammaValid at hv
    push_cast at hv
    nlinarith
  have heq : u + (1 + u) * p18Gamma u n =
      (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    unfold p18Gamma
    have hd : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    field_simp [ne_of_gt hden, hd]
    ring
  rw [heq]
  unfold p18Gamma
  push_cast
  apply (div_le_div_iff₀ hden hden').2
  nlinarith [mul_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1) * u) hu]

private lemma p18_gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P18GammaValid u n) : 0 ≤ p18Gamma u n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 1 - (n : ℝ) * u := by
    unfold P18GammaValid at hv
    linarith
  unfold p18Gamma
  positivity

private lemma p18_u_le_gamma (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hn : 1 ≤ n) (hv : P18GammaValid u n) : u ≤ p18Gamma u n := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hd : 0 < 1 - (n : ℝ) * u := by
    unfold P18GammaValid at hv
    linarith
  unfold p18Gamma
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hn') hu, sq_nonneg ((n : ℝ) * u)]

private lemma p18_valid_prefix (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P18GammaValid u (n + 1)) : P18GammaValid u n := by
  unfold P18GammaValid at *
  push_cast at hv
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith

private noncomputable def p18FullDot (fp : P18FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0

private lemma p18_fullDot_eq (fp : P18FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p18RoundedDotProduct fp n x y = p18FullDot fp n x y := by
  cases n with
  | zero => simp [p18RoundedDotProduct, p18FullDot]
  | succ n =>
    simp [p18RoundedDotProduct, p18FullDot, Fin.foldl_succ, fp.fl_add_zero]

private lemma p18_mul_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hm⟩ := fp.model_mul x y
  rw [hm]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p18_add_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hm⟩ := fp.model_add x y
  rw [hm]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p18_sub_error (fp : P18FPModel) (x y : ℝ) :
    |fp.fl_sub x y - (x - y)| ≤ fp.u * |x - y| := by
  obtain ⟨δ, hδ, hm⟩ := fp.model_sub x y
  rw [hm]
  have heq : (x - y) * (1 + δ) - (x - y) = (x - y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x - y))

private lemma p18_dot_step_error (fp : P18FPModel) (a b x y : ℝ) :
    |fp.fl_add a (fp.fl_mul x y) - (b + x * y)| ≤
      (1 + fp.u) * |a - b| + fp.u * |b| +
        (2 * fp.u + fp.u * fp.u) * |x * y| := by
  let p := fp.fl_mul x y
  let t := x * y
  have hp : |p - t| ≤ fp.u * |t| := p18_mul_error fp x y
  have ha : |fp.fl_add a p - (a + p)| ≤ fp.u * |a + p| :=
    p18_add_error fp a p
  have hd : |(a + p) - (b + t)| ≤ |a - b| + fp.u * |t| := by
    calc
      |(a + p) - (b + t)| = |(a - b) + (p - t)| := by congr 1; ring
      _ ≤ |a - b| + |p - t| := abs_add_le _ _
      _ ≤ |a - b| + fp.u * |t| := by gcongr
  have hm : |a + p| ≤ |a - b| + |b| + |t| + fp.u * |t| := by
    have htri : |a + p| ≤ |(a + p) - (b + t)| + |b + t| := by
      calc
        |a + p| = |((a + p) - (b + t)) + (b + t)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have hbt : |b + t| ≤ |b| + |t| := abs_add_le _ _
    linarith
  calc
    |fp.fl_add a p - (b + t)| ≤
        |fp.fl_add a p - (a + p)| + |(a + p) - (b + t)| := abs_sub_le _ _ _
    _ ≤ fp.u * |a + p| + (|a - b| + fp.u * |t|) := add_le_add ha hd
    _ ≤ fp.u * (|a - b| + |b| + |t| + fp.u * |t|) +
        (|a - b| + fp.u * |t|) := by
          gcongr
          exact fp.u_nonneg
    _ = (1 + fp.u) * |a - b| + fp.u * |b| +
          (2 * fp.u + fp.u * fp.u) * |t| := by ring

private lemma p18_fullDot_error (fp : P18FPModel) :
    ∀ n : ℕ, P18GammaValid fp.u n → ∀ x y : Fin n → ℝ,
      |p18FullDot fp n x y - ∑ k : Fin n, x k * y k| ≤
        p18Gamma fp.u n * ∑ k : Fin n, |x k * y k| := by
  intro n
  induction n with
  | zero =>
    intro hv x y
    simp [p18FullDot, p18Gamma]
  | succ n ih =>
    intro hv x y
    cases n with
    | zero =>
      have hg : fp.u ≤ p18Gamma fp.u 1 :=
        p18_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hv
      simpa [p18FullDot, Fin.foldl_succ_last, fp.fl_add_zero,
        Fin.sum_univ_one] using
        (le_trans (p18_mul_error fp (x 0) (y 0))
          (mul_le_mul_of_nonneg_right hg (abs_nonneg (x 0 * y 0))))
    | succ n =>
      let N := n + 1
      let xp : Fin N → ℝ := fun k => x k.castSucc
      let yp : Fin N → ℝ := fun k => y k.castSucc
      let a := p18FullDot fp N xp yp
      let b := ∑ k : Fin N, xp k * yp k
      let S := ∑ k : Fin N, |xp k * yp k|
      let t := x (Fin.last N) * y (Fin.last N)
      have hvN : P18GammaValid fp.u N :=
        p18_valid_prefix fp.u N fp.u_nonneg hv
      have hih : |a - b| ≤ p18Gamma fp.u N * S := ih hvN xp yp
      have hsum : |b| ≤ S := by
        simpa [b, S] using
          (Finset.abs_sum_le_sum_abs (fun k : Fin N => xp k * yp k) Finset.univ)
      have hS : 0 ≤ S := Finset.sum_nonneg (fun k hk => abs_nonneg _)
      have hfold : p18FullDot fp (N + 1) x y =
          fp.fl_add a (fp.fl_mul (x (Fin.last N)) (y (Fin.last N))) := by
        simp [p18FullDot, Fin.foldl_succ_last, a, xp, yp]
      have hsum' : (∑ k : Fin (N + 1), x k * y k) = b + t := by
        simp [Fin.sum_univ_castSucc, b, t, xp, yp]
      have habssum : (∑ k : Fin (N + 1), |x k * y k|) = S + |t| := by
        simp [Fin.sum_univ_castSucc, S, t, xp, yp]
      have hgstep : fp.u + (1 + fp.u) * p18Gamma fp.u N ≤
          p18Gamma fp.u (N + 1) :=
        p18_gamma_step fp.u N fp.u_nonneg hv
      have hglow : fp.u ≤ p18Gamma fp.u N :=
        p18_u_le_gamma fp.u N fp.u_nonneg (by dsimp [N]; omega) hvN
      have hc : 2 * fp.u + fp.u * fp.u ≤ p18Gamma fp.u (N + 1) := by
        nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hglow)]
      have hstep := p18_dot_step_error fp a b (x (Fin.last N)) (y (Fin.last N))
      rw [hfold, hsum', habssum]
      calc
        |fp.fl_add a (fp.fl_mul (x (Fin.last N)) (y (Fin.last N))) -
            (b + t)| ≤
            (1 + fp.u) * |a - b| + fp.u * |b| +
              (2 * fp.u + fp.u * fp.u) * |t| := hstep
        _ ≤ (1 + fp.u) * (p18Gamma fp.u N * S) +
              fp.u * S + (2 * fp.u + fp.u * fp.u) * |t| := by
          gcongr <;> linarith [fp.u_nonneg]
        _ ≤ p18Gamma fp.u (N + 1) * S +
              p18Gamma fp.u (N + 1) * |t| := by
          have h1 := mul_le_mul_of_nonneg_right hgstep hS
          have h2 := mul_le_mul_of_nonneg_right hc (abs_nonneg t)
          nlinarith [h1, h2]
        _ = p18Gamma fp.u (N + 1) * (S + |t|) := by ring

/-- P18-C2: the first-step Schur-complement error calculation in Appendix B. -/
theorem p18_c2_first_schur_error
    (fp : P18FPModel) (m r : ℕ)
    (A22 : P18Matrix m m) (L11 : P18Matrix m r)
    (A12 : P18Matrix r m)
    (hvalid : P18GammaValid fp.u r) :
    ∀ i j,
      |p18RoundedSchur fp A22 L11 A12 i j -
          p18ExactSchur A22 L11 A12 i j| ≤
        p18SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P18-C2-H001
  intro i j
  let a := A22 i j
  let d := p18RoundedDotProduct fp r (L11 i) (fun k => A12 k j)
  let e := ∑ k : Fin r, L11 i k * A12 k j
  have hdot : |d - e| ≤
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| := by
    have h := p18_fullDot_error fp r hvalid (L11 i) (fun k => A12 k j)
    rw [← p18_fullDot_eq] at h
    simpa only [d, e, abs_mul] using h
  change |fp.fl_sub a d - (a - e)| ≤
    fp.u * |a - d| +
      p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j|
  calc
    |fp.fl_sub a d - (a - e)| ≤
        |fp.fl_sub a d - (a - d)| + |(a - d) - (a - e)| := abs_sub_le _ _ _
    _ = |fp.fl_sub a d - (a - d)| + |d - e| := by
      congr 1
      rw [show (a - d) - (a - e) = e - d by ring, abs_sub_comm]
    _ ≤ fp.u * |a - d| +
          p18Gamma fp.u r * ∑ k : Fin r, |L11 i k| * |A12 k j| :=
      add_le_add (p18_sub_error fp a d) hdot

end VSCLReuse

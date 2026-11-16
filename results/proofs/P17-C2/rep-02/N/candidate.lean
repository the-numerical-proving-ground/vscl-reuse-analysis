import VSCLReuse.P17.Definitions

namespace VSCLReuse

private theorem p17_gamma_step (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : P17GammaValid u (k + 1)) :
    (1 + u) * p17Gamma u k + u ≤ p17Gamma u (k + 1) := by
  have hk : 0 < 1 - (k : ℝ) * u := by
    unfold P17GammaValid at hv
    push_cast at hv
    nlinarith
  have hk1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold P17GammaValid at hv
    linarith
  unfold p17Gamma
  have heq : (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
      (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt hk)).2
    push_cast
    calc
      ((1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u) *
          (1 - (k : ℝ) * u) =
        (1 + u) * (((k : ℝ) * u / (1 - (k : ℝ) * u)) *
          (1 - (k : ℝ) * u)) + u * (1 - (k : ℝ) * u) := by ring
      _ = (1 + u) * ((k : ℝ) * u) + u * (1 - (k : ℝ) * u) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hk)]
      _ = ((k : ℝ) + 1) * u := by ring
  rw [heq]
  apply (div_le_div_iff₀ hk hk1).2
  have hnonneg : 0 ≤ (((k + 1 : ℕ) : ℝ) * u) * u := mul_nonneg (by positivity) hu
  push_cast at *
  nlinarith

private theorem p17_gamma_nonneg (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : P17GammaValid u k) : 0 ≤ p17Gamma u k := by
  unfold p17Gamma P17GammaValid at *
  exact div_nonneg (mul_nonneg (by positivity) hu) (by linarith)

private theorem p17_u_le_gamma (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hv : P17GammaValid u k) :
    u ≤ p17Gamma u k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hd : 0 < 1 - (k : ℝ) * u := by
    unfold P17GammaValid at hv
    linarith
  unfold p17Gamma
  apply (le_div_iff₀ hd).2
  have h1 : 0 ≤ ((k : ℝ) - 1) * u := mul_nonneg (by linarith) hu
  have h2 : 0 ≤ ((k : ℝ) * u) * u := mul_nonneg (mul_nonneg (by positivity) hu) hu
  nlinarith

private theorem p17_two_u_le_gamma (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hv : P17GammaValid u (k + 1)) :
    2 * u + u ^ 2 ≤ p17Gamma u (k + 1) := by
  have hkv : P17GammaValid u k := by
    unfold P17GammaValid at *
    have : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    nlinarith
  have h1 := p17_u_le_gamma u k hu hk hkv
  have h2 := p17_gamma_step u k hu hv
  have h3 : 0 ≤ (1 + u) * (p17Gamma u k - u) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

private theorem p17_fl_mul_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl, show x * y * (1 + δ) - x * y = (x * y) * δ by ring, abs_mul]
  rw [mul_comm fp.u]
  exact mul_le_mul_of_nonneg_left hδ (abs_nonneg _)

private theorem p17_fl_add_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl, show (x + y) * (1 + δ) - (x + y) = (x + y) * δ by ring, abs_mul]
  calc
    |x + y| * |δ| ≤ |x + y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ fp.u * (|x| + |y|) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (abs_add_le x y) fp.u_nonneg

private theorem p17_fl_step_error (fp : P17FPModel) (a s x y : ℝ) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      (1 + fp.u) * |a - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |x * y| := by
  let m := fp.fl_mul x y
  let t := x * y
  have hm : |m - t| ≤ fp.u * |t| := p17_fl_mul_error fp x y
  have had : |fp.fl_add a m - (a + m)| ≤ fp.u * (|a| + |m|) :=
    p17_fl_add_error fp a m
  have htri : |fp.fl_add a m - (s + t)| ≤
      |fp.fl_add a m - (a + m)| + |a - s| + |m - t| := by
    have heq : fp.fl_add a m - (s + t) =
        (fp.fl_add a m - (a + m)) + ((a - s) + (m - t)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans
      (by simpa only [add_assoc] using
        (add_le_add_right (abs_add_le (a - s) (m - t))
          |fp.fl_add a m - (a + m)|))
  have ha : |a| ≤ |a - s| + |s| := by
    simpa only [sub_add_cancel] using abs_add_le (a - s) s
  have hmt : |m| ≤ |m - t| + |t| := by
    simpa only [sub_add_cancel] using abs_add_le (m - t) t
  have hau := mul_le_mul_of_nonneg_left ha fp.u_nonneg
  have hmu := mul_le_mul_of_nonneg_left hmt fp.u_nonneg
  have hmmu := mul_le_mul_of_nonneg_left hm fp.u_nonneg
  dsimp [m, t] at *
  nlinarith

private theorem p17_rounded_fold_error (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P17GammaValid fp.u n) :
    |Fin.foldl n
        (fun a i => fp.fl_add a (fp.fl_mul (x i) (y i))) 0 -
      ∑ i : Fin n, x i * y i| ≤
      p17Gamma fp.u n * (∑ i : Fin n, |x i * y i|) := by
  induction n with
  | zero => simp [p17Gamma]
  | succ n ih =>
    let xs : Fin n → ℝ := fun i => x i.castSucc
    let ys : Fin n → ℝ := fun i => y i.castSucc
    let a : ℝ := Fin.foldl n
      (fun b i => fp.fl_add b (fp.fl_mul (xs i) (ys i))) 0
    let s : ℝ := ∑ i : Fin n, xs i * ys i
    let A : ℝ := ∑ i : Fin n, |xs i * ys i|
    let t : ℝ := x (Fin.last n) * y (Fin.last n)
    have hvprev : P17GammaValid fp.u n := by
      unfold P17GammaValid at *
      have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      nlinarith [fp.u_nonneg]
    have hprev : |a - s| ≤ p17Gamma fp.u n * A :=
      ih xs ys hvprev
    have hs : |s| ≤ A := by
      simpa [s, A, xs, ys] using
        (Finset.abs_sum_le_sum_abs (fun i : Fin n => xs i * ys i) Finset.univ)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i hi => abs_nonneg _)
    have ht : 0 ≤ |t| := abs_nonneg _
    have hfold : Fin.foldl (n + 1)
        (fun b i => fp.fl_add b (fp.fl_mul (x i) (y i))) 0 =
        fp.fl_add a (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
      rw [Fin.foldl_succ_last]
    have hsum : (∑ i : Fin (n + 1), x i * y i) = s + t := by
      rw [Fin.sum_univ_castSucc]
    have habs : (∑ i : Fin (n + 1), |x i * y i|) = A + |t| := by
      rw [Fin.sum_univ_castSucc]
    rw [hfold, hsum, habs]
    by_cases hn : n = 0
    · subst n
      have heq : a = 0 := by simp [a]
      have hse : s = 0 := by simp [s]
      have hAe : A = 0 := by simp [A]
      rw [heq, hse, hAe, fp.fl_add_zero]
      simp only [zero_add]
      have hmul := p17_fl_mul_error fp (x (Fin.last 0)) (y (Fin.last 0))
      have hgam := p17_u_le_gamma fp.u 1 fp.u_nonneg (by omega) hv
      exact hmul.trans (mul_le_mul_of_nonneg_right hgam ht)
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hstep := p17_fl_step_error fp a s
        (x (Fin.last n)) (y (Fin.last n))
      have hg := p17_gamma_step fp.u n fp.u_nonneg hv
      have hg2 := p17_two_u_le_gamma fp.u n fp.u_nonneg hn1 hv
      have h1 := mul_le_mul_of_nonneg_left hprev (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
      have h2 := mul_le_mul_of_nonneg_left hs fp.u_nonneg
      have h3 := mul_le_mul_of_nonneg_right hg hA
      have h4 := mul_le_mul_of_nonneg_right hg2 ht
      dsimp [t] at *
      nlinarith

private theorem p17_rounded_dot_eq_fold (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p17RoundedDotProduct fp n x y =
      Fin.foldl n (fun a i => fp.fl_add a (fp.fl_mul (x i) (y i))) 0 := by
  cases n with
  | zero => simp [p17RoundedDotProduct]
  | succ n =>
    rw [Fin.foldl_succ]
    simp only [p17RoundedDotProduct, fp.fl_add_zero]

private theorem p17_rounded_matmul_error (fp : P17FPModel) {n : ℕ}
    (A B : P17RealMatrix n) (hv : P17GammaValid fp.u n) (i j : Fin n) :
    |p17RoundedMatMul fp A B i j - p17MatMul A B i j| ≤
      p17Gamma fp.u n * (∑ k : Fin n, |A i k| * |B k j|) := by
  have h := p17_rounded_fold_error fp n (A i) (fun k => B k j) hv
  simpa only [p17RoundedMatMul, p17MatMul, p17_rounded_dot_eq_fold,
    abs_mul] using h

/-- P17-C2: the forward-error term from forming `XXᵀX` in equation (6.6). -/
theorem p17_c2_newton_schulz_triple_product_error
    (fp : P17FPModel) (n : ℕ) (X : P17RealMatrix n)
    (hvalid : P17GammaValid fp.u n) :
    ∀ i j,
      |p17RoundedGramTriple fp X i j - p17ExactGramTriple X i j| ≤
        p17GramTripleErrorMajorant fp X i j := by
  -- PROOF_START P17-C2-H001
  intro i j
  let R : P17RealMatrix n := p17RoundedMatMul fp X (p17Transpose X)
  let E : P17RealMatrix n := p17MatMul X (p17Transpose X)
  change |p17RoundedMatMul fp R X i j - p17MatMul E X i j| ≤
    p17Gamma fp.u n * (∑ k : Fin n, |R i k| * |X k j|) +
      p17Gamma fp.u n *
        (∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j|)
  have hsecond := p17_rounded_matmul_error fp R X hvalid i j
  have hfirst (k : Fin n) :
      |R i k - E i k| ≤
        p17Gamma fp.u n * (∑ l : Fin n, |X i l| * |X k l|) := by
    simpa only [R, E, p17Transpose] using
      (p17_rounded_matmul_error fp X (p17Transpose X) hvalid i k)
  have hdiff : p17MatMul R X i j - p17MatMul E X i j =
      ∑ k : Fin n, (R i k - E i k) * X k j := by
    simp only [p17MatMul, sub_mul, Finset.sum_sub_distrib]
  have habs : |p17MatMul R X i j - p17MatMul E X i j| ≤
      ∑ k : Fin n, |R i k - E i k| * |X k j| := by
    rw [hdiff]
    simpa only [abs_mul] using
      (Finset.abs_sum_le_sum_abs
        (fun k : Fin n => (R i k - E i k) * X k j) Finset.univ)
  have htransport : |p17MatMul R X i j - p17MatMul E X i j| ≤
      p17Gamma fp.u n *
        (∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
    calc
      _ ≤ ∑ k : Fin n, |R i k - E i k| * |X k j| := habs
      _ ≤ ∑ k : Fin n,
          (p17Gamma fp.u n * (∑ l : Fin n, |X i l| * |X k l|)) * |X k j| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hfirst k) (abs_nonneg _)
      _ = p17Gamma fp.u n *
          (∑ k : Fin n, (∑ l : Fin n, |X i l| * |X k l|) * |X k j|) := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have htri : |p17RoundedMatMul fp R X i j - p17MatMul E X i j| ≤
      |p17RoundedMatMul fp R X i j - p17MatMul R X i j| +
        |p17MatMul R X i j - p17MatMul E X i j| := by
    have heq : p17RoundedMatMul fp R X i j - p17MatMul E X i j =
        (p17RoundedMatMul fp R X i j - p17MatMul R X i j) +
          (p17MatMul R X i j - p17MatMul E X i j) := by ring
    rw [heq]
    exact abs_add_le _ _
  exact htri.trans (add_le_add hsecond htransport)

end VSCLReuse

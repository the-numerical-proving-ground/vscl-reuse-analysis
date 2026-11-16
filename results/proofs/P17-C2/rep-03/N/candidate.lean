import VSCLReuse.P17.Definitions

namespace VSCLReuse

private theorem p17_mul_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hm⟩ := fp.model_mul x y
  rw [hm]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private theorem p17_add_error (fp : P17FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, ha⟩ := fp.model_add x y
  rw [ha]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private theorem p17_round_step (fp : P17FPModel) (a s t : ℝ)
    (m : ℝ) (hm : |m - t| ≤ fp.u * |t|) :
    |fp.fl_add a m - (s + t)| ≤
      (1 + fp.u) * |a - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |t| := by
  have ha := p17_add_error fp a m
  have hsplit : |fp.fl_add a m - (s + t)| ≤
      |fp.fl_add a m - (a + m)| + |a - s| + |m - t| := by
    have heq : fp.fl_add a m - (s + t) =
        (fp.fl_add a m - (a + m)) + (a - s) + (m - t) := by ring
    rw [heq]
    linarith [abs_add_le (fp.fl_add a m - (a + m)) (a - s),
      abs_add_le ((fp.fl_add a m - (a + m)) + (a - s)) (m - t)]
  have harg : |a + m| ≤ |a - s| + |s| + |m - t| + |t| := by
    have heq : a + m = (a - s) + s + (m - t) + t := by ring
    rw [heq]
    linarith [abs_add_le (a - s) s,
      abs_add_le ((a - s) + s) (m - t),
      abs_add_le (((a - s) + s) + (m - t)) t]
  have harg' := mul_le_mul_of_nonneg_left harg fp.u_nonneg
  have hm' := mul_le_mul_of_nonneg_left hm fp.u_nonneg
  nlinarith

private theorem p17_gamma_step_raw (u a : ℝ) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hvalid : a + u < 1) :
    (1 + u) * (a / (1 - a)) + u ≤
      (a + u) / (1 - (a + u)) := by
  have hd : 0 < 1 - a := by linarith
  have he : 0 < 1 - (a + u) := by linarith
  have hdiff :
      (a + u) / (1 - (a + u)) - ((1 + u) * (a / (1 - a)) + u) =
        u * (a + u) / ((1 - a) * (1 - (a + u))) := by
    field_simp
    ring
  rw [← sub_nonneg, hdiff]
  exact div_nonneg (mul_nonneg hu (by linarith))
    (mul_nonneg (le_of_lt hd) (le_of_lt he))

private theorem p17_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hvalid : P17GammaValid u (k + 1)) :
    (1 + u) * p17Gamma u k + u ≤ p17Gamma u (k + 1) := by
  unfold p17Gamma P17GammaValid at *
  push_cast at *
  have ha : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have := p17_gamma_step_raw u ((k : ℝ) * u) hu ha (by nlinarith [hvalid])
  simpa only [add_mul, one_mul] using this

private theorem p17_gamma_ge_u (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P17GammaValid u k) :
    u ≤ p17Gamma u k := by
  unfold p17Gamma P17GammaValid at *
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ha : u ≤ (k : ℝ) * u := by nlinarith
  have hb : 0 ≤ (k : ℝ) * u := by nlinarith
  have hd : 0 < 1 - (k : ℝ) * u := by linarith
  apply (le_div_iff₀ hd).2
  nlinarith

private theorem p17_gamma_step_term (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P17GammaValid u (k + 1)) :
    2 * u + u ^ 2 ≤ p17Gamma u (k + 1) := by
  have hvalid_k : P17GammaValid u k := by
    unfold P17GammaValid at *
    have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ k)
    nlinarith
  have hg := p17_gamma_ge_u u k hu hk hvalid_k
  have hs := p17_gamma_step u k hu hvalid
  have hm := mul_le_mul_of_nonneg_left hg (by linarith : 0 ≤ 1 + u)
  nlinarith

private theorem p17_fold_error (fp : P17FPModel) :
    ∀ (n : ℕ) (t m : Fin n → ℝ),
      (∀ i, |m i - t i| ≤ fp.u * |t i|) →
      P17GammaValid fp.u n →
      |Fin.foldl n (fun acc i => fp.fl_add acc (m i)) 0 - ∑ i, t i| ≤
        p17Gamma fp.u n * ∑ i, |t i| := by
  intro n
  induction n with
  | zero =>
      intro t m hm hv
      simp [Fin.foldl_zero]
  | succ n ih =>
      intro t m hm hv
      by_cases hn : n = 0
      · subst n
        have hg : fp.u ≤ p17Gamma fp.u 1 :=
          p17_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hv
        have ht := hm (Fin.last 0)
        have hmul := mul_le_mul_of_nonneg_right hg (abs_nonneg (t (Fin.last 0)))
        simpa [Fin.foldl_succ_last, Fin.sum_univ_castSucc, fp.fl_add_zero]
          using le_trans ht hmul
      · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hvn : P17GammaValid fp.u n := by
          unfold P17GammaValid at *
          have hc : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ n)
          nlinarith [fp.u_nonneg]
        let a : ℝ := Fin.foldl n
          (fun acc i => fp.fl_add acc (m i.castSucc)) 0
        let s : ℝ := ∑ i : Fin n, t i.castSucc
        let v : ℝ := t (Fin.last n)
        let M : ℝ := m (Fin.last n)
        let S : ℝ := ∑ i : Fin n, |t i.castSucc|
        have hi : |a - s| ≤ p17Gamma fp.u n * S := by
          exact ih (fun i => t i.castSucc) (fun i => m i.castSucc)
            (fun i => hm i.castSucc) hvn
        have hs : |s| ≤ S := by
          simpa [s, S] using
            (Finset.abs_sum_le_sum_abs (fun i : Fin n => t i.castSucc) Finset.univ)
        have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        have hr := p17_round_step fp a s v M (hm (Fin.last n))
        have h1 := mul_le_mul_of_nonneg_left hi
          (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
        have h2 := mul_le_mul_of_nonneg_left hs fp.u_nonneg
        have hg := p17_gamma_step fp.u n fp.u_nonneg hv
        have hgS := mul_le_mul_of_nonneg_right hg hS
        have hgt := p17_gamma_step_term fp.u n fp.u_nonneg hn' hv
        have hgtv := mul_le_mul_of_nonneg_right hgt (abs_nonneg v)
        rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
          Fin.sum_univ_castSucc]
        change |fp.fl_add a M - (s + v)| ≤
          p17Gamma fp.u (n + 1) * (S + |v|)
        nlinarith

private theorem p17_rounded_dot_eq_fold (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p17RoundedDotProduct fp n x y =
      Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 := by
  cases n with
  | zero => simp [p17RoundedDotProduct]
  | succ n =>
      rw [Fin.foldl_succ]
      simp [p17RoundedDotProduct, fp.fl_add_zero]

private theorem p17_dot_error (fp : P17FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P17GammaValid fp.u n) :
    |p17RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p17Gamma fp.u n * ∑ i, |x i| * |y i| := by
  rw [p17_rounded_dot_eq_fold]
  simpa only [abs_mul] using
    p17_fold_error fp n (fun i => x i * y i)
      (fun i => fp.fl_mul (x i) (y i))
      (fun i => p17_mul_error fp (x i) (y i)) hvalid

private theorem p17_matmul_error (fp : P17FPModel) (n : ℕ)
    (A B : P17RealMatrix n) (hvalid : P17GammaValid fp.u n)
    (i j : Fin n) :
    |p17RoundedMatMul fp A B i j - p17MatMul A B i j| ≤
      p17Gamma fp.u n * ∑ k, |A i k| * |B k j| := by
  exact p17_dot_error fp n (A i) (fun k => B k j) hvalid

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
  have houter :
      |p17RoundedMatMul fp R X i j - p17MatMul R X i j| ≤
        p17Gamma fp.u n * ∑ k, |R i k| * |X k j| :=
    p17_matmul_error fp n R X hvalid i j
  have hinner (k : Fin n) :
      |R i k - E i k| ≤
        p17Gamma fp.u n * ∑ l, |X i l| * |X k l| := by
    simpa [R, E, p17Transpose] using
      (p17_matmul_error fp n X (p17Transpose X) hvalid i k)
  have htransport :
      |p17MatMul R X i j - p17MatMul E X i j| ≤
        p17Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
    change |(∑ k, R i k * X k j) - (∑ k, E i k * X k j)| ≤ _
    have heq :
        (∑ k, R i k * X k j) - (∑ k, E i k * X k j) =
          ∑ k, (R i k - E i k) * X k j := by
      simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ k, (R i k - E i k) * X k j| ≤
          ∑ k, |(R i k - E i k) * X k j| := by
            simpa using (Finset.abs_sum_le_sum_abs
              (fun k : Fin n => (R i k - E i k) * X k j) Finset.univ)
      _ = ∑ k, |R i k - E i k| * |X k j| := by simp_rw [abs_mul]
      _ ≤ ∑ k, (p17Gamma fp.u n *
          (∑ l, |X i l| * |X k l|)) * |X k j| := by
            apply Finset.sum_le_sum
            intro k hk
            exact mul_le_mul_of_nonneg_right (hinner k) (abs_nonneg _)
      _ = p17Gamma fp.u n *
          ∑ k, (∑ l, |X i l| * |X k l|) * |X k j| := by
            rw [Finset.mul_sum]
            simp_rw [mul_assoc]
  change |p17RoundedMatMul fp R X i j - p17MatMul E X i j| ≤ _
  have htriangle :
      |p17RoundedMatMul fp R X i j - p17MatMul E X i j| ≤
        |p17RoundedMatMul fp R X i j - p17MatMul R X i j| +
        |p17MatMul R X i j - p17MatMul E X i j| := by
    have heq : p17RoundedMatMul fp R X i j - p17MatMul E X i j =
        (p17RoundedMatMul fp R X i j - p17MatMul R X i j) +
        (p17MatMul R X i j - p17MatMul E X i j) := by ring
    rw [heq]
    exact abs_add_le _ _
  unfold p17GramTripleErrorMajorant
  exact htriangle.trans (add_le_add houter htransport)

end VSCLReuse

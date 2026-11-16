import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius
set_option maxHeartbeats 2000000

private lemma p08_frob_eq_norm {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = ‖M‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]

private lemma p08_frob_eq_norm_sq {n : ℕ} (M : P08Matrix n) :
    p08FrobNorm M = ‖M‖ := p08_frob_eq_norm M

private lemma p08_frob_nonneg {m n : ℕ} (M : P08RectMatrix m n) :
    0 ≤ p08RectFrobNorm M := by rw [p08_frob_eq_norm]; exact norm_nonneg _

private lemma p08_frob_add_le {n : ℕ} (M N : P08Matrix n) :
    p08FrobNorm (p08RectAdd M N) ≤ p08FrobNorm M + p08FrobNorm N := by
  simp only [p08_frob_eq_norm_sq]
  have h : p08RectAdd M N = M + N := by ext i j; rfl
  rw [h]
  exact norm_add_le _ _

private lemma p08_gamma_mono (u a c : ℝ) (hu : 0 ≤ u)
    (hac : a ≤ c) (ha : 0 ≤ a) (hc : c * u < 1) :
    p08GammaReal a u ≤ p08GammaReal c u := by
  have h1 : 0 < 1 - a * u := by nlinarith [mul_le_mul_of_nonneg_right hac hu]
  have h2 : 0 < 1 - c * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ h1 h2).2
  nlinarith [mul_le_mul_of_nonneg_right hac hu]

private lemma p08_gamma_nonneg (u c : ℝ) (hu : 0 ≤ u)
    (hc : 0 ≤ c) (hvalid : c * u < 1) :
    0 ≤ p08GammaReal c u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hc hu) (by linarith)

private lemma p08_gamma_step (u k : ℝ) (hu : 0 ≤ u)
    (hk : 0 ≤ k) (hvalid : (k + 1) * u < 1) :
    (1 + u) * p08GammaReal k u + u ≤
      p08GammaReal (k + 1) u := by
  have hd1 : 0 < 1 - k * u := by nlinarith
  have hd2 : 0 < 1 - (k + 1) * u := by linarith
  unfold p08GammaReal
  calc
    (1 + u) * (k * u / (1 - k * u)) + u = (k + 1) * u / (1 - k * u) := by
      apply (eq_div_iff (ne_of_gt hd1)).2
      calc
        ((1 + u) * (k * u / (1 - k * u)) + u) * (1 - k * u) =
            (1 + u) * ((k * u / (1 - k * u)) * (1 - k * u)) + u * (1 - k * u) := by ring
        _ = (k + 1) * u := by rw [div_mul_cancel₀ _ (ne_of_gt hd1)]; ring
    _ ≤ (k + 1) * u / (1 - (k + 1) * u) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      nlinarith [mul_nonneg (add_nonneg hk zero_le_one) hu]

private lemma p08_gamma_two (u k : ℝ) (hu : 0 ≤ u)
    (hk : 2 ≤ k) (hvalid : k * u < 1) :
    2 * u + u ^ 2 ≤ p08GammaReal k u := by
  have h2 : 2 * u < 1 := by nlinarith [mul_le_mul_of_nonneg_right hk hu]
  have hm : p08GammaReal 2 u ≤ p08GammaReal k u :=
    p08_gamma_mono u 2 k hu hk (by norm_num) hvalid
  have hbase : 2 * u + u ^ 2 ≤ p08GammaReal 2 u := by
    unfold p08GammaReal
    apply (le_div_iff₀ (by linarith : 0 < 1 - 2 * u)).2
    nlinarith [sq_nonneg u]
  linarith

private lemma p08_gamma_one (u : ℝ) (hu : 0 ≤ u) (hvalid : u < 1) :
    u ≤ p08GammaReal 1 u := by
  unfold p08GammaReal
  norm_num
  apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
  nlinarith [sq_nonneg u]

private lemma p08_fl_mul_error (fp : StandardFPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have h : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p08_fl_add_error (fp : StandardFPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have h : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p08_dot_succ_succ (fp : StandardFPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    roundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (roundedDotProduct fp (n + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  change Fin.foldl (n + 1)
      (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
      (fp.fl_mul (x 0) (y 0)) = _
  rw [Fin.foldl_succ_last]
  simp only [roundedDotProduct]
  rfl

private lemma p08_dot_step_bound (fp : StandardFPModel)
    (a s m t S g : ℝ)
    (hS : |s| ≤ S) (ha : |a - s| ≤ g * S)
    (hm : |m - t| ≤ fp.u * |t|)
    (hadd : |fp.fl_add a m - (a + m)| ≤ fp.u * |a + m|) :
    |fp.fl_add a m - (s + t)| ≤
      ((1 + fp.u) * g + fp.u) * S + (2 * fp.u + fp.u ^ 2) * |t| := by
  have ha' : |a| ≤ |a - s| + |s| := by
    calc
      |a| = |(a - s) + s| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hm' : |m| ≤ |m - t| + |t| := by
    calc
      |m| = |(m - t) + t| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have ham : |a + m| ≤ |a - s| + |s| + |m - t| + |t| := by
    linarith [abs_add_le a m]
  have ham' : |a + m| ≤ g * S + S + fp.u * |t| + |t| := by linarith
  have hmul := mul_le_mul_of_nonneg_left ham' fp.u_nonneg
  have hres : |(a + m) - (s + t)| ≤ |a - s| + |m - t| := by
    calc
      |(a + m) - (s + t)| = |(a - s) + (m - t)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have htri := abs_sub_le (fp.fl_add a m) (a + m) (s + t)
  nlinarith

private lemma p08_dot_forward (fp : StandardFPModel) :
    ∀ n : ℕ, ∀ x y : Fin n → ℝ, (n : ℝ) * fp.u < 1 →
      |roundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
        p08GammaReal (n : ℝ) fp.u * ∑ i : Fin n, |x i * y i| := by
  intro n
  induction n with
  | zero =>
      intro x y hn
      simp [roundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          intro x y hn
          have hmul := p08_fl_mul_error fp (x 0) (y 0)
          have hγ : fp.u ≤ p08GammaReal 1 fp.u :=
            p08_gamma_one fp.u fp.u_nonneg (by simpa using hn)
          have hnonneg : 0 ≤ |x 0 * y 0| := abs_nonneg _
          have hbound := mul_le_mul_of_nonneg_right hγ hnonneg
          simpa [roundedDotProduct, Fin.foldl_zero, Fin.sum_univ_succ] using
            le_trans hmul hbound
      | succ n =>
          intro x y hn
          let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
          let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
          let s : ℝ := ∑ i : Fin (n + 1), x' i * y' i
          let S : ℝ := ∑ i : Fin (n + 1), |x' i * y' i|
          let t : ℝ := x (Fin.last (n + 1)) * y (Fin.last (n + 1))
          let a : ℝ := roundedDotProduct fp (n + 1) x' y'
          let m : ℝ := fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
          have hprefix : ((n + 1 : ℕ) : ℝ) * fp.u < 1 := by
            have hnonneg := fp.u_nonneg
            push_cast at hn ⊢
            nlinarith
          have ha : |a - s| ≤ p08GammaReal (n + 1 : ℝ) fp.u * S :=
            by simpa only [a, s, S, Nat.cast_add, Nat.cast_one] using ih x' y' hprefix
          have hs : |s| ≤ S := by
            simpa [s, S, x', y'] using
              (Finset.abs_sum_le_sum_abs (fun i : Fin (n + 1) => x i.castSucc * y i.castSucc) Finset.univ)
          have hm : |m - t| ≤ fp.u * |t| := p08_fl_mul_error fp _ _
          have hstep := p08_dot_step_bound fp a s m t S
            (p08GammaReal (n + 1 : ℝ) fp.u) hs ha hm (p08_fl_add_error fp a m)
          have hSn : 0 ≤ S := Finset.sum_nonneg (fun i hi => abs_nonneg _)
          have hγstep :
              (1 + fp.u) * p08GammaReal (n + 1 : ℝ) fp.u + fp.u ≤
                p08GammaReal (n + 2 : ℝ) fp.u := by
            convert p08_gamma_step fp.u (n + 1 : ℝ) fp.u_nonneg
              (by positivity) (by simpa [Nat.cast_add] using hn) using 1 <;> push_cast <;> ring
          have hγtwo : 2 * fp.u + fp.u ^ 2 ≤ p08GammaReal (n + 2 : ℝ) fp.u :=
            p08_gamma_two fp.u (n + 2 : ℝ) fp.u_nonneg
              (by exact_mod_cast (show (2 : ℕ) ≤ n + 2 by omega))
              (by convert hn using 1 <;> push_cast <;> ring)
          have hbound :
              ((1 + fp.u) * p08GammaReal (n + 1 : ℝ) fp.u + fp.u) * S +
                  (2 * fp.u + fp.u ^ 2) * |t| ≤
                p08GammaReal (n + 2 : ℝ) fp.u * (S + |t|) := by
            nlinarith [mul_le_mul_of_nonneg_right hγstep hSn,
              mul_le_mul_of_nonneg_right hγtwo (abs_nonneg t)]
          have h := le_trans hstep hbound
          rw [p08_dot_succ_succ]
          rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => x i * y i)]
          rw [Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |x i * y i|)]
          convert h using 1 <;> simp only [a, s, S, t, m, x', y', Nat.cast_add, Nat.cast_one] <;> ring

private def p08Col {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin 1) ℝ :=
  fun i _ => x i

private lemma p08_col_norm_sq {n : ℕ} (x : Fin n → ℝ) :
    ‖p08Col x‖ ^ 2 = ∑ i : Fin n, x i ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [p08Col, Fin.sum_univ_one, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg _)

private lemma p08_col_norm_abs {n : ℕ} (x : Fin n → ℝ) :
    ‖p08Col (fun i => |x i|)‖ = ‖p08Col x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [p08_col_norm_sq, sq_abs]

private lemma p08_matrix_norm_abs {m n : ℕ} (M : P08RectMatrix m n) :
    ‖M.map abs‖ = ‖M‖ := by
  exact Matrix.frobenius_norm_map_eq M abs (by intro a; simp)

private lemma p08_matrix_norm_mono {m n : ℕ} (M N : P08RectMatrix m n)
    (h : ∀ i j, |M i j| ≤ |N i j|) : ‖M‖ ≤ ‖N‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two]
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _)
    ?_ (by norm_num)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact pow_le_pow_left₀ (abs_nonneg _) (h i j) 2

private lemma p08_rect_mul_col {m n : ℕ}
    (M : P08RectMatrix m n) (x : Fin n → ℝ) (i : Fin m) :
    (M * p08Col x) i 0 = p08RectMatVec M x i := by
  simp only [Matrix.mul_apply, p08Col, p08RectMatVec]

private lemma p08_matvec_forward (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hn : (n : ℝ) * fp.u < 1) :
    ‖p08Col (fun i => p08RoundedRectMatVec fp A x i - p08RectMatVec A x i)‖ ≤
      p08GammaReal (n : ℝ) fp.u * ‖A‖ * ‖p08Col x‖ := by
  let γ := p08GammaReal (n : ℝ) fp.u
  let B := A.map abs
  let w := p08Col (fun j => |x j|)
  let P := B * w
  let e := p08Col (fun i => p08RoundedRectMatVec fp A x i - p08RectMatVec A x i)
  have hγ : 0 ≤ γ := p08_gamma_nonneg fp.u n fp.u_nonneg (by positivity) hn
  have hentry (i : Fin m) : |e i 0| ≤ |(γ • P) i 0| := by
    have hd := p08_dot_forward fp n (A i) x hn
    have hP : P i 0 = ∑ j : Fin n, |A i j * x j| := by
      simp only [P, B, w, Matrix.mul_apply, Matrix.map_apply, p08Col, abs_mul]
    have hPnonneg : 0 ≤ P i 0 := by rw [hP]; exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    change |p08RoundedRectMatVec fp A x i - p08RectMatVec A x i| ≤ |γ * P i 0|
    rw [abs_mul, abs_of_nonneg hγ, abs_of_nonneg hPnonneg, hP]
    simpa only [p08RoundedRectMatVec, roundedMatVec, p08RectMatVec, γ] using hd
  have hnorm : ‖e‖ ≤ ‖γ • P‖ := by
    apply p08_matrix_norm_mono
    intro i j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    exact hentry i
  have hPbound : ‖P‖ ≤ ‖A‖ * ‖p08Col x‖ := by
    calc
      ‖P‖ ≤ ‖B‖ * ‖w‖ := Matrix.frobenius_norm_mul B w
      _ = ‖A‖ * ‖p08Col x‖ := by rw [p08_matrix_norm_abs, p08_col_norm_abs]
  change ‖e‖ ≤ γ * ‖A‖ * ‖p08Col x‖
  calc
    ‖e‖ ≤ ‖γ • P‖ := hnorm
    _ = γ * ‖P‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
    _ ≤ γ * (‖A‖ * ‖p08Col x‖) := mul_le_mul_of_nonneg_left hPbound hγ
    _ = γ * ‖A‖ * ‖p08Col x‖ := by ring

private lemma p08_outer_apply {m n : ℕ} (e : Fin m → ℝ) (x : Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    (p08Col e * (p08Col x).transpose) i j = e i * x j := by
  simp [Matrix.mul_apply, p08Col]

private lemma p08_backward_of_forward {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hforward :
      ‖p08Col (fun i => y i - p08RectMatVec A x i)‖ ≤
        C * ‖A‖ * ‖p08Col x‖) :
    ∃ E : P08RectMatrix m n,
      y = p08RectMatVec (p08RectAdd A E) x ∧ ‖E‖ ≤ C * ‖A‖ := by
  let e : Fin m → ℝ := fun i => y i - p08RectMatVec A x i
  let s : ℝ := ∑ j : Fin n, x j ^ 2
  have hs : s = ‖p08Col x‖ ^ 2 := (p08_col_norm_sq x).symm
  by_cases hx : ‖p08Col x‖ = 0
  · have hx0 : x = 0 := by
      have hcol : p08Col x = 0 := (norm_eq_zero).mp hx
      funext j
      have hj := congrArg (fun M : Matrix (Fin n) (Fin 1) ℝ => M j 0) hcol
      simpa [p08Col] using hj
    have he : p08Col e = 0 := by
      apply (norm_eq_zero).mp
      have hh : ‖p08Col e‖ ≤ 0 := by simpa [e, hx] using hforward
      exact le_antisymm hh (norm_nonneg _)
    refine ⟨0, ?_, ?_⟩
    · funext i
      have hi := congrArg (fun M : Matrix (Fin m) (Fin 1) ℝ => M i 0) he
      have hie : e i = 0 := by simpa [p08Col] using hi
      simp only [e] at hie
      simp [p08RectMatVec, p08RectAdd, hx0] at hie ⊢
      exact hie
    · simp [hC, mul_nonneg]
  · have hspos : 0 < s := by rw [hs]; positivity
    let E : P08RectMatrix m n := (1 / s) • (p08Col e * (p08Col x).transpose)
    have hE (i : Fin m) (j : Fin n) : E i j = e i * x j / s := by
      simp only [E, Matrix.smul_apply, smul_eq_mul, p08_outer_apply, one_div, div_eq_mul_inv]
      ring
    have hEv (i : Fin m) : p08RectMatVec E x i = e i := by
      simp only [p08RectMatVec, hE]
      have hsum : (∑ j : Fin n, (e i * x j / s) * x j) = e i * s / s := by
        calc
          (∑ j : Fin n, (e i * x j / s) * x j) =
              ∑ j : Fin n, e i * (x j ^ 2) / s := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = e i * s / s := by rw [← Finset.sum_div]; simp [s, Finset.mul_sum]
      rw [hsum]
      simp [ne_of_gt hspos]
    refine ⟨E, ?_, ?_⟩
    · funext i
      calc
        y i = p08RectMatVec A x i + e i := by dsimp [e]; ring
        _ = p08RectMatVec A x i + p08RectMatVec E x i := by rw [hEv]
        _ = p08RectMatVec (p08RectAdd A E) x i := by
          simp only [p08RectMatVec, p08RectAdd, add_mul, Finset.sum_add_distrib]
    · have hxn : 0 < ‖p08Col x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      have hEn : ‖E‖ ≤ ‖p08Col e‖ / ‖p08Col x‖ := by
        calc
          ‖E‖ = (1 / s) * ‖p08Col e * (p08Col x).transpose‖ := by
            simp [E, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hspos)]
          _ ≤ (1 / s) * (‖p08Col e‖ * ‖(p08Col x).transpose‖) :=
            mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul _ _) (by positivity)
          _ = ‖p08Col e‖ / ‖p08Col x‖ := by
            rw [Matrix.frobenius_norm_transpose, hs]
            field_simp
      exact le_trans hEn ((div_le_iff₀ hxn).2 (by simpa [e, mul_assoc] using hforward))

private lemma p08_rounded_stage (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hn : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      p08RoundedRectMatVec fp A x = p08RectMatVec (p08RectAdd A E) x ∧
      ‖E‖ ≤ p08GammaReal (n : ℝ) fp.u * ‖A‖ := by
  exact p08_backward_of_forward A x (p08RoundedRectMatVec fp A x)
    (p08GammaReal (n : ℝ) fp.u)
    (p08_gamma_nonneg fp.u n fp.u_nonneg (by positivity) hn)
    (p08_matvec_forward fp A x hn)

private lemma p08_norm_sq_trace {m n : ℕ} (M : P08RectMatrix m n) :
    ‖M‖ ^ 2 = ∑ j : Fin n, (M.transpose * M) j j := by
  rw [Matrix.frobenius_norm_def]
  rw [← Real.sqrt_eq_rpow]
  have hn : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, ‖M i j‖ ^ (2 : ℝ) := by
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => by positivity
  rw [Real.sq_sqrt hn]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, Real.rpow_two, sq_abs, pow_two]
  rw [Finset.sum_comm]
  simp only [← pow_two, sq_abs]

private lemma p08_orthonormal_transpose_mul {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    X.transpose * X = 1 := by
  ext j k
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hX j k

private lemma p08_orthonormal_mul_norm {b r p : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (B : P08RectMatrix r p) : ‖X * B‖ = ‖B‖ := by
  have hXT := p08_orthonormal_transpose_mul X hX
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [p08_norm_sq_trace (X * B), p08_norm_sq_trace B]
  congr 1
  ext j
  calc
    ((X * B).transpose * (X * B)) j j =
        ((B.transpose * X.transpose) * (X * B)) j j := by rw [Matrix.transpose_mul]
    _ = (B.transpose * ((X.transpose * X) * B)) j j := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc X.transpose X B]
    _ = (B.transpose * B) j j := by rw [hXT, Matrix.one_mul]

private lemma p08_orthonormal_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖X‖ = Real.sqrt (r : ℝ) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [p08_norm_sq_trace, p08_orthonormal_transpose_mul X hX,
    Real.sq_sqrt (Nat.cast_nonneg r)]
  simp

private lemma p08_lowrank_norm {b r : ℕ}
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖p08LowRankMatrix X Y‖ = ‖Y‖ := by
  change ‖X * Y.transpose‖ = ‖Y‖
  rw [p08_orthonormal_mul_norm X hX, Matrix.frobenius_norm_transpose]

private lemma p08_r_le_rsqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => norm_num
  | succ r =>
      have hr : (1 : ℝ) ≤ Real.sqrt (r + 1 : ℝ) := by
        simpa using Real.sqrt_le_sqrt
          (show (1 : ℝ) ≤ (r + 1 : ℝ) by positivity)
      have h := mul_le_mul_of_nonneg_left hr (show 0 ≤ (r + 1 : ℝ) by positivity)
      simpa [Nat.cast_add, mul_comm] using h

private lemma p08_gamma_combine_aux (a d q : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (hqd : q ≤ d) (hvalid : a + d < 1) :
    a / (1 - a) + d / (1 - q) +
        a / (1 - a) * (d / (1 - q)) ≤
      (a + d) / (1 - a - d) := by
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 - q := by linarith
  have h3 : 0 < 1 - a - d := by linarith
  have heq : a / (1 - a) + d / (1 - q) +
      a / (1 - a) * (d / (1 - q)) =
      (a + d - a * q) / ((1 - a) * (1 - q)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
    ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos h1 h2) h3).2
  nlinarith [mul_nonneg (add_nonneg ha hd) (sub_nonneg.mpr hqd), mul_nonneg ha hq]

private lemma p08_gamma_combine (b r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (b : ℝ) u +
      p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) +
      p08GammaReal (b : ℝ) u *
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) u := by
  let a := (b : ℝ) * u
  let d := (r : ℝ) * Real.sqrt (r : ℝ) * u
  let q := (r : ℝ) * u
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqd : q ≤ d := by
    dsimp [q, d]
    exact mul_le_mul_of_nonneg_right (p08_r_le_rsqrt r) hu
  have hav : a + d < 1 := by dsimp [a, d]; nlinarith [hvalid]
  have h := p08_gamma_combine_aux a d q ha hd hq hqd hav
  convert h using 1 <;> dsimp [a, d, q, p08GammaReal] <;> ring

private lemma p08_col_matvec {m n : ℕ}
    (M : P08RectMatrix m n) (x : Fin n → ℝ) :
    p08Col (p08RectMatVec M x) = M * p08Col x := by
  ext i j
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  exact (p08_rect_mul_col M x i).symm

private lemma p08_col_lowrank_matvec {b r : ℕ}
    (X Y : P08RectMatrix b r) (v : P08Vector b) :
    p08Col (p08MatVec (p08LowRankMatrix X Y) v) =
      X * (Y.transpose * p08Col v) := by
  have hL : p08LowRankMatrix X Y = X * Y.transpose := by
    ext i j
    rfl
  rw [hL]
  change p08Col (p08RectMatVec (X * Y.transpose) v) = _
  rw [p08_col_matvec, Matrix.mul_assoc]

private lemma p08_lowrank_forward (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (v : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ‖p08Col (fun i => p08RoundedLowRankMatVec fp X Y v i -
        p08MatVec (p08LowRankMatrix X Y) v i)‖ ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
        ‖p08LowRankMatrix X Y‖ * ‖p08Col v‖ := by
  let T := Y.transpose
  let w := p08RectMatVec T v
  let wh := p08RoundedRectMatVec fp T v
  let z := p08RoundedRectMatVec fp X wh
  let e1 := p08Col (fun j => wh j - w j)
  let e2 := p08Col (fun i => z i - p08RectMatVec X wh i)
  let et := p08Col (fun i => z i - p08MatVec (p08LowRankMatrix X Y) v i)
  let γb := p08GammaReal (b : ℝ) fp.u
  let γr := p08GammaReal (r : ℝ) fp.u
  let γc := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  have hb : (b : ℝ) * fp.u < 1 := by
    have hterm : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) * fp.u :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) fp.u_nonneg
    nlinarith [hvalid]
  have hr : (r : ℝ) * fp.u < 1 := by
    have hle := mul_le_mul_of_nonneg_right (p08_r_le_rsqrt r) fp.u_nonneg
    have hbnonneg : 0 ≤ (b : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    nlinarith [hvalid]
  have hγr : 0 ≤ γr := p08_gamma_nonneg fp.u r fp.u_nonneg (by positivity) hr
  have hγb : 0 ≤ γb := p08_gamma_nonneg fp.u b fp.u_nonneg (by positivity) hb
  have h1 : ‖e1‖ ≤ γb * ‖T‖ * ‖p08Col v‖ :=
    p08_matvec_forward fp T v hb
  have h2 : ‖e2‖ ≤ γr * ‖X‖ * ‖p08Col wh‖ :=
    p08_matvec_forward fp X wh hr
  have he1 : e1 = p08Col wh - T * p08Col v := by
    rw [← p08_col_matvec]
    ext i j
    rfl
  have he2 : e2 = p08Col z - X * p08Col wh := by
    rw [← p08_col_matvec]
    ext i j
    rfl
  have het : et = p08Col z - X * (T * p08Col v) := by
    rw [← p08_col_lowrank_matvec]
    ext i j
    rfl
  have hdecomp : et = e2 + X * e1 := by
    rw [he1, he2, het, Matrix.mul_sub]
    abel
  have hw : ‖p08Col wh‖ ≤ (1 + γb) * ‖T‖ * ‖p08Col v‖ := by
    have hweq : p08Col wh = e1 + T * p08Col v := by rw [he1]; abel
    calc
      ‖p08Col wh‖ = ‖e1 + T * p08Col v‖ := by rw [hweq]
      _ ≤ ‖e1‖ + ‖T * p08Col v‖ := norm_add_le _ _
      _ ≤ γb * ‖T‖ * ‖p08Col v‖ + ‖T‖ * ‖p08Col v‖ :=
        add_le_add h1 (Matrix.frobenius_norm_mul _ _)
      _ = (1 + γb) * ‖T‖ * ‖p08Col v‖ := by ring
  have h2' : ‖e2‖ ≤
      γr * Real.sqrt (r : ℝ) * (1 + γb) * ‖Y‖ * ‖p08Col v‖ := by
    calc
      ‖e2‖ ≤ γr * ‖X‖ * ‖p08Col wh‖ := h2
      _ ≤ γr * ‖X‖ * ((1 + γb) * ‖T‖ * ‖p08Col v‖) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hγr (norm_nonneg _))
      _ = γr * Real.sqrt (r : ℝ) * (1 + γb) * ‖Y‖ * ‖p08Col v‖ := by
        rw [p08_orthonormal_norm X hX, Matrix.frobenius_norm_transpose]
        ring
  have htotal : ‖et‖ ≤
      (γb + γr * Real.sqrt (r : ℝ) + γb * (γr * Real.sqrt (r : ℝ))) *
        ‖Y‖ * ‖p08Col v‖ := by
    calc
      ‖et‖ = ‖e2 + X * e1‖ := by rw [hdecomp]
      _ ≤ ‖e2‖ + ‖X * e1‖ := norm_add_le _ _
      _ = ‖e2‖ + ‖e1‖ := by rw [p08_orthonormal_mul_norm X hX]
      _ ≤ γr * Real.sqrt (r : ℝ) * (1 + γb) * ‖Y‖ * ‖p08Col v‖ +
          γb * ‖Y‖ * ‖p08Col v‖ := by
        apply add_le_add h2'
        simpa only [T, Matrix.frobenius_norm_transpose] using h1
      _ = _ := by ring
  have hcoeff : γb + γr * Real.sqrt (r : ℝ) +
      γb * (γr * Real.sqrt (r : ℝ)) ≤ γc :=
    p08_gamma_combine b r fp.u fp.u_nonneg hvalid
  have hnn : 0 ≤ ‖Y‖ * ‖p08Col v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hlast := mul_le_mul_of_nonneg_right hcoeff hnn
  change ‖et‖ ≤ γc * ‖p08LowRankMatrix X Y‖ * ‖p08Col v‖
  rw [p08_lowrank_norm X Y hX]
  nlinarith [htotal, hlast]

/-- Full Lemma 3.1: low-rank matrix-vector backward error and its A-relative bound. -/
theorem p08_c2_full_low_rank_matvec_error
    {b r : ℕ} (fp : StandardFPModel)
    (A : P08Matrix b) (X Y : P08RectMatrix b r) (v : P08Vector b)
    (ε β : ℝ) (hβ : 0 < β)
    (hX : p08OrthonormalColumns X)
    (happrox : p08FrobNorm (A - p08LowRankMatrix X Y) ≤ ε * β)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    let zHat := p08RoundedLowRankMatVec fp X Y v
    ∃ ΔAtilde ΔA : P08Matrix b,
      zHat = p08MatVec (p08RectAdd (p08LowRankMatrix X Y) ΔAtilde) v ∧
      p08FrobNorm ΔAtilde ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) ∧
      zHat = p08MatVec (p08RectAdd A ΔA) v ∧
      p08FrobNorm ΔA ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm A +
        ε * (1 + p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u) * β := by
  -- PROOF_START P08-C2-H001
  let L := p08LowRankMatrix X Y
  let z := p08RoundedLowRankMatVec fp X Y v
  let γc := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  have hc : 0 ≤ (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) := by
    positivity
  have hγc : 0 ≤ γc := p08_gamma_nonneg fp.u _ fp.u_nonneg hc hvalid
  have hf :
      ‖p08Col (fun i => z i - p08RectMatVec L v i)‖ ≤
        γc * ‖L‖ * ‖p08Col v‖ := by
    simpa only [L, z, γc] using p08_lowrank_forward fp X Y v hX hvalid
  obtain ⟨D, hz, hD⟩ := p08_backward_of_forward L v z γc hγc hf
  let E : P08Matrix b := L + D - A
  have hAeq : p08RectAdd A E = p08RectAdd L D := by
    ext i j
    dsimp [E, p08RectAdd]
    ring
  have happroxN : ‖A - L‖ ≤ ε * β := by
    simpa only [L, p08_frob_eq_norm_sq] using happrox
  have hLA : ‖L - A‖ ≤ ε * β := by rw [norm_sub_rev]; exact happroxN
  have hLbound : ‖L‖ ≤ ‖A‖ + ε * β := by
    calc
      ‖L‖ = ‖A + (L - A)‖ := by congr 1; abel
      _ ≤ ‖A‖ + ‖L - A‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ε * β := by simpa [add_comm] using add_le_add_left hLA ‖A‖
  have hEnorm : ‖E‖ ≤ γc * ‖A‖ + ε * (1 + γc) * β := by
    have hEeq : E = D + (L - A) := by dsimp [E]; abel
    have hmul := mul_le_mul_of_nonneg_left hLbound hγc
    calc
      ‖E‖ = ‖D + (L - A)‖ := by rw [hEeq]
      _ ≤ ‖D‖ + ‖L - A‖ := norm_add_le _ _
      _ ≤ γc * ‖L‖ + ε * β := add_le_add hD hLA
      _ ≤ γc * (‖A‖ + ε * β) + ε * β := by
        simpa [add_comm] using add_le_add_right hmul (ε * β)
      _ = γc * ‖A‖ + ε * (1 + γc) * β := by ring
  refine ⟨D, E, ?_, ?_, ?_, ?_⟩
  · change z = p08MatVec (p08RectAdd L D) v
    exact hz
  · simpa only [p08_frob_eq_norm_sq, L, γc] using hD
  · change z = p08MatVec (p08RectAdd A E) v
    rw [hAeq]
    exact hz
  · simpa only [p08_frob_eq_norm_sq, γc] using hEnorm

end VSCLReuse

import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped Matrix Matrix.Norms.Frobenius

private lemma p08_gamma_nonneg {k u : ℝ} (hu : 0 ≤ u) (hk : 0 ≤ k)
    (hv : k * u < 1) : 0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private lemma p08_gamma_mono {k l u : ℝ} (hu : 0 ≤ u)
    (hk : 0 ≤ k) (hkl : k ≤ l) (hv : l * u < 1) :
    p08GammaReal k u ≤ p08GammaReal l u := by
  have hku : k * u ≤ l * u := mul_le_mul_of_nonneg_right hkl hu
  have hkden : 0 < 1 - k * u := by linarith
  have hlden : 0 < 1 - l * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ hkden hlden).2
  nlinarith

private lemma p08_gamma_step {k u : ℝ} (hu : 0 ≤ u) (hk : 1 ≤ k)
    (hv : (k + 1) * u < 1) :
    (1 + u) * p08GammaReal k u + u ≤ p08GammaReal (k + 1) u ∧
    (1 + u) ^ 2 - 1 ≤ p08GammaReal (k + 1) u := by
  have hku : 0 ≤ k * u := mul_nonneg (by linarith) hu
  have hden1 : 0 < 1 - k * u := by nlinarith
  have hden2 : 0 < 1 - (k + 1) * u := by linarith
  have hu1 : u < 1 := by nlinarith
  unfold p08GammaReal
  constructor
  · have hid : (1 + u) * (k * u / (1 - k * u)) + u =
        (k + 1) * u / (1 - k * u) := by
      have hd : 1 - k * u ≠ 0 := ne_of_gt hden1
      have hd' : 1 - u * k ≠ 0 := by simpa [mul_comm] using hd
      apply (eq_div_iff hd).2
      field_simp [hd, hd']
      ring
    rw [hid]
    apply (div_le_div_iff₀ hden1 hden2).2
    have hnum : 0 ≤ (k + 1) * u := mul_nonneg (by linarith) hu
    nlinarith
  · have h2 : 2 * u < 1 := by nlinarith
    have hd2 : 0 < 1 - 2 * u := by linarith
    have hbasic : (1 + u) ^ 2 - 1 ≤ (2 * u) / (1 - 2 * u) := by
      apply (le_div_iff₀ hd2).2
      nlinarith [mul_nonneg (sq_nonneg u) hu]
    have hmono := p08_gamma_mono hu (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (2 : ℝ) ≤ k + 1) hv
    exact hbasic.trans (by simpa [p08GammaReal] using hmono)

private lemma p08_fl_mul_error (fp : StandardFPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul a b
  rw [heq]
  have h : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p08_fl_add_error (fp : StandardFPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add a b
  rw [heq]
  have h : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [h, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma p08_round_sum_step (fp : StandardFPModel)
    {acc t a f S G H : ℝ} (hS : 0 ≤ S) (ht : |t| ≤ S)
    (hacc : |acc - t| ≤ G * S) (hf : |f - a| ≤ fp.u * |a|)
    (hG : 0 ≤ G)
    (hGS : (1 + fp.u) * G + fp.u ≤ H)
    (hGa : (1 + fp.u) ^ 2 - 1 ≤ H) :
    |fp.fl_add acc f - (t + a)| ≤ H * (S + |a|) := by
  have haccabs : |acc| ≤ (1 + G) * S := by
    have h := abs_add_le (acc - t) t
    have heq : (acc - t) + t = acc := by ring
    rw [heq] at h
    nlinarith
  have hfabs : |f| ≤ (1 + fp.u) * |a| := by
    have h := abs_add_le (f - a) a
    have heq : (f - a) + a = f := by ring
    rw [heq] at h
    nlinarith
  have hsum : |acc + f| ≤ (1 + G) * S + (1 + fp.u) * |a| := by
    calc
      |acc + f| ≤ |acc| + |f| := abs_add_le _ _
      _ ≤ (1 + G) * S + (1 + fp.u) * |a| := add_le_add haccabs hfabs
  have herr : |fp.fl_add acc f - (t + a)| ≤
      fp.u * |acc + f| + |acc - t| + |f - a| := by
    have heq : fp.fl_add acc f - (t + a) =
        (fp.fl_add acc f - (acc + f)) + ((acc - t) + (f - a)) := by ring
    rw [heq]
    calc
      _ ≤ |fp.fl_add acc f - (acc + f)| + |(acc - t) + (f - a)| := abs_add_le _ _
      _ ≤ |fp.fl_add acc f - (acc + f)| + (|acc - t| + |f - a|) :=
        add_le_add_right (abs_add_le _ _) _
      _ ≤ fp.u * |acc + f| + |acc - t| + |f - a| := by
        linarith [p08_fl_add_error fp acc f]
  have hScoef : (((1 + fp.u) * G + fp.u) * S) ≤ H * S :=
    mul_le_mul_of_nonneg_right hGS hS
  have hAcoef : (((1 + fp.u) ^ 2 - 1) * |a|) ≤ H * |a| :=
    mul_le_mul_of_nonneg_right hGa (abs_nonneg a)
  have hu := fp.u_nonneg
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hsum)]

private lemma p08_rounded_dot_bound (fp : StandardFPModel) :
    ∀ n : ℕ, ∀ x y : Fin (n + 1) → ℝ,
      ((n + 1 : ℕ) : ℝ) * fp.u < 1 →
      |roundedDotProduct fp (n + 1) x y - ∑ i, x i * y i| ≤
        p08GammaReal ((n + 1 : ℕ) : ℝ) fp.u * ∑ i, |x i * y i| := by
  intro n
  induction n with
  | zero =>
      intro x y hv
      have hd : 0 < 1 - fp.u := by norm_num at hv ⊢; linarith
      have hγ : fp.u ≤ p08GammaReal 1 fp.u := by
        unfold p08GammaReal
        norm_num
        apply (le_div_iff₀ hd).2
        nlinarith [sq_nonneg fp.u]
      have h := p08_fl_mul_error fp (x 0) (y 0)
      simpa [roundedDotProduct] using
        (h.trans (mul_le_mul_of_nonneg_right hγ (abs_nonneg (x 0 * y 0))))
  | succ n ih =>
      intro x y hv
      let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
      let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
      have hv' : ((n + 1 : ℕ) : ℝ) * fp.u < 1 := by
        have hle : ((n + 1 : ℕ) : ℝ) * fp.u ≤ ((n + 2 : ℕ) : ℝ) * fp.u := by
          apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
          exact_mod_cast Nat.le_succ (n + 1)
        exact lt_of_le_of_lt hle (by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hv)
      have hprev := ih x' y' hv'
      have ht : |∑ i : Fin (n + 1), x' i * y' i| ≤
          ∑ i : Fin (n + 1), |x' i * y' i| := by
        simpa using Finset.abs_sum_le_sum_abs (fun i : Fin (n + 1) => x' i * y' i) Finset.univ
      have hS : 0 ≤ ∑ i : Fin (n + 1), |x' i * y' i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hγ : 0 ≤ p08GammaReal ((n + 1 : ℕ) : ℝ) fp.u :=
        p08_gamma_nonneg fp.u_nonneg (by positivity) hv'
      have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_left 1 n
      have hvstep : (((n + 1 : ℕ) : ℝ) + 1) * fp.u < 1 := by
        convert hv using 1 <;> push_cast <;> ring
      have hstep := p08_gamma_step fp.u_nonneg hk hvstep
      have hlast := p08_round_sum_step fp hS ht hprev
        (p08_fl_mul_error fp (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
        hγ hstep.1 hstep.2
      have hdot : roundedDotProduct fp (n + 2) x y =
          fp.fl_add (roundedDotProduct fp (n + 1) x' y')
            (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
        simp [roundedDotProduct, Fin.foldl_succ_last, x', y', Fin.castSucc_succ]
      have hsum : (∑ i : Fin (n + 2), x i * y i) =
          (∑ i : Fin (n + 1), x' i * y' i) +
            x (Fin.last (n + 1)) * y (Fin.last (n + 1)) := by
        simpa [x', y'] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => x i * y i))
      have habs : (∑ i : Fin (n + 2), |x i * y i|) =
          (∑ i : Fin (n + 1), |x' i * y' i|) +
            |x (Fin.last (n + 1)) * y (Fin.last (n + 1))| := by
        simpa [x', y'] using
          (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |x i * y i|))
      have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (((n + 2 : ℕ) : ℝ)) := by
        push_cast
        ring
      rw [hcast] at hlast
      rw [hdot, hsum, habs]
      simpa [x', y', Nat.succ_eq_add_one, Nat.add_assoc] using hlast

private lemma p08_frob_eq_norm {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = ‖M‖ := by
  rw [Matrix.frobenius_norm_def]
  simp [p08RectFrobNorm, Real.sqrt_eq_rpow, sq_abs]

private noncomputable def p08Sign (a : ℝ) : ℝ := if a < 0 then -1 else 1

private lemma p08Sign_mul (a : ℝ) : p08Sign a * a = |a| := by
  by_cases h : a < 0
  · simp [p08Sign, h, abs_of_neg h]
  · have ha : 0 ≤ a := le_of_not_gt h
    simp [p08Sign, h, abs_of_nonneg ha]

private lemma p08Sign_abs (a : ℝ) : |p08Sign a| = 1 := by
  by_cases h : a < 0 <;> simp [p08Sign, h]

private lemma p08_frob_le_entry {m n : ℕ} (E A : P08RectMatrix m n)
    {g : ℝ} (hg : 0 ≤ g) (he : ∀ i j, |E i j| ≤ g * |A i j|) :
    p08RectFrobNorm E ≤ g * p08RectFrobNorm A := by
  have hsq : ∀ i j, (E i j) ^ 2 ≤ g ^ 2 * (A i j) ^ 2 := by
    intro i j
    have h := pow_le_pow_left₀ (abs_nonneg (E i j)) (he i j) 2
    simpa [mul_pow, sq_abs] using h
  have hsum : (∑ i : Fin m, ∑ j : Fin n, (E i j) ^ 2) ≤
      g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * (A i j) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
      _ = g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, (A i j) ^ 2) := by
        simp [Finset.mul_sum]
  have hroot := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq_eq_abs, abs_of_nonneg hg] at hroot
  simpa [p08RectFrobNorm] using hroot

private lemma p08_rounded_dot_bound_all (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : (n : ℝ) * fp.u < 1) :
    |roundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p08GammaReal (n : ℝ) fp.u * ∑ i, |x i * y i| := by
  cases n with
  | zero => simp [roundedDotProduct, p08GammaReal]
  | succ n => exact p08_rounded_dot_bound fp n x y hv

private lemma p08_backward_matvec_of_row_bound {m n : ℕ}
    (A : P08RectMatrix m n) (v : Fin n → ℝ) (w : Fin m → ℝ)
    {g : ℝ} (hg : 0 ≤ g)
    (hrow : ∀ i, |w i - ∑ j, A i j * v j| ≤
      g * ∑ j, |A i j * v j|) :
    ∃ E : P08RectMatrix m n,
      w = p08RectMatVec (p08RectAdd A E) v ∧
      p08RectFrobNorm E ≤ g * p08RectFrobNorm A := by
  let S : Fin m → ℝ := fun i => ∑ j : Fin n, |A i j * v j|
  let e : Fin m → ℝ := fun i => w i - ∑ j : Fin n, A i j * v j
  let E : P08RectMatrix m n := fun i j =>
    if S i = 0 then 0 else (e i / S i) * p08Sign (A i j * v j) * A i j
  have hS : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcoef : ∀ i, S i ≠ 0 → |e i / S i| ≤ g := by
    intro i hne
    have hpos : 0 < S i := lt_of_le_of_ne (hS i) (Ne.symm hne)
    rw [abs_div, abs_of_nonneg (hS i)]
    exact (div_le_iff₀ hpos).2 (hrow i)
  have hentry : ∀ i j, |E i j| ≤ g * |A i j| := by
    intro i j
    by_cases hzero : S i = 0
    · simp only [E, hzero, ↓reduceIte, abs_zero]
      exact mul_nonneg hg (abs_nonneg _)
    · simp only [E, hzero, ↓reduceIte, abs_mul, p08Sign_abs, mul_one]
      exact mul_le_mul_of_nonneg_right (hcoef i hzero) (abs_nonneg _)
  have hmul : ∀ i, ∑ j : Fin n, E i j * v j = e i := by
    intro i
    by_cases hzero : S i = 0
    · have hezero : e i = 0 := by
        have h := hrow i
        change |e i| ≤ g * S i at h
        rw [hzero, mul_zero] at h
        exact abs_nonpos_iff.mp h
      simp [E, hzero, hezero]
    · have hsum : (∑ j : Fin n, E i j * v j) = (e i / S i) * S i := by
        simp only [E, hzero, ↓reduceIte]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        calc
          e i / S i * p08Sign (A i j * v j) * A i j * v j =
              (e i / S i) * (p08Sign (A i j * v j) * (A i j * v j)) := by ring
          _ = (e i / S i) * |A i j * v j| := by rw [p08Sign_mul]
      rw [hsum, div_mul_cancel₀ _ hzero]
  refine ⟨E, ?_, p08_frob_le_entry E A hg hentry⟩
  funext i
  have h := hmul i
  simp only [p08RectMatVec, p08RectAdd]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  dsimp [e] at h
  linarith

private lemma p08_rounded_matvec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P08RectMatrix m n) (v : Fin n → ℝ)
    (hv : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      p08RoundedRectMatVec fp A v = p08RectMatVec (p08RectAdd A E) v ∧
      p08RectFrobNorm E ≤ p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm A := by
  apply p08_backward_matvec_of_row_bound A v (p08RoundedRectMatVec fp A v)
    (p08_gamma_nonneg fp.u_nonneg (by positivity) hv)
  intro i
  simpa [p08RoundedRectMatVec, roundedMatVec] using
    p08_rounded_dot_bound_all fp n (A i) v hv

private lemma p08_frob_sq_trace {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M ^ 2 = Matrix.trace (Mᵀ * M) := by
  have hs : 0 ≤ ∑ i : Fin m, ∑ j : Fin n, (M i j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [p08RectFrobNorm, Real.sq_sqrt hs]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

private lemma p08_X_gram {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) : Xᵀ * X = 1 := by
  ext j k
  simpa [p08OrthonormalColumns, Matrix.mul_apply, Matrix.transpose_apply] using hX j k

private lemma p08_X_isometry {b r p : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) (M : P08RectMatrix r p) :
    p08RectFrobNorm (X * M) = p08RectFrobNorm M := by
  have hgram := p08_X_gram X hX
  have hsq : p08RectFrobNorm (X * M) ^ 2 = p08RectFrobNorm M ^ 2 := by
    rw [p08_frob_sq_trace, p08_frob_sq_trace, Matrix.transpose_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ X M, hgram, Matrix.one_mul]
  have hnonneg1 : 0 ≤ p08RectFrobNorm (X * M) := Real.sqrt_nonneg _
  have hnonneg2 : 0 ≤ p08RectFrobNorm M := Real.sqrt_nonneg _
  nlinarith

private lemma p08_X_norm {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  have hsum : (∑ i : Fin b, ∑ j : Fin r, (X i j) ^ 2) = (r : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [pow_two]
    have hcol : ∀ j : Fin r, (∑ i : Fin b, X i j * X i j) = 1 := by
      intro j
      simpa using hX j j
    simp_rw [hcol]
    simp
  simp [p08RectFrobNorm, hsum]

private lemma p08_frob_add_le {m n : ℕ} (M N : P08RectMatrix m n) :
    p08RectFrobNorm (M + N) ≤ p08RectFrobNorm M + p08RectFrobNorm N := by
  simpa only [p08_frob_eq_norm] using norm_add_le M N

private lemma p08_frob_mul_le {m n p : ℕ}
    (M : P08RectMatrix m n) (N : P08RectMatrix n p) :
    p08RectFrobNorm (M * N) ≤ p08RectFrobNorm M * p08RectFrobNorm N := by
  simpa only [p08_frob_eq_norm] using Matrix.frobenius_norm_mul M N

private lemma p08_frob_transpose {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm Mᵀ = p08RectFrobNorm M := by
  simpa only [p08_frob_eq_norm] using Matrix.frobenius_norm_transpose M

private lemma p08_one_add_gamma {x u : ℝ} (hv : x * u < 1) :
    1 + p08GammaReal x u = 1 / (1 - x * u) := by
  have hd : 1 - x * u ≠ 0 := ne_of_gt (by linarith)
  unfold p08GammaReal
  field_simp [hd]
  ring

private lemma p08_gamma_compose {x y u : ℝ} (hu : 0 ≤ u)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hv : (x + y) * u < 1) :
    p08GammaReal x u + p08GammaReal y u +
      p08GammaReal x u * p08GammaReal y u ≤ p08GammaReal (x + y) u := by
  have hxu : x * u < 1 := by nlinarith [mul_nonneg hy hu]
  have hyu : y * u < 1 := by nlinarith [mul_nonneg hx hu]
  have hdx : 0 < 1 - x * u := by linarith
  have hdy : 0 < 1 - y * u := by linarith
  have hdc : 0 < 1 - (x + y) * u := by linarith
  have hden : 1 - (x + y) * u ≤ (1 - x * u) * (1 - y * u) := by
    nlinarith [mul_nonneg (mul_nonneg hx hy) (sq_nonneg u)]
  have hrecip : (1 : ℝ) / ((1 - x * u) * (1 - y * u)) ≤
      1 / (1 - (x + y) * u) := by
    apply (div_le_div_iff₀ (mul_pos hdx hdy) hdc).2
    simpa using hden
  have hprod : (1 + p08GammaReal x u) * (1 + p08GammaReal y u) ≤
      1 + p08GammaReal (x + y) u := by
    rw [p08_one_add_gamma hxu, p08_one_add_gamma hyu,
      p08_one_add_gamma hv]
    simpa [one_div, mul_inv_rev, mul_comm] using hrecip
  nlinarith

private lemma p08_gamma_scale {r s u : ℝ} (hu : 0 ≤ u)
    (hr : 0 ≤ r) (hs : 1 ≤ s) (hv : (r * s) * u < 1) :
    p08GammaReal r u * s ≤ p08GammaReal (r * s) u := by
  have hru : r * u ≤ (r * s) * u := by nlinarith [mul_nonneg hr hu]
  have hrv : r * u < 1 := lt_of_le_of_lt hru hv
  have hdr : 0 < 1 - r * u := by linarith
  have hds : 0 < 1 - (r * s) * u := by linarith
  have hnum : 0 ≤ (r * s) * u := mul_nonneg (mul_nonneg hr (by linarith)) hu
  unfold p08GammaReal
  have hid : r * u / (1 - r * u) * s = (r * s) * u / (1 - r * u) := by
    ring
  rw [hid]
  apply (div_le_div_iff₀ hdr hds).2
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hru)]

private lemma p08_rank_le_rank_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => norm_num
  | succ n =>
      have hr1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hs : 1 ≤ Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
        Real.one_le_sqrt.mpr hr1
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
        (sub_nonneg.mpr hs)]

private lemma p08_gamma_lr_bound (fp : StandardFPModel) (b r : ℕ)
    (hv : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    p08GammaReal (b : ℝ) fp.u +
      p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) +
      p08GammaReal (b : ℝ) fp.u *
        (p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ)) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
  let q : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have hq : 0 ≤ q := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hqv : q * fp.u < 1 := by
    have hb : 0 ≤ (b : ℝ) * fp.u := mul_nonneg (by positivity) fp.u_nonneg
    dsimp [q] at *
    nlinarith
  have hbv : (b : ℝ) * fp.u < 1 := by
    have hqu : 0 ≤ q * fp.u := mul_nonneg hq fp.u_nonneg
    dsimp [q] at *
    nlinarith
  have hscale : p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) ≤
      p08GammaReal q fp.u := by
    cases r with
    | zero => simp [q, p08GammaReal]
    | succ n =>
        have hr1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        have hs : 1 ≤ Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
          Real.one_le_sqrt.mpr hr1
        exact p08_gamma_scale fp.u_nonneg (by positivity) hs hqv
  have hgb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
    p08_gamma_nonneg fp.u_nonneg (by positivity) hbv
  have hmul := mul_le_mul_of_nonneg_left hscale hgb
  have hcomp := p08_gamma_compose fp.u_nonneg
    (show (0 : ℝ) ≤ b by positivity) hq hv
  dsimp [q] at *
  nlinarith

private lemma p08_lowrank_backward (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (v : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ D : P08Matrix b,
      p08RoundedLowRankMatVec fp X Y v =
        p08MatVec (p08RectAdd (p08LowRankMatrix X Y) D) v ∧
      p08FrobNorm D ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) := by
  let s : ℝ := Real.sqrt (r : ℝ)
  let gb : ℝ := p08GammaReal (b : ℝ) fp.u
  let gr : ℝ := p08GammaReal (r : ℝ) fp.u
  let gc : ℝ := p08GammaReal ((b : ℝ) + (r : ℝ) * s) fp.u
  have hqnonneg : 0 ≤ (r : ℝ) * s :=
    mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have hq : 0 ≤ ((r : ℝ) * s) * fp.u := mul_nonneg hqnonneg fp.u_nonneg
    dsimp [s] at *
    nlinarith
  have hrvalid : (r : ℝ) * fp.u < 1 := by
    have hle : (r : ℝ) ≤ (b : ℝ) + (r : ℝ) * s := by
      have hr := p08_rank_le_rank_sqrt r
      dsimp [s]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hle fp.u_nonneg
    exact lt_of_le_of_lt hmul hvalid
  obtain ⟨DY, hYstage, hDY⟩ :=
    p08_rounded_matvec_backward fp (p08RectTranspose Y) v hbvalid
  let wHat : Fin r → ℝ := p08RoundedRectMatVec fp (p08RectTranspose Y) v
  obtain ⟨DX, hXstage, hDX⟩ :=
    p08_rounded_matvec_backward fp X wHat hrvalid
  let L : P08Matrix b := p08LowRankMatrix X Y
  let D : P08Matrix b := (X + DX) * (Yᵀ + DY) - L
  have hLnorm : p08FrobNorm L = p08RectFrobNorm Y := by
    change p08RectFrobNorm (X * Yᵀ) = p08RectFrobNorm Y
    rw [p08_X_isometry X hX, p08_frob_transpose]
  have hDYbound : p08RectFrobNorm DY ≤ gb * p08FrobNorm L := by
    calc
      p08RectFrobNorm DY ≤ gb * p08RectFrobNorm (p08RectTranspose Y) := hDY
      _ = gb * p08RectFrobNorm Y := by
        change gb * p08RectFrobNorm Yᵀ = gb * p08RectFrobNorm Y
        rw [p08_frob_transpose]
      _ = gb * p08FrobNorm L := by rw [hLnorm]
  have hDXbound : p08RectFrobNorm DX ≤ gr * s := by
    simpa [gr, s, p08_X_norm X hX] using hDX
  have hprod : p08RoundedLowRankMatVec fp X Y v =
      p08MatVec ((X + DX) * (Yᵀ + DY)) v := by
    change p08RoundedRectMatVec fp X wHat = _
    rw [hXstage]
    change (X + DX).mulVec
      (p08RoundedRectMatVec fp (p08RectTranspose Y) v) =
      ((X + DX) * (Yᵀ + DY)).mulVec v
    rw [hYstage]
    exact Matrix.mulVec_mulVec v (X + DX) (Yᵀ + DY)
  have hDexpr : D = X * DY + DX * Yᵀ + DX * DY := by
    dsimp [D, L]
    change (X + DX) * (Yᵀ + DY) - X * Yᵀ = _
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    abel
  have hnonnegL : 0 ≤ p08FrobNorm L := Real.sqrt_nonneg _
  have hnonnegDY : 0 ≤ p08RectFrobNorm DY := Real.sqrt_nonneg _
  have hnonnegGRS : 0 ≤ gr * s := by
    apply mul_nonneg
    · exact p08_gamma_nonneg fp.u_nonneg (by positivity) hrvalid
    · exact Real.sqrt_nonneg _
  have hnormD : p08FrobNorm D ≤
      (gb + gr * s + gb * (gr * s)) * p08FrobNorm L := by
    have htri : p08FrobNorm D ≤
        p08RectFrobNorm (X * DY) +
          p08RectFrobNorm (DX * Yᵀ) + p08RectFrobNorm (DX * DY) := by
      rw [hDexpr]
      calc
        p08RectFrobNorm (X * DY + DX * Yᵀ + DX * DY) ≤
            p08RectFrobNorm (X * DY + DX * Yᵀ) + p08RectFrobNorm (DX * DY) :=
          p08_frob_add_le _ _
        _ ≤ p08RectFrobNorm (X * DY) + p08RectFrobNorm (DX * Yᵀ) +
            p08RectFrobNorm (DX * DY) := by
          linarith [p08_frob_add_le (X * DY) (DX * Yᵀ)]
    have hfirst : p08RectFrobNorm (X * DY) = p08RectFrobNorm DY :=
      p08_X_isometry X hX DY
    have hsecond : p08RectFrobNorm (DX * Yᵀ) ≤
        (gr * s) * p08FrobNorm L := by
      calc
        _ ≤ p08RectFrobNorm DX * p08RectFrobNorm Yᵀ := p08_frob_mul_le _ _
        _ = p08RectFrobNorm DX * p08FrobNorm L := by rw [p08_frob_transpose, hLnorm]
        _ ≤ (gr * s) * p08FrobNorm L :=
          mul_le_mul_of_nonneg_right hDXbound hnonnegL
    have hthird : p08RectFrobNorm (DX * DY) ≤
        (gr * s) * (gb * p08FrobNorm L) := by
      calc
        _ ≤ p08RectFrobNorm DX * p08RectFrobNorm DY := p08_frob_mul_le _ _
        _ ≤ (gr * s) * p08RectFrobNorm DY :=
          mul_le_mul_of_nonneg_right hDXbound hnonnegDY
        _ ≤ (gr * s) * (gb * p08FrobNorm L) :=
          mul_le_mul_of_nonneg_left hDYbound hnonnegGRS
    rw [hfirst] at htri
    nlinarith [hDYbound, hsecond, hthird]
  have hcoef : gb + gr * s + gb * (gr * s) ≤ gc := by
    exact p08_gamma_lr_bound fp b r hvalid
  have hDfinal : p08FrobNorm D ≤ gc * p08FrobNorm L :=
    hnormD.trans (mul_le_mul_of_nonneg_right hcoef hnonnegL)
  refine ⟨D, ?_, ?_⟩
  · dsimp [D]
    have hsum : L + ((X + DX) * (Yᵀ + DY) - L) =
        (X + DX) * (Yᵀ + DY) := by abel
    change p08RoundedLowRankMatVec fp X Y v =
      p08MatVec (L + ((X + DX) * (Yᵀ + DY) - L)) v
    rw [hsum]
    exact hprod
  · exact hDfinal

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
  dsimp
  obtain ⟨D, hz, hD⟩ := p08_lowrank_backward fp X Y v hX hvalid
  let L : P08Matrix b := p08LowRankMatrix X Y
  let G : ℝ := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  let ΔA : P08Matrix b := D - (A - L)
  have hG : 0 ≤ G :=
    p08_gamma_nonneg fp.u_nonneg
      (by exact add_nonneg (by positivity) (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
      hvalid
  have hmat : A + ΔA = L + D := by
    dsimp [ΔA, L]
    abel
  have hLtri : p08FrobNorm L ≤ p08FrobNorm A + p08FrobNorm (A - L) := by
    have hLid : L = A - (A - L) := by abel
    calc
      p08FrobNorm L = p08FrobNorm (A - (A - L)) :=
        congrArg p08FrobNorm hLid
      _ ≤ p08FrobNorm A + p08FrobNorm (A - L) := by
        simpa only [p08FrobNorm, p08_frob_eq_norm] using norm_sub_le A (A - L)
  have hΔ : p08FrobNorm ΔA ≤ p08FrobNorm D + p08FrobNorm (A - L) := by
    change p08RectFrobNorm (D - (A - L)) ≤
      p08RectFrobNorm D + p08RectFrobNorm (A - L)
    simpa only [p08_frob_eq_norm] using norm_sub_le D (A - L)
  have hfinal : p08FrobNorm ΔA ≤
      G * p08FrobNorm A + ε * (1 + G) * β := by
    have hmul := mul_le_mul_of_nonneg_left hLtri hG
    have happrox' : p08FrobNorm (A - L) ≤ ε * β := happrox
    have hmul' := mul_le_mul_of_nonneg_left happrox' (by linarith : 0 ≤ 1 + G)
    have hD' : p08FrobNorm D ≤ G * p08FrobNorm L := hD
    nlinarith
  refine ⟨D, ΔA, hz, hD, ?_, hfinal⟩
  change p08RoundedLowRankMatVec fp X Y v = p08MatVec (A + ΔA) v
  rw [hmat]
  exact hz

end VSCLReuse

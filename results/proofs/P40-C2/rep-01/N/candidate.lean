import VSCLReuse.P40.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p40_mul_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  rw [hfl]
  have heq : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p40_add_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma p40_sub_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub a b
  rw [hfl]
  have heq : (a - b) * (1 + δ) - (a - b) = (a - b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a - b))

private lemma p40_pow_den_bound (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hfac : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
          1 - (k : ℝ) * u := by
        have hn : 0 ≤ ((k : ℝ) + 1) * u * u := by positivity
        push_cast
        nlinarith
      calc
        (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ k * ((1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hfac (pow_nonneg (by positivity) _)
        _ ≤ 1 := ih

private lemma p40_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P40GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p40Gamma u k := by
  have hd : 0 < 1 - (k : ℝ) * u := by
    unfold P40GammaValid at hk
    linarith
  unfold p40Gamma
  apply (le_div_iff₀ hd).2
  have hp := p40_pow_den_bound u hu k
  nlinarith

private lemma p40_roundedDot_eq_foldDot (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p40RoundedDotProduct fp n x y =
      Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 := by
  cases n with
  | zero => simp [p40RoundedDotProduct]
  | succ n =>
      simp only [p40RoundedDotProduct, Fin.foldl_succ,
        fp.fl_add_zero]

private lemma p40_foldDot_one (fp : P40FPModel) (x y : Fin 1 → ℝ) :
    |Fin.foldl 1 (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 -
      ∑ i : Fin 1, x i * y i| ≤
      ((1 + fp.u) ^ 1 - 1) * ∑ i : Fin 1, |x i| * |y i| := by
  simp only [Fin.foldl_succ, Fin.foldl_zero, fp.fl_add_zero,
    Fin.sum_univ_one, pow_one]
  have h := p40_mul_error fp (x 0) (y 0)
  simpa [abs_mul, add_sub_cancel_left] using h

private lemma p40_fold_step (fp : P40FPModel) (c d p t S e E : ℝ)
    (hS : 0 ≤ S) (hd : |d| ≤ S)
    (he : |c - d| ≤ e * S)
    (hp : |p - t| ≤ fp.u * |t|)
    (hcoef : (1 + fp.u) * e + fp.u ≤ E)
    (hnew : fp.u * (1 + fp.u) + fp.u ≤ E) :
    |fp.fl_add c p - (d + t)| ≤ E * (S + |t|) := by
  have htri : |fp.fl_add c p - (d + t)| ≤
      fp.u * |c + p| + |c - d| + |p - t| := by
    have h₁ := abs_sub_le (fp.fl_add c p) (c + p) (d + t)
    have h₂ := abs_sub_le (c + p) (d + p) (d + t)
    have h₃ := p40_add_error fp c p
    have h₄ : |(c + p) - (d + p)| = |c - d| := by congr 1; ring
    have h₅ : |(d + p) - (d + t)| = |p - t| := by congr 1; ring
    rw [h₄, h₅] at h₂
    linarith
  have hc : |c| ≤ |c - d| + |d| := by
    calc
      |c| = |(c - d) + d| := by ring
      _ ≤ |c - d| + |d| := abs_add_le _ _
  have hpabs : |p| ≤ |p - t| + |t| := by
    calc
      |p| = |(p - t) + t| := by ring
      _ ≤ |p - t| + |t| := abs_add_le _ _
  have habs : |c + p| ≤ |c - d| + S + |p - t| + |t| := by
    have h := abs_add_le c p
    linarith
  have hmul := mul_le_mul_of_nonneg_left habs fp.u_nonneg
  have hmulp := mul_le_mul_of_nonneg_left hp fp.u_nonneg
  have herr := mul_le_mul_of_nonneg_left he (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
  have hcoefS := mul_le_mul_of_nonneg_right hcoef hS
  have hnewT := mul_le_mul_of_nonneg_right hnew (abs_nonneg t)
  nlinarith

private lemma p40_foldDot_error (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    |Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 -
      ∑ i : Fin n, x i * y i| ≤
      ((1 + fp.u) ^ n - 1) * ∑ i : Fin n, |x i| * |y i| := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simpa using p40_foldDot_one fp x y
      | succ k =>
          let xc : Fin (k + 1) → ℝ := fun i => x i.castSucc
          let yc : Fin (k + 1) → ℝ := fun i => y i.castSucc
          let c := Fin.foldl (k + 1)
            (fun acc i => fp.fl_add acc (fp.fl_mul (xc i) (yc i))) 0
          let d := ∑ i : Fin (k + 1), xc i * yc i
          let S := ∑ i : Fin (k + 1), |xc i| * |yc i|
          let t := x (Fin.last (k + 1)) * y (Fin.last (k + 1))
          let p := fp.fl_mul (x (Fin.last (k + 1))) (y (Fin.last (k + 1)))
          have hfold : Fin.foldl (k + 1 + 1)
              (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 =
              fp.fl_add c p := by
            simp [Fin.foldl_succ_last, c, p, xc, yc]
          have hsum : (∑ i : Fin (k + 1 + 1), x i * y i) = d + t := by
            simp [Fin.sum_univ_castSucc, d, t, xc, yc]
          have habssum : (∑ i : Fin (k + 1 + 1), |x i| * |y i|) = S + |t| := by
            simp [Fin.sum_univ_castSucc, S, t, xc, yc, abs_mul]
          have hS : 0 ≤ S := by
            dsimp [S]
            exact Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          have hd : |d| ≤ S := by
            dsimp [d, S]
            simpa [abs_mul] using
              (Finset.abs_sum_le_sum_abs (fun i : Fin (k + 1) => xc i * yc i) Finset.univ)
          have he : |c - d| ≤ ((1 + fp.u) ^ (k + 1) - 1) * S := ih xc yc
          have hp : |p - t| ≤ fp.u * |t| := by
            exact p40_mul_error fp _ _
          have hcoef : (1 + fp.u) * ((1 + fp.u) ^ (k + 1) - 1) + fp.u ≤
              (1 + fp.u) ^ (k + 1 + 1) - 1 := by
            apply le_of_eq
            rw [pow_succ]
            ring
          have hnew : fp.u * (1 + fp.u) + fp.u ≤
              (1 + fp.u) ^ (k + 1 + 1) - 1 := by
            have hq : 1 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
            have hpow : 1 ≤ (1 + fp.u) ^ k := one_le_pow₀ hq
            have hq2 : 0 ≤ (1 + fp.u) ^ 2 := pow_nonneg (by positivity) _
            have hm := mul_le_mul_of_nonneg_right hpow hq2
            have hpow2 : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (k + 1 + 1) := by
              calc
                (1 + fp.u) ^ 2 = 1 * (1 + fp.u) ^ 2 := by ring
                _ ≤ (1 + fp.u) ^ k * (1 + fp.u) ^ 2 := hm
                _ = (1 + fp.u) ^ (k + 1 + 1) := by rw [← pow_add]
            nlinarith [hpow2]
          rw [hfold, hsum, habssum]
          exact p40_fold_step fp c d p t S _ _ hS hd he hp hcoef hnew

private lemma p40_sub_step (fp : P40FPModel) (b c z S e E : ℝ)
    (hS : 0 ≤ S) (hz : |z| ≤ S)
    (he : |c - z| ≤ e * S)
    (hcoef : (1 + fp.u) * e + fp.u ≤ E)
    (hbcoef : fp.u ≤ E) :
    |fp.fl_sub b c - (b - z)| ≤ E * (|b| + S) := by
  have htri : |fp.fl_sub b c - (b - z)| ≤
      fp.u * |b - c| + |c - z| := by
    have h₁ := abs_sub_le (fp.fl_sub b c) (b - c) (b - z)
    have h₂ := p40_sub_error fp b c
    have h₃ : |(b - c) - (b - z)| = |c - z| := by
      rw [abs_sub_comm]
      congr 1
      ring
    rw [h₃] at h₁
    linarith
  have hc : |c| ≤ |c - z| + |z| := by
    calc
      |c| = |(c - z) + z| := by ring
      _ ≤ |c - z| + |z| := abs_add_le _ _
  have hbc : |b - c| ≤ |b| + |c - z| + S := by
    have h := abs_sub_le b 0 c
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbc fp.u_nonneg
  have herr := mul_le_mul_of_nonneg_left he (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
  have hcoefS := mul_le_mul_of_nonneg_right hcoef hS
  have hbcoefB := mul_le_mul_of_nonneg_right hbcoef (abs_nonneg b)
  nlinarith

private lemma p40_high_error (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fp.u (n + 1)) (i : Fin n) :
    |p40HighResidual fp n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      p40Gamma fp.u (n + 1) *
        (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  let z := ∑ j : Fin n, A i j * x j
  let S := ∑ j : Fin n, |A i j| * |x j|
  let c := p40RoundedDotProduct fp n (A i) x
  let e := (1 + fp.u) ^ n - 1
  let E := (1 + fp.u) ^ (n + 1) - 1
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hz : |z| ≤ S := by
    dsimp [z, S]
    simpa [abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun j : Fin n => A i j * x j) Finset.univ)
  have he : |c - z| ≤ e * S := by
    dsimp [c, z, e, S]
    rw [p40_roundedDot_eq_foldDot]
    exact p40_foldDot_error fp n (A i) x
  have hcoef : (1 + fp.u) * e + fp.u ≤ E := by
    dsimp [e, E]
    apply le_of_eq
    rw [pow_succ]
    ring
  have hbcoef : fp.u ≤ E := by
    have hq : 1 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have hp : 1 ≤ (1 + fp.u) ^ n := one_le_pow₀ hq
    dsimp [E]
    rw [pow_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) fp.u_nonneg]
  have hstep := p40_sub_step fp (b i) c z S e E hS hz he hcoef hbcoef
  have hgamma := p40_pow_le_gamma fp.u fp.u_nonneg (n + 1) hvalid
  have hmag : 0 ≤ |b i| + S := add_nonneg (abs_nonneg _) hS
  have hmul := mul_le_mul_of_nonneg_right hgamma hmag
  change |fp.fl_sub (b i) c - (b i - z)| ≤
    p40Gamma fp.u (n + 1) * (|b i| + S)
  exact hstep.trans hmul

/-- Equation (2.3): the two-precision computed residual bound. -/
theorem p40_c2_two_precision_residual
    (fpHi fpLo : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fpHi.u (n + 1))
    (_hprecision : fpHi.u ≤ fpLo.u) :
    ∀ i : Fin n,
      |p40StoredResidual fpHi fpLo n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      fpLo.u * |b i - ∑ j : Fin n, A i j * x j| +
        (1 + fpLo.u) * p40Gamma fpHi.u (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  -- PROOF_START P40-C2-H001
  intro i
  let z := b i - ∑ j : Fin n, A i j * x j
  let s := p40HighResidual fpHi n A x b i
  let M := p40Gamma fpHi.u (n + 1) *
    (|b i| + ∑ j : Fin n, |A i j| * |x j|)
  have hhigh : |s - z| ≤ M := p40_high_error fpHi n A x b hvalid i
  have hstore : |fpLo.fl_mul s 1 - s| ≤ fpLo.u * |s| := by
    simpa using p40_mul_error fpLo s 1
  have hs : |s| ≤ |s - z| + |z| := by
    calc
      |s| = |(s - z) + z| := by ring
      _ ≤ |s - z| + |z| := abs_add_le _ _
  have htri : |fpLo.fl_mul s 1 - z| ≤
      |fpLo.fl_mul s 1 - s| + |s - z| := abs_sub_le _ _ _
  have hmuls := mul_le_mul_of_nonneg_left hs fpLo.u_nonneg
  have hmulh := mul_le_mul_of_nonneg_left hhigh
    (by linarith [fpLo.u_nonneg] : 0 ≤ 1 + fpLo.u)
  have hresult : |fpLo.fl_mul s 1 - z| ≤
      fpLo.u * |z| + (1 + fpLo.u) * M := by
    nlinarith
  simpa only [s, z, M, p40StoredResidual, mul_assoc] using hresult

end VSCLReuse

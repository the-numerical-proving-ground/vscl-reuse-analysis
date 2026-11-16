import VSCLReuse.P40.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p40_mul_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  rw [hfl]
  have heq : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |a * b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

private theorem p40_add_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |a + b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

private theorem p40_sub_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub a b
  rw [hfl]
  have heq : (a - b) * (1 + δ) - (a - b) = (a - b) * δ := by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |a - b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

private theorem p40_valid_mono (u : ℝ) (hu : 0 ≤ u)
    {k l : ℕ} (hkl : k ≤ l) (hvalid : P40GammaValid u l) :
    P40GammaValid u k := by
  unfold P40GammaValid at *
  have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hvalid

private theorem p40_gamma_nonneg (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : P40GammaValid u k) :
    0 ≤ p40Gamma u k := by
  unfold P40GammaValid at hvalid
  unfold p40Gamma
  have hk : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  exact div_nonneg hk (by linarith)

private theorem p40_gamma_step (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : P40GammaValid u (k + 1)) :
    (1 + u) * p40Gamma u k + u ≤ p40Gamma u (k + 1) := by
  unfold P40GammaValid at hvalid
  unfold p40Gamma
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hden₁ : 0 < 1 - (k : ℝ) * u := by
    push_cast at hvalid
    nlinarith
  have hden₂ : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  push_cast at *
  calc
    (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
        (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
          apply (eq_div_iff hden₁.ne').2
          rw [add_mul, mul_assoc, div_mul_cancel₀] <;> try linarith
    _ ≤ (((k : ℝ) + 1) * u) / (1 - ((k : ℝ) + 1) * u) := by
      apply (div_le_div_iff₀ hden₁ hden₂).2
      have hp : 0 ≤ (((k : ℝ) + 1) * u) * u := mul_nonneg (by positivity) hu
      nlinarith


private theorem p40_gamma_ge_u (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hvalid : P40GammaValid u k) :
    u ≤ p40Gamma u k := by
  unfold P40GammaValid at hvalid
  unfold p40Gamma
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd : 0 < 1 - (k : ℝ) * u := by linarith
  apply (le_div_iff₀ hd).2
  have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (by positivity) hu
  nlinarith [mul_nonneg hku hu]

private theorem p40_add_mul_step (fp : P40FPModel)
    (a s W x y : ℝ) (hW : 0 ≤ W) (hs : |s| ≤ W)
    (m : ℕ) (hm : 1 ≤ m) (hvalid : P40GammaValid fp.u (m + 1))
    (ha : |a - s| ≤ p40Gamma fp.u m * W) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      p40Gamma fp.u (m + 1) * (W + |x| * |y|) := by
  let p := fp.fl_mul x y
  let t := x * y
  let r := fp.fl_add a p
  have hp : |p - t| ≤ fp.u * |t| := p40_mul_error fp x y
  have hr : |r - (a + p)| ≤ fp.u * |a + p| := p40_add_error fp a p
  have hmag : |a + p| ≤ |s| + |t| + |a - s| + |p - t| := by
    have heq : a + p = (s + t) + (a - s) + (p - t) := by ring
    rw [heq]
    calc
      |(s + t) + (a - s) + (p - t)| ≤ |s + t| + |a - s| + |p - t| := by
        calc
          _ ≤ |(s + t) + (a - s)| + |p - t| := abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by linarith [abs_add_le s t]
  have herr : |r - (s + t)| ≤ |r - (a + p)| + |a - s| + |p - t| := by
    have heq : r - (s + t) = (r - (a + p)) + (a - s) + (p - t) := by ring
    rw [heq]
    calc
      _ ≤ |(r - (a + p)) + (a - s)| + |p - t| := abs_add_le _ _
      _ ≤ _ := by gcongr; exact abs_add_le _ _
  have hu := fp.u_nonneg
  have hg0 := p40_gamma_nonneg fp.u m hu (by
    unfold P40GammaValid at *
    have hle : (m : ℝ) * fp.u ≤ ((m + 1 : ℕ) : ℝ) * fp.u := by
      push_cast
      nlinarith
    linarith)
  have hge := p40_gamma_ge_u fp.u m hu hm (by
    unfold P40GammaValid at *
    have hle : (m : ℝ) * fp.u ≤ ((m + 1 : ℕ) : ℝ) * fp.u := by
      push_cast
      nlinarith
    linarith)
  have hstep := p40_gamma_step fp.u m hu hvalid
  have hcoeff : 2 * fp.u + fp.u ^ 2 ≤ p40Gamma fp.u (m + 1) := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hge)]
  have hRmag := mul_le_mul_of_nonneg_left hmag hu
  have hPmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1 + fp.u)
  have hAmul := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 1 + fp.u)
  have hstepW := mul_le_mul_of_nonneg_right hstep hW
  have hstepT := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg t)
  have ht : |t| = |x| * |y| := abs_mul x y
  rw [← ht]
  nlinarith

private theorem p40_fold_error (fp : P40FPModel) :
    ∀ (k m : ℕ) (x y : Fin k → ℝ) (a s W : ℝ),
      1 ≤ m → 0 ≤ W → |s| ≤ W →
      P40GammaValid fp.u (m + k) →
      |a - s| ≤ p40Gamma fp.u m * W →
      |Fin.foldl k (fun acc j => fp.fl_add acc (fp.fl_mul (x j) (y j))) a -
        (s + ∑ j : Fin k, x j * y j)| ≤
        p40Gamma fp.u (m + k) *
          (W + ∑ j : Fin k, |x j| * |y j|) := by
  intro k
  induction k with
  | zero =>
      intro m x y a s W hm hW hs hv ha
      simpa using ha
  | succ k ih =>
      intro m x y a s W hm hW hs hv ha
      have hv1 : P40GammaValid fp.u (m + 1) :=
        p40_valid_mono fp.u fp.u_nonneg (by omega : m + 1 ≤ m + (k + 1)) hv
      have hfirst := p40_add_mul_step fp a s W (x 0) (y 0) hW hs m hm hv1 ha
      have hW' : 0 ≤ W + |x 0| * |y 0| := by positivity
      have hs' : |s + x 0 * y 0| ≤ W + |x 0| * |y 0| := by
        calc
          _ ≤ |s| + |x 0 * y 0| := abs_add_le _ _
          _ ≤ _ := by rw [abs_mul]; linarith
      have hv' : P40GammaValid fp.u ((m + 1) + k) := by
        convert hv using 1; omega
      have hrest := ih (m + 1) (fun j => x j.succ) (fun j => y j.succ)
        (fp.fl_add a (fp.fl_mul (x 0) (y 0)))
        (s + x 0 * y 0) (W + |x 0| * |y 0|)
        (by omega) hW' hs' hv' hfirst
      simpa [Fin.foldl_succ, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, add_assoc] using hrest

private theorem p40_dot_error (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P40GammaValid fp.u n) :
    |p40RoundedDotProduct fp n x y - ∑ j : Fin n, x j * y j| ≤
      p40Gamma fp.u n * (∑ j : Fin n, |x j| * |y j|) := by
  cases n with
  | zero =>
      simp [p40RoundedDotProduct]
  | succ n =>
      have hv1 : P40GammaValid fp.u 1 :=
        p40_valid_mono fp.u fp.u_nonneg (by omega : 1 ≤ n + 1) hvalid
      have hγ : fp.u ≤ p40Gamma fp.u 1 :=
        p40_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hv1
      have hbase :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p40Gamma fp.u 1 * (|x 0| * |y 0|) := by
        calc
          _ ≤ fp.u * |x 0 * y 0| := p40_mul_error fp _ _
          _ ≤ _ := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right hγ (by positivity)
      have hfold := p40_fold_error fp n 1
        (fun j => x j.succ) (fun j => y j.succ)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0)
        (|x 0| * |y 0|)
        (by omega) (by positivity) (by rw [abs_mul])
        (by simpa [Nat.add_comm] using hvalid) hbase
      simpa [p40RoundedDotProduct, Fin.sum_univ_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, add_assoc] using hfold

private theorem p40_sub_approx (fp : P40FPModel) (b q v : ℝ) :
    |fp.fl_sub b q - (b - v)| ≤
      fp.u * |b - v| + (1 + fp.u) * |q - v| := by
  have hr := p40_sub_error fp b q
  have hmag : |b - q| ≤ |b - v| + |q - v| := by
    have heq : b - q = (b - v) + (-(q - v)) := by ring
    rw [heq]
    simpa only [abs_neg] using abs_add_le (b - v) (-(q - v))
  have herr : |fp.fl_sub b q - (b - v)| ≤
      |fp.fl_sub b q - (b - q)| + |q - v| := by
    have heq : fp.fl_sub b q - (b - v) =
        (fp.fl_sub b q - (b - q)) + (-(q - v)) := by ring
    rw [heq]
    simpa only [abs_neg] using abs_add_le
      (fp.fl_sub b q - (b - q)) (-(q - v))
  have hmul := mul_le_mul_of_nonneg_left hmag fp.u_nonneg
  nlinarith

private theorem p40_high_residual_error (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fp.u (n + 1)) (i : Fin n) :
    |p40HighResidual fp n A x b i -
      (b i - ∑ j : Fin n, A i j * x j)| ≤
      p40Gamma fp.u (n + 1) *
        (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  let v := ∑ j : Fin n, A i j * x j
  let q := p40RoundedMatVec fp n A x i
  let S := ∑ j : Fin n, |A i j| * |x j|
  let W := |b i| + S
  have hvn : P40GammaValid fp.u n :=
    p40_valid_mono fp.u fp.u_nonneg (by omega : n ≤ n + 1) hvalid
  have hdot : |q - v| ≤ p40Gamma fp.u n * S := by
    simpa [q, v, S, p40RoundedMatVec] using
      p40_dot_error fp n (A i) x hvn
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hSW : S ≤ W := by dsimp [W]; linarith [abs_nonneg (b i)]
  have hvs : |v| ≤ S := by
    simpa only [v, S, abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun j : Fin n => A i j * x j) Finset.univ)
  have hdmag : |b i - v| ≤ W := by
    calc
      _ ≤ |b i| + |v| := by
        simpa only [abs_neg] using abs_add_le (b i) (-v)
      _ ≤ W := by dsimp [W]; linarith
  have hsub : |fp.fl_sub (b i) q - (b i - v)| ≤
      fp.u * |b i - v| + (1 + fp.u) * |q - v| :=
    p40_sub_approx fp (b i) q v
  have hγ := p40_gamma_step fp.u n fp.u_nonneg hvalid
  have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hγ0 := p40_gamma_nonneg fp.u n fp.u_nonneg hvn
  have hdot' := mul_le_mul_of_nonneg_left hdot hu1
  have hSW' := mul_le_mul_of_nonneg_left hSW (mul_nonneg hu1 hγ0)
  have hdmag' := mul_le_mul_of_nonneg_left hdmag fp.u_nonneg
  have hγW := mul_le_mul_of_nonneg_right hγ hW
  dsimp [p40HighResidual]
  dsimp [q, v, S, W] at *
  nlinarith

private theorem p40_storage_approx (fp : P40FPModel) (s d : ℝ) :
    |fp.fl_mul s 1 - d| ≤ fp.u * |d| + (1 + fp.u) * |s - d| := by
  have hr : |fp.fl_mul s 1 - s| ≤ fp.u * |s| := by
    simpa using p40_mul_error fp s 1
  have hmag : |s| ≤ |d| + |s - d| := by
    have heq : s = d + (s - d) := by ring
    conv_lhs => rw [heq]
    exact abs_add_le _ _
  have herr : |fp.fl_mul s 1 - d| ≤
      |fp.fl_mul s 1 - s| + |s - d| := by
    have heq : fp.fl_mul s 1 - d = (fp.fl_mul s 1 - s) + (s - d) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hmag' := mul_le_mul_of_nonneg_left hmag fp.u_nonneg
  nlinarith

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
  let d := b i - ∑ j : Fin n, A i j * x j
  let W := |b i| + ∑ j : Fin n, |A i j| * |x j|
  let s := p40HighResidual fpHi n A x b i
  have hhi : |s - d| ≤ p40Gamma fpHi.u (n + 1) * W := by
    simpa [s, d, W] using p40_high_residual_error fpHi n A x b hvalid i
  have hlo := p40_storage_approx fpLo s d
  have hu1 : 0 ≤ 1 + fpLo.u := by linarith [fpLo.u_nonneg]
  have hhi' := mul_le_mul_of_nonneg_left hhi hu1
  simpa only [p40StoredResidual, s, d, W] using (show
    |fpLo.fl_mul s 1 - d| ≤
      fpLo.u * |d| + (1 + fpLo.u) * p40Gamma fpHi.u (n + 1) * W by
        nlinarith)

end VSCLReuse

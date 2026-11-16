import VSCLReuse.P40.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p40_gamma_nonneg (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : P40GammaValid u k) : 0 ≤ p40Gamma u k := by
  unfold p40Gamma P40GammaValid at *
  have hn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  exact div_nonneg (mul_nonneg hn hu) (le_of_lt (sub_pos.mpr hv))

private theorem p40_gamma_step (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : P40GammaValid u (k + 1)) :
    (1 + u) * p40Gamma u k + u ≤ p40Gamma u (k + 1) := by
  let t : ℝ := (k : ℝ) * u
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hu
  have hv' : t + u < 1 := by
    simpa [P40GammaValid, t, Nat.cast_add, add_mul] using hv
  have hd : 0 < 1 - t := by linarith
  have hd' : 0 < 1 - (t + u) := by linarith
  have hg : 0 ≤ t / (1 - t) := div_nonneg ht (le_of_lt hd)
  have heq : (t / (1 - t)) * (1 - t) = t := div_mul_cancel₀ _ (ne_of_gt hd)
  have hprod : 0 ≤ u * t * (t / (1 - t)) := mul_nonneg (mul_nonneg hu ht) hg
  have hprod' : 0 ≤ u * u * (t / (1 - t)) := mul_nonneg (mul_nonneg hu hu) hg
  have hformula : (1 + u) * (t / (1 - t)) + u ≤
      (t + u) / (1 - (t + u)) := by
    apply (le_div_iff₀ hd').2
    nlinarith [heq, hprod, hprod', mul_nonneg hu ht, mul_nonneg hu hu]
  simpa [p40Gamma, t, Nat.cast_add, add_mul, mul_add] using hformula

private theorem p40_gamma_ge_u (u : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 0 < k) (hv : P40GammaValid u k) :
    u ≤ p40Gamma u k := by
  cases k with
  | zero => omega
  | succ k =>
      have hvk : P40GammaValid u k := by
        unfold P40GammaValid at *
        have hku : (k : ℝ) * u ≤ (↑(k + 1) : ℝ) * u := by
          apply mul_le_mul_of_nonneg_right _ hu
          exact_mod_cast Nat.le_succ k
        linarith
      have hnon : 0 ≤ p40Gamma u k := p40_gamma_nonneg u k hu hvk
      have hstep := p40_gamma_step u k hu hv
      simpa only [Nat.succ_eq_add_one] using
        (le_trans (show u ≤ (1 + u) * p40Gamma u k + u by nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + u) hnon]) hstep)

private theorem p40_mul_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hmodel⟩ := fp.model_mul a b
  rw [hmodel]
  have hident : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [hident, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private theorem p40_sub_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| := by
  obtain ⟨δ, hδ, hmodel⟩ := fp.model_sub a b
  rw [hmodel]
  have hident : (a - b) * (1 + δ) - (a - b) = (a - b) * δ := by ring
  rw [hident, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a - b))

private theorem p40_add_error (fp : P40FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hmodel⟩ := fp.model_add a b
  rw [hmodel]
  have hident : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [hident, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private theorem p40_add_perturbed (fp : P40FPModel) (a b s t : ℝ) :
    |fp.fl_add a b - (s + t)| ≤
      (1 + fp.u) * (|a - s| + |b - t|) + fp.u * (|s| + |t|) := by
  have h₁ : |(a + b) - (s + t)| ≤ |a - s| + |b - t| := by
    convert abs_add_le (a - s) (b - t) using 1 <;> ring
  have h₂ : |a + b| ≤ |s| + |t| + |a - s| + |b - t| := by
    have h := abs_add_le (s + t) ((a - s) + (b - t))
    have hst := abs_add_le s t
    have hab := abs_add_le (a - s) (b - t)
    have heq : s + t + ((a - s) + (b - t)) = a + b := by ring
    rw [heq] at h
    linarith
  have h₃ := p40_add_error fp a b
  have htri : |fp.fl_add a b - (s + t)| ≤
      |fp.fl_add a b - (a + b)| + |(a + b) - (s + t)| := by
    convert abs_add_le (fp.fl_add a b - (a + b)) ((a + b) - (s + t)) using 1 <;> ring
  have hu := fp.u_nonneg
  nlinarith [mul_le_mul_of_nonneg_left h₂ hu]

private theorem p40_sub_perturbed (fp : P40FPModel) (b d s : ℝ) :
    |fp.fl_sub b d - (b - s)| ≤
      (1 + fp.u) * |d - s| + fp.u * (|b| + |s|) := by
  have h₁ : |(b - d) - (b - s)| = |d - s| := by
    have heq : (b - d) - (b - s) = -(d - s) := by ring
    rw [heq, abs_neg]
  have h₂ : |b - d| ≤ |b| + |s| + |d - s| := by
    have heq : b - d = b + -s + -(d - s) := by ring
    rw [heq]
    have h := abs_add_le (b + -s) (-(d - s))
    have h' := abs_add_le b (-s)
    simp only [abs_neg] at h h'
    linarith
  have htri : |fp.fl_sub b d - (b - s)| ≤
      |fp.fl_sub b d - (b - d)| + |(b - d) - (b - s)| := by
    convert abs_add_le (fp.fl_sub b d - (b - d)) ((b - d) - (b - s)) using 1 <;> ring
  have hr := p40_sub_error fp b d
  nlinarith [mul_le_mul_of_nonneg_left h₂ fp.u_nonneg]

private noncomputable def p40Accum (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0

private theorem p40_rounded_eq_accum (fp : P40FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : p40RoundedDotProduct fp n x y = p40Accum fp n x y := by
  cases n with
  | zero => simp [p40RoundedDotProduct, p40Accum]
  | succ n =>
      simp only [p40RoundedDotProduct, p40Accum, Fin.foldl_succ, fp.fl_add_zero]

private theorem p40_valid_le (u : ℝ) (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (hv : P40GammaValid u n) : P40GammaValid u m := by
  unfold P40GammaValid at *
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith [mul_le_mul_of_nonneg_right hmn' hu]

private theorem p40_accum_bound (fp : P40FPModel) :
    ∀ n : ℕ, ∀ (x y : Fin n → ℝ), P40GammaValid fp.u n →
      |p40Accum fp n x y - ∑ i : Fin n, x i * y i| ≤
        p40Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  intro n
  induction n with
  | zero =>
      intro x y hv
      simp [p40Accum, p40Gamma]
  | succ n ih =>
      intro x y hv
      by_cases hn : n = 0
      · subst n
        have hmul := p40_mul_error fp (x 0) (y 0)
        have hge : fp.u ≤ p40Gamma fp.u 1 :=
          p40_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hv
        have hscale := mul_le_mul_of_nonneg_right hge (abs_nonneg (x 0 * y 0))
        simpa [p40Accum, Fin.foldl_succ, fp.fl_add_zero] using le_trans hmul hscale
      · let X : Fin n → ℝ := fun i => x i.castSucc
        let Y : Fin n → ℝ := fun i => y i.castSucc
        let oldR : ℝ := p40Accum fp n X Y
        let oldS : ℝ := ∑ i : Fin n, X i * Y i
        let oldB : ℝ := ∑ i : Fin n, |X i * Y i|
        let t : ℝ := x (Fin.last n) * y (Fin.last n)
        let m : ℝ := fp.fl_mul (x (Fin.last n)) (y (Fin.last n))
        have hvPrev : P40GammaValid fp.u n :=
          p40_valid_le fp.u fp.u_nonneg (Nat.le_succ n) hv
        have hprev : |oldR - oldS| ≤ p40Gamma fp.u n * oldB := ih X Y hvPrev
        have hmul : |m - t| ≤ fp.u * |t| :=
          p40_mul_error fp (x (Fin.last n)) (y (Fin.last n))
        have hS : |oldS| ≤ oldB := by
          simpa [oldS, oldB] using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin n => X i * Y i))
        have hB : 0 ≤ oldB := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have hge : fp.u ≤ p40Gamma fp.u n :=
          p40_gamma_ge_u fp.u n fp.u_nonneg (Nat.pos_of_ne_zero hn) hvPrev
        have hstep : (1 + fp.u) * p40Gamma fp.u n + fp.u ≤
            p40Gamma fp.u (n + 1) := p40_gamma_step fp.u n fp.u_nonneg hv
        have hnew : (1 + fp.u) * fp.u + fp.u ≤ p40Gamma fp.u (n + 1) := by
          nlinarith [mul_le_mul_of_nonneg_left hge (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)]
        have hacc : p40Accum fp (n + 1) x y = fp.fl_add oldR m := by
          simp only [p40Accum, Fin.foldl_succ_last]
          rfl
        have hsum : (∑ i : Fin (n + 1), x i * y i) = oldS + t := by
          simp [Fin.sum_univ_castSucc, oldS, t, X, Y]
        have hsumabs : (∑ i : Fin (n + 1), |x i * y i|) = oldB + |t| := by
          simp [Fin.sum_univ_castSucc, oldB, t, X, Y]
        rw [hacc, hsum, hsumabs]
        have hadd := p40_add_perturbed fp oldR m oldS t
        have h1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        have hA := mul_le_mul_of_nonneg_left hprev h1
        have hM := mul_le_mul_of_nonneg_left hmul h1
        have hS' := mul_le_mul_of_nonneg_left hS fp.u_nonneg
        have hOld := mul_le_mul_of_nonneg_right hstep hB
        have hNew := mul_le_mul_of_nonneg_right hnew (abs_nonneg t)
        nlinarith

private theorem p40_high_bound (fp : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hv : P40GammaValid fp.u (n + 1)) (i : Fin n) :
    |p40HighResidual fp n A x b i -
      (b i - ∑ j : Fin n, A i j * x j)| ≤
      p40Gamma fp.u (n + 1) *
        (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  let d : ℝ := p40RoundedMatVec fp n A x i
  let s : ℝ := ∑ j : Fin n, A i j * x j
  let B : ℝ := ∑ j : Fin n, |A i j * x j|
  have hvPrev : P40GammaValid fp.u n :=
    p40_valid_le fp.u fp.u_nonneg (Nat.le_succ n) hv
  have hdot : |d - s| ≤ p40Gamma fp.u n * B := by
    have h := p40_accum_bound fp n (A i) x hvPrev
    simpa [d, s, B, p40RoundedMatVec, p40_rounded_eq_accum] using h
  have hs : |s| ≤ B := by
    simpa [s, B] using
      (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin n => A i j * x j))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hr := p40_sub_perturbed fp (b i) d s
  have hstep : (1 + fp.u) * p40Gamma fp.u n + fp.u ≤
      p40Gamma fp.u (n + 1) := p40_gamma_step fp.u n fp.u_nonneg hv
  have hge : fp.u ≤ p40Gamma fp.u (n + 1) :=
    p40_gamma_ge_u fp.u (n + 1) fp.u_nonneg (by omega) hv
  have h1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have hdot' := mul_le_mul_of_nonneg_left hdot h1
  have hs' := mul_le_mul_of_nonneg_left hs fp.u_nonneg
  have hstep' := mul_le_mul_of_nonneg_right hstep hB
  have hge' := mul_le_mul_of_nonneg_right hge (abs_nonneg (b i))
  change |fp.fl_sub (b i) d - (b i - s)| ≤
    p40Gamma fp.u (n + 1) *
      (|b i| + ∑ j : Fin n, |A i j| * |x j|)
  have hB' : B = ∑ j : Fin n, |A i j| * |x j| := by
    simp [B, abs_mul]
  rw [← hB']
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
  let s : ℝ := p40HighResidual fpHi n A x b i
  let t : ℝ := b i - ∑ j : Fin n, A i j * x j
  let B : ℝ := |b i| + ∑ j : Fin n, |A i j| * |x j|
  have hhigh : |s - t| ≤ p40Gamma fpHi.u (n + 1) * B := by
    simpa [s, t, B] using p40_high_bound fpHi n A x b hvalid i
  have hstore : |p40StoredResidual fpHi fpLo n A x b i - s| ≤ fpLo.u * |s| := by
    simpa [p40StoredResidual, s] using (p40_mul_error fpLo s 1)
  have hs : |s| ≤ |t| + |s - t| := by
    have heq : s = t + (s - t) := by ring
    calc
      |s| = |t + (s - t)| := congrArg abs heq
      _ ≤ |t| + |s - t| := abs_add_le t (s - t)
  have htri : |p40StoredResidual fpHi fpLo n A x b i - t| ≤
      |p40StoredResidual fpHi fpLo n A x b i - s| + |s - t| := by
    convert abs_add_le
      (p40StoredResidual fpHi fpLo n A x b i - s) (s - t) using 1 <;> ring
  have hs' := mul_le_mul_of_nonneg_left hs fpLo.u_nonneg
  have h1 : 0 ≤ 1 + fpLo.u := by linarith [fpLo.u_nonneg]
  have hhigh' := mul_le_mul_of_nonneg_left hhigh h1
  change |p40StoredResidual fpHi fpLo n A x b i - t| ≤
    fpLo.u * |t| + (1 + fpLo.u) * p40Gamma fpHi.u (n + 1) * B
  nlinarith

end VSCLReuse

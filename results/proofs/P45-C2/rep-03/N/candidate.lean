import VSCLReuse.P45.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p45_gamma_lower (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hv : P45GammaValid u k) : u ≤ p45Gamma u k := by
  have hpos : 0 < 1 - (k : ℝ) * u := by
    change (k : ℝ) * u < 1 at hv
    linarith
  unfold p45Gamma
  apply (le_div_iff₀ hpos).2
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknonneg : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  nlinarith [mul_nonneg hknonneg hu]

private lemma p45_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hv : P45GammaValid u (k + 1)) :
    0 ≤ p45Gamma u k ∧
    (1 + u) * p45Gamma u k + u ≤ p45Gamma u (k + 1) ∧
    (1 + u) * u + u ≤ p45Gamma u (k + 1) := by
  have hku : (k : ℝ) * u < 1 := by
    have : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      push_cast
      nlinarith
    exact lt_of_le_of_lt this hv
  have hkpos : 0 < 1 - (k : ℝ) * u := by linarith
  have hnext : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    change ((k + 1 : ℕ) : ℝ) * u < 1 at hv
    linarith
  have hknonneg : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hkg : 0 ≤ p45Gamma u k := by
    unfold p45Gamma
    positivity
  have hbase : u ≤ p45Gamma u k := by
    unfold p45Gamma
    apply (le_div_iff₀ hkpos).2
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hknonneg hu]
  have hrec : (1 + u) * p45Gamma u k + u ≤ p45Gamma u (k + 1) := by
    unfold p45Gamma
    have heq : (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
        ((k + 1 : ℕ) : ℝ) * u / (1 - (k : ℝ) * u) := by
      push_cast
      field_simp [show 1 - u * (k : ℝ) ≠ 0 by nlinarith [hkpos]]
      ring
    rw [heq]
    apply (div_le_div_iff₀ hkpos hnext).2
    push_cast
    nlinarith [mul_nonneg ((add_nonneg hknonneg hu)) hu]
  exact ⟨hkg, hrec, by nlinarith [mul_nonneg hu (sub_nonneg.mpr hbase)]⟩

private lemma p45_mul_error (fp : P45FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

private lemma p45_add_error (fp : P45FPModel) (x y x₀ y₀ : ℝ) :
    |fp.fl_add x y - (x₀ + y₀)| ≤
      ((1 + fp.u) * |x - x₀| + fp.u * |x₀|) +
      ((1 + fp.u) * |y - y₀| + fp.u * |y₀|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  have h1 : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have heq : (x + y) * (1 + δ) - (x₀ + y₀) =
      ((x - x₀) + (y - y₀)) * (1 + δ) + δ * (x₀ + y₀) := by ring
  rw [hfl, heq]
  calc
    |((x - x₀) + (y - y₀)) * (1 + δ) + δ * (x₀ + y₀)|
        ≤ |((x - x₀) + (y - y₀)) * (1 + δ)| + |δ * (x₀ + y₀)| :=
          abs_add_le _ _
    _ = |(x - x₀) + (y - y₀)| * |1 + δ| + |δ| * |x₀ + y₀| := by
      rw [abs_mul, abs_mul]
    _ ≤ (|x - x₀| + |y - y₀|) * (1 + fp.u) +
        fp.u * (|x₀| + |y₀|) := by
      apply add_le_add
      · exact mul_le_mul (abs_add_le _ _) h1 (abs_nonneg _)
          (by positivity)
      · exact mul_le_mul hδ (abs_add_le _ _) (abs_nonneg _)
          fp.u_nonneg
    _ = ((1 + fp.u) * |x - x₀| + fp.u * |x₀|) +
        ((1 + fp.u) * |y - y₀| + fp.u * |y₀|) := by ring

private lemma p45_fold_error (fp : P45FPModel) (m : ℕ)
    (v w : Fin m → ℝ) (z z₀ : ℝ)
    (hz : |z - z₀| ≤ fp.u * |z₀|)
    (hvw : ∀ i, |v i - w i| ≤ fp.u * |w i|)
    (hv : P45GammaValid fp.u (m + 1)) :
    |Fin.foldl m (fun acc i => fp.fl_add acc (v i)) z -
        (z₀ + ∑ i : Fin m, w i)| ≤
      p45Gamma fp.u (m + 1) * (|z₀| + ∑ i : Fin m, |w i|) := by
  induction m with
  | zero =>
      simp only [Fin.foldl_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact hz.trans (mul_le_mul_of_nonneg_right
        (p45_gamma_lower fp.u 1 fp.u_nonneg (by omega) hv) (abs_nonneg _))
  | succ m ih =>
      let v' : Fin m → ℝ := fun i => v i.castSucc
      let w' : Fin m → ℝ := fun i => w i.castSucc
      have hv' : P45GammaValid fp.u (m + 1) := by
        change ((m + 1 : ℕ) : ℝ) * fp.u < 1
        change ((m + 1 + 1 : ℕ) : ℝ) * fp.u < 1 at hv
        push_cast at *
        nlinarith [fp.u_nonneg]
      have hprev := ih v' w' (fun i => hvw i.castSucc) hv'
      have hsum : |z₀ + ∑ i : Fin m, w' i| ≤
          |z₀| + ∑ i : Fin m, |w' i| := by
        calc
          |z₀ + ∑ i : Fin m, w' i| ≤ |z₀| + |∑ i : Fin m, w' i| :=
            abs_add_le _ _
          _ ≤ |z₀| + ∑ i : Fin m, |w' i| := by
            gcongr
            simpa using Finset.abs_sum_le_sum_abs w' Finset.univ
      have hS : 0 ≤ |z₀| + ∑ i : Fin m, |w' i| := by positivity
      have hg := p45_gamma_step fp.u (m + 1) fp.u_nonneg (by omega) hv
      have hadd := p45_add_error fp
        (Fin.foldl m (fun acc i => fp.fl_add acc (v' i)) z)
        (v (Fin.last m))
        (z₀ + ∑ i : Fin m, w' i) (w (Fin.last m))
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        Fin.sum_univ_castSucc]
      simp only [← add_assoc]
      change |fp.fl_add
          (Fin.foldl m (fun acc i => fp.fl_add acc (v' i)) z)
          (v (Fin.last m)) -
        ((z₀ + ∑ i : Fin m, w' i) + w (Fin.last m))| ≤
        p45Gamma fp.u (m + 1 + 1) *
          ((|z₀| + ∑ i : Fin m, |w' i|) + |w (Fin.last m)|)
      calc
        _ ≤ ((1 + fp.u) *
            |Fin.foldl m (fun acc i => fp.fl_add acc (v' i)) z -
              (z₀ + ∑ i : Fin m, w' i)| +
            fp.u * |z₀ + ∑ i : Fin m, w' i|) +
            ((1 + fp.u) * |v (Fin.last m) - w (Fin.last m)| +
              fp.u * |w (Fin.last m)|) := hadd
        _ ≤ ((1 + fp.u) * p45Gamma fp.u (m + 1) + fp.u) *
            (|z₀| + ∑ i : Fin m, |w' i|) +
            ((1 + fp.u) * fp.u + fp.u) * |w (Fin.last m)| := by
          have hnonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hA : (1 + fp.u) *
              |Fin.foldl m (fun acc i => fp.fl_add acc (v' i)) z -
                (z₀ + ∑ i : Fin m, w' i)| +
              fp.u * |z₀ + ∑ i : Fin m, w' i| ≤
              ((1 + fp.u) * p45Gamma fp.u (m + 1) + fp.u) *
                (|z₀| + ∑ i : Fin m, |w' i|) := by
            calc
              _ ≤ (1 + fp.u) * (p45Gamma fp.u (m + 1) *
                    (|z₀| + ∑ i : Fin m, |w' i|)) +
                    fp.u * (|z₀| + ∑ i : Fin m, |w' i|) :=
                  add_le_add (mul_le_mul_of_nonneg_left hprev hnonneg)
                    (mul_le_mul_of_nonneg_left hsum fp.u_nonneg)
              _ = _ := by ring
          have hB : (1 + fp.u) * |v (Fin.last m) - w (Fin.last m)| +
              fp.u * |w (Fin.last m)| ≤
              ((1 + fp.u) * fp.u + fp.u) * |w (Fin.last m)| := by
            calc
              _ ≤ (1 + fp.u) * (fp.u * |w (Fin.last m)|) +
                  fp.u * |w (Fin.last m)| :=
                    add_le_add_left
                      (mul_le_mul_of_nonneg_left (hvw (Fin.last m)) hnonneg) _
              _ = _ := by ring
          exact add_le_add hA hB
        _ ≤ p45Gamma fp.u (m + 1 + 1) *
            (|z₀| + ∑ i : Fin m, |w' i|) +
            p45Gamma fp.u (m + 1 + 1) * |w (Fin.last m)| := by
          exact add_le_add (mul_le_mul_of_nonneg_right hg.2.1 hS)
            (mul_le_mul_of_nonneg_right hg.2.2 (abs_nonneg _))
        _ = _ := by ring

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  cases n with
  | zero =>
      simp [p45BlockDot]
  | succ m =>
      have h := p45_fold_error fp m
        (fun i : Fin m => fp.fl_mul (a i.succ) (x i.succ))
        (fun i : Fin m => a i.succ * x i.succ)
        (fp.fl_mul (a 0) (x 0)) (a 0 * x 0)
        (p45_mul_error fp (a 0) (x 0))
        (fun i => p45_mul_error fp (a i.succ) (x i.succ)) hv
      simpa only [p45BlockDot, Fin.sum_univ_succ] using h

end VSCLReuse

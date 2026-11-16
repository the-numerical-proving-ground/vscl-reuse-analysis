import VSCLReuse.P20.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p20_step_bound
    (u q z M t r d : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hM : |z| ≤ M)
    (hq : |q - z| ≤ ((1 + u) ^ k - 1) * M)
    (hr : |r - t| ≤ u * |t|) (hd : |d| ≤ u) :
    |(q + r) * (1 + d) - (z + t)| ≤
      ((1 + u) ^ (k + 1) - 1) * (M + |t|) := by
  have hbase : 1 ≤ 1 + u := by linarith
  have hpow2 : (1 + u) ^ 2 ≤ (1 + u) ^ (k + 1) :=
    pow_le_pow_right₀ hbase (by omega)
  have hcoef : u * (2 + u) ≤ (1 + u) ^ (k + 1) - 1 := by
    nlinarith [hpow2]
  have hcoef_t := mul_le_mul_of_nonneg_right hcoef (abs_nonneg t)
  have hM0 : 0 ≤ M := (abs_nonneg z).trans hM
  have hqr : |q + r| ≤ |q - z| + M + |r - t| + |t| := by
    calc
      |q + r| = |((q - z) + z) + ((r - t) + t)| := by congr 1; ring
      _ ≤ |(q - z) + z| + |(r - t) + t| := abs_add_le _ _
      _ ≤ |q - z| + M + |r - t| + |t| := by
        linarith [abs_add_le (q - z) z, abs_add_le (r - t) t]
  have herr : |(q + r) * (1 + d) - (z + t)| ≤
      |q - z| + |r - t| + |q + r| * |d| := by
    calc
      |(q + r) * (1 + d) - (z + t)| =
          |((q - z) + (r - t)) + (q + r) * d| := by congr 1; ring
      _ ≤ |(q - z) + (r - t)| + |(q + r) * d| := abs_add_le _ _
      _ ≤ |q - z| + |r - t| + |q + r| * |d| := by
        rw [abs_mul]
        linarith [abs_add_le (q - z) (r - t)]
  have hmul : |q + r| * |d| ≤
      (|q - z| + M + |r - t| + |t|) * u := by
    exact mul_le_mul hqr hd (abs_nonneg d) (by positivity)
  have hq' := mul_le_mul_of_nonneg_left hq (by linarith : 0 ≤ 1 + u)
  have hr' := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1 + u)
  calc
    |(q + r) * (1 + d) - (z + t)| ≤
        (1 + u) * (((1 + u) ^ k - 1) * M) + u * M +
          (1 + u) * (u * |t|) + u * |t| := by
            nlinarith [herr, hmul, hq', hr']
    _ = ((1 + u) ^ (k + 1) - 1) * M + (u * (2 + u)) * |t| := by
      rw [pow_succ]
      ring
    _ ≤ ((1 + u) ^ (k + 1) - 1) * (M + |t|) := by
      nlinarith [hcoef_t]

private theorem p20_fold_bound (fp : P20FPModel) (n : ℕ) :
    ∀ (k : ℕ) (t r : Fin n → ℝ) (q z M : ℝ),
      1 ≤ k → |z| ≤ M →
      |q - z| ≤ ((1 + fp.u) ^ k - 1) * M →
      (∀ j, |r j - t j| ≤ fp.u * |t j|) →
      |Fin.foldl n (fun acc j ↦ fp.fl_add acc (r j)) q -
          (z + ∑ j : Fin n, t j)| ≤
        ((1 + fp.u) ^ (k + n) - 1) *
          (M + ∑ j : Fin n, |t j|) := by
  induction n with
  | zero =>
      intro k t r q z M hk hM hq hr
      simpa using hq
  | succ n ih =>
      intro k t r q z M hk hM hq hr
      obtain ⟨d, hd, heq⟩ := fp.model_add q (r 0)
      have hstep : |fp.fl_add q (r 0) - (z + t 0)| ≤
          ((1 + fp.u) ^ (k + 1) - 1) * (M + |t 0|) := by
        rw [heq]
        exact p20_step_bound fp.u q z M (t 0) (r 0) d k
          fp.u_nonneg hk hM hq (hr 0) hd
      have hM' : |z + t 0| ≤ M + |t 0| := by
        linarith [abs_add_le z (t 0)]
      have hrest := ih (k + 1) (fun j ↦ t j.succ) (fun j ↦ r j.succ)
        (fp.fl_add q (r 0)) (z + t 0) (M + |t 0|)
        (by omega) hM' hstep (fun j ↦ hr j.succ)
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, add_assoc,
        Nat.add_assoc, Nat.add_comm 1 n] using hrest

private theorem p20_mul_bound (fp : P20FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * |a * x| := by
  obtain ⟨d, hd, heq⟩ := fp.model_mul a x
  rw [heq, show (a * x) * (1 + d) - a * x = (a * x) * d by ring, abs_mul]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hd (abs_nonneg (a * x)))

private theorem p20_dot_power_bound (fp : P20FPModel) (s : ℕ)
    (a x : Fin s → ℝ) :
    |p20RoundedSparseRowProduct fp s a x - ∑ j : Fin s, a j * x j| ≤
      ((1 + fp.u) ^ s - 1) * ∑ j : Fin s, |a j| * |x j| := by
  cases s with
  | zero =>
      simp [p20RoundedSparseRowProduct]
  | succ n =>
      have hfirst := p20_mul_bound fp (a 0) (x 0)
      have hfold := p20_fold_bound fp n 1
        (fun j ↦ a j.succ * x j.succ)
        (fun j ↦ fp.fl_mul (a j.succ) (x j.succ))
        (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) |a 0 * x 0|
        (by omega) (le_refl _)
        (by simpa using hfirst)
        (fun j ↦ p20_mul_bound fp (a j.succ) (x j.succ))
      simpa only [p20RoundedSparseRowProduct, Fin.sum_univ_succ,
        pow_one, add_sub_cancel_left, Nat.add_comm 1 n, abs_mul] using hfold

private theorem p20_sub_bound (fp : P20FPModel) (b q : ℝ) :
    |fp.fl_sub b q - (b - q)| ≤ fp.u * |b - q| := by
  obtain ⟨d, hd, heq⟩ := fp.model_sub b q
  rw [heq, show (b - q) * (1 + d) - (b - q) = (b - q) * d by ring, abs_mul]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hd (abs_nonneg (b - q)))

private theorem p20_residual_power_bound (fp : P20FPModel) (s : ℕ)
    (a x : Fin s → ℝ) (b : ℝ) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      ((1 + fp.u) ^ (s + 1) - 1) *
        (|b| + ∑ j : Fin s, |a j| * |x j|) := by
  let M : ℝ := ∑ j : Fin s, |a j| * |x j|
  have hS : |∑ j : Fin s, a j * x j| ≤ M := by
    simpa only [M, abs_mul] using
      (Finset.abs_sum_le_sum_abs (fun j : Fin s ↦ a j * x j) Finset.univ)
  cases s with
  | zero =>
      have hb := p20_sub_bound fp b 0
      simpa [p20RoundedResidual, p20RoundedSparseRowProduct,
        p20ExactResidual, M] using hb
  | succ n =>
      let q := p20RoundedSparseRowProduct fp (n + 1) a x
      let z := ∑ j : Fin (n + 1), a j * x j
      have hdot : |q - z| ≤ ((1 + fp.u) ^ (n + 1) - 1) * M :=
        p20_dot_power_bound fp (n + 1) a x
      obtain ⟨d, hd, heq⟩ := fp.model_sub b q
      have hstep := p20_step_bound fp.u (-q) (-z) M b b d (n + 1)
        fp.u_nonneg (by omega) (by simpa only [abs_neg] using hS)
        (by simpa only [neg_sub_neg, abs_sub_comm] using hdot)
        (by simpa only [sub_self, abs_zero] using
          (mul_nonneg fp.u_nonneg (abs_nonneg b))) hd
      change |fp.fl_sub b q - (b - z)| ≤
        ((1 + fp.u) ^ ((n + 1) + 1) - 1) * (|b| + M)
      rw [heq]
      rw [show -q + b = b - q by ring,
        show -z + b = b - z by ring,
        add_comm M |b|] at hstep
      exact hstep

private theorem p20_pow_gap_le_one (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    P20GammaValid u n →
      (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero =>
      intro hv
      norm_num
  | succ n ih =>
      intro hv
      have hvn : P20GammaValid u n := by
        unfold P20GammaValid at hv ⊢
        push_cast at hv
        nlinarith
      have hfactor :
          (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
            1 - (n : ℝ) * u := by
        push_cast
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [mul_nonneg hn (sq_nonneg u)]
      have hmult := mul_le_mul_of_nonneg_left hfactor
        (pow_nonneg (by linarith : 0 ≤ 1 + u) n)
      calc
        (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ n * ((1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]
              ring
        _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) := by
          simpa only [mul_comm] using hmult
        _ ≤ 1 := ih hvn

private theorem p20_power_le_gamma (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P20GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p20Gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    unfold P20GammaValid at hv
    linarith
  have hpow := p20_pow_gap_le_one u hu n hv
  unfold p20Gamma
  apply (le_div_iff₀ hden).2
  nlinarith [hpow]

/-- P20-C2: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p20_c2_sparse_residual_error
    (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P20GammaValid fp.u (s + 1)) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      p20ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P20-C2-H001
  have hpower := p20_residual_power_bound fp s a x b
  have hgamma := p20_power_le_gamma fp.u (s + 1) fp.u_nonneg hvalid
  have hweight : 0 ≤ |b| + ∑ j : Fin s, |a j| * |x j| := by
    apply add_nonneg (abs_nonneg b)
    exact Finset.sum_nonneg (fun j hj ↦ mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hscaled := mul_le_mul_of_nonneg_right hgamma hweight
  exact hpower.trans (by simpa only [p20ResidualErrorMajorant] using hscaled)

end VSCLReuse

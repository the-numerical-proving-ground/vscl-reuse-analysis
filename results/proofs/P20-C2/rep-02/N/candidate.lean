import VSCLReuse.P20.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p20_valid_mono {u : ℝ} (hu : 0 ≤ u) {n m : ℕ}
    (hnm : n ≤ m) (hm : P20GammaValid u m) : P20GammaValid u n := by
  unfold P20GammaValid at *
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hm

private theorem p20_gamma_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (hn : P20GammaValid u n) : 0 ≤ p20Gamma u n := by
  unfold p20Gamma P20GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private theorem p20_gamma_ge_u {u : ℝ} (hu : 0 ≤ u) (k : ℕ)
    (hk : 1 ≤ k) (hvalid : P20GammaValid u k) : u ≤ p20Gamma u k := by
  unfold p20Gamma P20GammaValid at *
  have hden : 0 < 1 - (k : ℝ) * u := by linarith
  rw [le_div_iff₀ hden]
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [mul_nonneg (sub_nonneg.mpr hk') hu, sq_nonneg u,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sq_nonneg u)]

private theorem p20_gamma_step {u : ℝ} (hu : 0 ≤ u) (k : ℕ)
    (hvalid : P20GammaValid u (k + 1)) :
    (1 + u) * p20Gamma u k + u ≤ p20Gamma u (k + 1) := by
  have hk := p20_valid_mono hu (Nat.le_succ k) hvalid
  have hd0 : 0 < 1 - (k : ℝ) * u := by unfold P20GammaValid at hk; linarith
  have hd1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold P20GammaValid at hvalid
    linarith
  have hN : 0 ≤ (((k + 1 : ℕ) : ℝ) * u) := by positivity
  have hD : 1 - ((k + 1 : ℕ) : ℝ) * u ≤ 1 - (k : ℝ) * u := by
    push_cast
    nlinarith
  have heq : (1 + u) * p20Gamma u k + u =
      (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    unfold p20Gamma
    push_cast
    have hd0' : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hd0]
    field_simp [ne_of_gt hd0, hd0']
    ring
  rw [heq]
  unfold p20Gamma
  apply (le_div_iff₀ hd1).2
  calc
    (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) *
        (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
        (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) *
        (1 - (k : ℝ) * u) :=
      mul_le_mul_of_nonneg_left hD (div_nonneg hN hd0.le)
    _ = (((k + 1 : ℕ) : ℝ) * u) := div_mul_cancel₀ _ hd0.ne'

private theorem p20_round_bound (u z t δ : ℝ) (hu : 0 ≤ u)
    (hδ : |δ| ≤ u) :
    |z * (1 + δ) - t| ≤ (1 + u) * |z - t| + u * |t| := by
  have heq : z * (1 + δ) - t = (z - t) * (1 + δ) + t * δ := by ring
  rw [heq]
  have hfac : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  calc
    |(z - t) * (1 + δ) + t * δ| ≤
        |(z - t) * (1 + δ)| + |t * δ| := abs_add_le _ _
    _ = |z - t| * |1 + δ| + |t| * |δ| := by rw [abs_mul, abs_mul]
    _ ≤ |z - t| * (1 + u) + |t| * u :=
      add_le_add (mul_le_mul_of_nonneg_left hfac (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hδ (abs_nonneg _))
    _ = (1 + u) * |z - t| + u * |t| := by ring

private theorem p20_mul_error (fp : P20FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * |a * x| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a x
  rw [hfl]
  have heq : (a * x) * (1 + δ) - a * x = (a * x) * δ := by ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * x))]

private theorem p20_add_step (fp : P20FPModel) (k : ℕ) (q t M v m : ℝ)
    (hk : 1 ≤ k) (hvalid : P20GammaValid fp.u (k + 1))
    (hM : 0 ≤ M) (ht : |t| ≤ M)
    (hq : |q - t| ≤ p20Gamma fp.u k * M)
    (hm : |m - v| ≤ fp.u * |v|) :
    |fp.fl_add q m - (t + v)| ≤
      p20Gamma fp.u (k + 1) * (M + |v|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add q m
  have hinput : |q + m - (t + v)| ≤ |q - t| + |m - v| := by
    convert abs_add_le (q - t) (m - v) using 1 <;> ring
  have htv : |t + v| ≤ M + |v| := by linarith [abs_add_le t v]
  have hgamma := p20_gamma_step fp.u_nonneg k hvalid
  have hkvalid := p20_valid_mono fp.u_nonneg (Nat.le_succ k) hvalid
  have hge := p20_gamma_ge_u fp.u_nonneg k hk hkvalid
  have hcoef : fp.u * (2 + fp.u) ≤ p20Gamma fp.u (k + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hge (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
    nlinarith
  have hnonneg : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  rw [hfl]
  calc
    |(q + m) * (1 + δ) - (t + v)| ≤
        (1 + fp.u) * |q + m - (t + v)| + fp.u * |t + v| :=
      p20_round_bound fp.u (q + m) (t + v) δ fp.u_nonneg hδ
    _ ≤ (1 + fp.u) * (|q - t| + |m - v|) + fp.u * (M + |v|) :=
      add_le_add (mul_le_mul_of_nonneg_left hinput hnonneg)
        (mul_le_mul_of_nonneg_left htv fp.u_nonneg)
    _ ≤ (1 + fp.u) * (p20Gamma fp.u k * M + fp.u * |v|) +
        fp.u * (M + |v|) := by
      gcongr
    _ = ((1 + fp.u) * p20Gamma fp.u k + fp.u) * M +
          (fp.u * (2 + fp.u)) * |v| := by ring
    _ ≤ p20Gamma fp.u (k + 1) * M +
          p20Gamma fp.u (k + 1) * |v| :=
      add_le_add (mul_le_mul_of_nonneg_right hgamma hM)
        (mul_le_mul_of_nonneg_right hcoef (abs_nonneg v))
    _ = p20Gamma fp.u (k + 1) * (M + |v|) := by ring

private theorem p20_fold_error (fp : P20FPModel) (n : ℕ)
    (v m : Fin n → ℝ) (k : ℕ) (q t M : ℝ)
    (hk : 1 ≤ k) (hvalid : P20GammaValid fp.u (k + n))
    (hM : 0 ≤ M) (ht : |t| ≤ M)
    (hq : |q - t| ≤ p20Gamma fp.u k * M)
    (hm : ∀ j, |m j - v j| ≤ fp.u * |v j|) :
    |Fin.foldl n (fun acc j => fp.fl_add acc (m j)) q -
        (t + ∑ j : Fin n, v j)| ≤
      p20Gamma fp.u (k + n) * (M + ∑ j : Fin n, |v j|) := by
  induction n generalizing k q t M with
  | zero =>
      simpa using hq
  | succ n ih =>
      have hvalid_step : P20GammaValid fp.u (k + 1) :=
        p20_valid_mono fp.u_nonneg (by omega : k + 1 ≤ k + (n + 1)) hvalid
      have hstep := p20_add_step fp k q t M (v 0) (m 0) hk hvalid_step
        hM ht hq (hm 0)
      have hM' : 0 ≤ M + |v 0| := add_nonneg hM (abs_nonneg _)
      have ht' : |t + v 0| ≤ M + |v 0| := by
        linarith [abs_add_le t (v 0)]
      have hvalid' : P20GammaValid fp.u ((k + 1) + n) := by
        convert hvalid using 1 <;> omega
      have hm' : ∀ j : Fin n,
          |m j.succ - v j.succ| ≤ fp.u * |v j.succ| := fun j => hm j.succ
      have hrec := ih (fun j : Fin n => v j.succ)
        (fun j : Fin n => m j.succ) (k + 1)
        (fp.fl_add q (m 0)) (t + v 0) (M + |v 0|)
        (by omega : 1 ≤ k + 1) hvalid' hM' ht' hstep hm'
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, Nat.add_assoc,
        Nat.add_comm 1 n,
        add_assoc] using hrec

private theorem p20_row_error (fp : P20FPModel) (s : ℕ)
    (a x : Fin s → ℝ) (hvalid : P20GammaValid fp.u s) :
    |p20RoundedSparseRowProduct fp s a x - ∑ j : Fin s, a j * x j| ≤
      p20Gamma fp.u s * ∑ j : Fin s, |a j * x j| := by
  cases s with
  | zero =>
      simp [p20RoundedSparseRowProduct]
  | succ n =>
      have hvalid' : P20GammaValid fp.u (1 + n) := by
        convert hvalid using 1 <;> omega
      have hstart :
          |fp.fl_mul (a 0) (x 0) - a 0 * x 0| ≤
            p20Gamma fp.u 1 * |a 0 * x 0| := by
        calc
          _ ≤ fp.u * |a 0 * x 0| := p20_mul_error fp _ _
          _ ≤ p20Gamma fp.u 1 * |a 0 * x 0| :=
            mul_le_mul_of_nonneg_right
              (p20_gamma_ge_u fp.u_nonneg 1 (by omega) (p20_valid_mono fp.u_nonneg
                (by omega : 1 ≤ n + 1) hvalid)) (abs_nonneg _)
      have hrec := p20_fold_error fp n
        (fun j : Fin n => a j.succ * x j.succ)
        (fun j : Fin n => fp.fl_mul (a j.succ) (x j.succ))
        1 (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) |a 0 * x 0|
        (by omega) hvalid' (abs_nonneg _) le_rfl hstart
        (fun j => p20_mul_error fp _ _)
      simpa only [p20RoundedSparseRowProduct, Fin.sum_univ_succ,
        Nat.add_comm 1 n, add_assoc] using hrec

/-- P20-C2: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p20_c2_sparse_residual_error
    (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P20GammaValid fp.u (s + 1)) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      p20ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P20-C2-H001
  let q := p20RoundedSparseRowProduct fp s a x
  let t := ∑ j : Fin s, a j * x j
  let A := ∑ j : Fin s, |a j * x j|
  have hvalid_row : P20GammaValid fp.u s :=
    p20_valid_mono fp.u_nonneg (by omega : s ≤ s + 1) hvalid
  have hrow : |q - t| ≤ p20Gamma fp.u s * A :=
    p20_row_error fp s a x hvalid_row
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have ht : |t| ≤ A := by
    dsimp [t, A]
    simpa using (Finset.abs_sum_le_sum_abs (fun j : Fin s => a j * x j) Finset.univ)
  have hbt : |b - t| ≤ |b| + A := by
    calc
      |b - t| = |b + -t| := by ring
      _ ≤ |b| + |-t| := abs_add_le _ _
      _ = |b| + |t| := by rw [abs_neg]
      _ ≤ |b| + A := by linarith
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub b q
  have hgamma := p20_gamma_step fp.u_nonneg s hvalid
  have hgu := p20_gamma_ge_u fp.u_nonneg (s + 1)
    (by omega : 1 ≤ s + 1) hvalid
  have hres : |fp.fl_sub b q - (b - t)| ≤
      p20Gamma fp.u (s + 1) * (|b| + A) := by
    have hinput : |(b - q) - (b - t)| = |q - t| := by
      have heq : (b - q) - (b - t) = t - q := by ring
      rw [heq, abs_sub_comm]
    rw [hfl]
    calc
      |(b - q) * (1 + δ) - (b - t)| ≤
          (1 + fp.u) * |(b - q) - (b - t)| + fp.u * |b - t| :=
        p20_round_bound fp.u (b - q) (b - t) δ fp.u_nonneg hδ
      _ ≤ (1 + fp.u) * (p20Gamma fp.u s * A) +
            fp.u * (|b| + A) := by
        rw [hinput]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hrow (by linarith [fp.u_nonneg]))
          (mul_le_mul_of_nonneg_left hbt fp.u_nonneg)
      _ = ((1 + fp.u) * p20Gamma fp.u s + fp.u) * A + fp.u * |b| := by ring
      _ ≤ p20Gamma fp.u (s + 1) * A +
            p20Gamma fp.u (s + 1) * |b| :=
        add_le_add (mul_le_mul_of_nonneg_right hgamma hA)
          (mul_le_mul_of_nonneg_right hgu (abs_nonneg b))
      _ = p20Gamma fp.u (s + 1) * (|b| + A) := by ring
  simpa [p20RoundedResidual, p20ExactResidual,
    p20ResidualErrorMajorant, q, t, A, abs_mul] using hres

end VSCLReuse

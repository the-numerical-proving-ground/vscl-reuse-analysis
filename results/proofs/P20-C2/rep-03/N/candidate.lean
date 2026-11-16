import VSCLReuse.P20.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p20_mul_error (fp : P20FPModel) (v w : ℝ) :
    |fp.fl_mul v w - v * w| ≤ fp.u * |v * w| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul v w
  rw [hfl]
  have heq : (v * w) * (1 + δ) - v * w = (v * w) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (v * w))

private theorem p20_add_error (fp : P20FPModel) (v w V W : ℝ) :
    |fp.fl_add v w - (V + W)| ≤
      (1 + fp.u) * (|v - V| + |w - W|) + fp.u * (|V| + |W|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add v w
  rw [hfl]
  have heq : (v + w) * (1 + δ) - (V + W) =
      ((v - V) + (w - W)) * (1 + δ) + (V + W) * δ := by ring
  rw [heq]
  calc
    |((v - V) + (w - W)) * (1 + δ) + (V + W) * δ| ≤
        |((v - V) + (w - W)) * (1 + δ)| + |(V + W) * δ| := abs_add_le _ _
    _ = |(v - V) + (w - W)| * |1 + δ| + |V + W| * |δ| := by rw [abs_mul, abs_mul]
    _ ≤ (|v - V| + |w - W|) * (1 + fp.u) + (|V| + |W|) * fp.u := by
      gcongr
      · exact abs_add_le _ _
      · calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      · exact abs_add_le _ _
    _ = _ := by ring

private theorem p20_sub_error (fp : P20FPModel) (v w V W : ℝ) :
    |fp.fl_sub v w - (V - W)| ≤
      (1 + fp.u) * (|v - V| + |w - W|) + fp.u * (|V| + |W|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_sub v w
  rw [hfl]
  have heq : (v - w) * (1 + δ) - (V - W) =
      ((v - V) - (w - W)) * (1 + δ) + (V - W) * δ := by ring
  rw [heq]
  calc
    |((v - V) - (w - W)) * (1 + δ) + (V - W) * δ| ≤
        |((v - V) - (w - W)) * (1 + δ)| + |(V - W) * δ| := abs_add_le _ _
    _ = |(v - V) - (w - W)| * |1 + δ| + |V - W| * |δ| := by rw [abs_mul, abs_mul]
    _ ≤ (|v - V| + |w - W|) * (1 + fp.u) + (|V| + |W|) * fp.u := by
      gcongr
      · exact abs_sub _ _
      · calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      · exact abs_sub _ _
    _ = _ := by ring

private theorem p20_pow_factor (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
    have hs : (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
        1 - (n : ℝ) * u := by
      have h : 0 ≤ ((n : ℝ) + 1) * u ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      push_cast
      nlinarith
    calc
      (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
          (1 + u) ^ n * ((1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u)) := by
            rw [pow_succ]; ring
      _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) := mul_le_mul_of_nonneg_left hs hp
      _ ≤ 1 := ih

private theorem p20_pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P20GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p20Gamma u n := by
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  rw [p20Gamma]
  apply (le_div_iff₀ hd).2
  have h := p20_pow_factor u hu n
  nlinarith

private theorem p20_fold_bound (fp : P20FPModel) (n : ℕ)
    (q r : Fin n → ℝ) (v V C : ℝ)
    (hC : 0 ≤ C) (hV : |V| ≤ C) (hv : |v - V| ≤ fp.u * C)
    (hq : ∀ j, |q j - r j| ≤ fp.u * |r j|) :
    |Fin.foldl n (fun acc j => fp.fl_add acc (q j)) v -
        (V + ∑ j, r j)| ≤
      ((1 + fp.u) ^ (n + 1) - 1) * (C + ∑ j, |r j|) := by
  induction n with
  | zero =>
    simpa using hv
  | succ n ih =>
    let q' : Fin n → ℝ := fun j => q j.castSucc
    let r' : Fin n → ℝ := fun j => r j.castSucc
    let acc := Fin.foldl n (fun z j => fp.fl_add z (q' j)) v
    let E := V + ∑ j, r' j
    let A := C + ∑ j, |r' j|
    have hprev : |acc - E| ≤ ((1 + fp.u) ^ (n + 1) - 1) * A := by
      exact ih q' r' (fun j => hq j.castSucc)
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hE : |E| ≤ A := by
      dsimp [E, A]
      calc
        |V + ∑ j, r' j| ≤ |V| + |∑ j, r' j| := abs_add_le _ _
        _ ≤ C + ∑ j, |r' j| :=
          add_le_add hV (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := r'))
    have hqLast : |q (Fin.last n) - r (Fin.last n)| ≤
        fp.u * |r (Fin.last n)| := hq _
    have hstep :
        |fp.fl_add acc (q (Fin.last n)) - (E + r (Fin.last n))| ≤
          (1 + fp.u) *
              (((1 + fp.u) ^ (n + 1) - 1) * A + fp.u * |r (Fin.last n)|) +
            fp.u * (A + |r (Fin.last n)|) := by
      calc
        _ ≤ (1 + fp.u) * (|acc - E| + |q (Fin.last n) - r (Fin.last n)|) +
            fp.u * (|E| + |r (Fin.last n)|) := p20_add_error fp _ _ _ _
        _ ≤ (1 + fp.u) *
              (((1 + fp.u) ^ (n + 1) - 1) * A + fp.u * |r (Fin.last n)|) +
            fp.u * (A + |r (Fin.last n)|) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (add_le_add hprev hqLast)
              (by linarith [fp.u_nonneg])
          · exact mul_le_mul_of_nonneg_left (add_le_add hE le_rfl)
              fp.u_nonneg
    have hcoef : (1 + fp.u) * fp.u + fp.u ≤
        (1 + fp.u) ^ (n + 2) - 1 := by
      have hp : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (n + 2) :=
        pow_le_pow_right₀ (by linarith [fp.u_nonneg]) (by omega)
      nlinarith [hp]
    have hbound :
        |fp.fl_add acc (q (Fin.last n)) - (E + r (Fin.last n))| ≤
          ((1 + fp.u) ^ (n + 2) - 1) *
            (A + |r (Fin.last n)|) := by
      calc
        _ ≤ (1 + fp.u) *
              (((1 + fp.u) ^ (n + 1) - 1) * A + fp.u * |r (Fin.last n)|) +
            fp.u * (A + |r (Fin.last n)|) := hstep
        _ = ((1 + fp.u) ^ (n + 2) - 1) * A +
              ((1 + fp.u) * fp.u + fp.u) * |r (Fin.last n)| := by
                rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
                ring
        _ ≤ ((1 + fp.u) ^ (n + 2) - 1) * A +
              ((1 + fp.u) ^ (n + 2) - 1) * |r (Fin.last n)| :=
                add_le_add_right (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) _
        _ = _ := by ring
    simpa [acc, E, A, q', r', Fin.foldl_succ_last, Fin.sum_univ_castSucc,
      add_assoc, show n + 1 + 1 = n + 2 by omega] using hbound

private theorem p20_product_bound (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) :
    |p20RoundedSparseRowProduct fp s a x - ∑ j, a j * x j| ≤
      ((1 + fp.u) ^ s - 1) * ∑ j, |a j * x j| := by
  cases s with
  | zero => simp [p20RoundedSparseRowProduct]
  | succ n =>
    have h := p20_fold_bound fp n
      (fun j : Fin n => fp.fl_mul (a j.succ) (x j.succ))
      (fun j : Fin n => a j.succ * x j.succ)
      (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) |a 0 * x 0|
      (abs_nonneg _) le_rfl (p20_mul_error fp (a 0) (x 0))
      (fun j => p20_mul_error fp (a j.succ) (x j.succ))
    simpa [p20RoundedSparseRowProduct, Fin.sum_univ_succ] using h

/-- P20-C2: the sparse-row computed-residual error bound in Section 2.2. -/
theorem p20_c2_sparse_residual_error
    (fp : P20FPModel) (s : ℕ) (a x : Fin s → ℝ) (b : ℝ)
    (hvalid : P20GammaValid fp.u (s + 1)) :
    |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      p20ResidualErrorMajorant fp s a x b := by
  -- PROOF_START P20-C2-H001
  let R : ℝ := ∑ j : Fin s, a j * x j
  let W : ℝ := ∑ j : Fin s, |a j * x j|
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hR : |R| ≤ W := by
    exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin s => a j * x j)
  have hp : |p20RoundedSparseRowProduct fp s a x - R| ≤
      ((1 + fp.u) ^ s - 1) * W := p20_product_bound fp s a x
  have hs : |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      (1 + fp.u) * |p20RoundedSparseRowProduct fp s a x - R| +
        fp.u * (|b| + |R|) := by
    simpa [p20RoundedResidual, p20ExactResidual, R] using
      (p20_sub_error fp b (p20RoundedSparseRowProduct fp s a x) b R)
  have hcoef : fp.u ≤ (1 + fp.u) ^ (s + 1) - 1 := by
    have hpow : (1 + fp.u) ^ 1 ≤ (1 + fp.u) ^ (s + 1) :=
      pow_le_pow_right₀ (by linarith [fp.u_nonneg]) (by omega)
    simp only [pow_one] at hpow
    linarith
  have hpower : |p20RoundedResidual fp s a x b - p20ExactResidual s a x b| ≤
      ((1 + fp.u) ^ (s + 1) - 1) * (|b| + W) := by
    calc
      _ ≤ (1 + fp.u) * |p20RoundedSparseRowProduct fp s a x - R| +
          fp.u * (|b| + |R|) := hs
      _ ≤ (1 + fp.u) * (((1 + fp.u) ^ s - 1) * W) +
          fp.u * (|b| + W) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hp (by linarith [fp.u_nonneg])
            · exact mul_le_mul_of_nonneg_left (add_le_add_right hR _) fp.u_nonneg
      _ = ((1 + fp.u) ^ (s + 1) - 1) * W + fp.u * |b| := by
            rw [pow_succ]
            ring
      _ ≤ ((1 + fp.u) ^ (s + 1) - 1) * W +
          ((1 + fp.u) ^ (s + 1) - 1) * |b| :=
            add_le_add_right (mul_le_mul_of_nonneg_right hcoef (abs_nonneg b)) _
      _ = _ := by ring
  have hgamma := p20_pow_sub_one_le_gamma fp.u fp.u_nonneg (s + 1) hvalid
  calc
    _ ≤ ((1 + fp.u) ^ (s + 1) - 1) * (|b| + W) := hpower
    _ ≤ p20Gamma fp.u (s + 1) * (|b| + W) :=
      mul_le_mul_of_nonneg_right hgamma (by positivity)
    _ = p20ResidualErrorMajorant fp s a x b := by
      simp [p20ResidualErrorMajorant, W, abs_mul]

end VSCLReuse

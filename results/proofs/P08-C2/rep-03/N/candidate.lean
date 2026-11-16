import VSCLReuse.P08.Definitions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace VSCLReuse

open scoped Matrix Matrix.Norms.Frobenius
open WithLp

private theorem p08_gamma_nonneg (u k : ℝ) (hu : 0 ≤ u) (hk : 0 ≤ k)
    (hvalid : k * u < 1) : 0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private theorem p08_gamma_step (u k : ℝ) (hu : 0 ≤ u) (hk : 1 ≤ k)
    (hvalid : (k + 1) * u < 1) :
    (1 + u) * p08GammaReal k u + u ≤ p08GammaReal (k + 1) u ∧
    2 * u + u ^ 2 ≤ p08GammaReal (k + 1) u := by
  have hden : 0 < 1 - k * u := by nlinarith
  have hden' : 0 < 1 - (k + 1) * u := by linarith
  have hk2 : 2 * u < 1 := by nlinarith
  unfold p08GammaReal
  constructor
  · have heq : (1 + u) * (k * u / (1 - k * u)) + u =
        (k + 1) * u / (1 - k * u) := by
      apply (eq_div_iff (ne_of_gt hden)).2
      have hcancel := div_mul_cancel₀ (k * u) (ne_of_gt hden)
      nlinarith
    rw [heq]
    apply (div_le_div_iff₀ hden hden').2
    nlinarith [mul_nonneg (add_nonneg (sub_nonneg.mpr hk) zero_le_one) hu]
  · apply (le_div_iff₀ hden').2
    nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg u)]

private theorem p08_round_step (fp : StandardFPModel) (k t s S x y : ℝ)
    (hk : 1 ≤ k) (hvalid : (k + 1) * fp.u < 1)
    (hS : |s| ≤ S) (herr : |t - s| ≤ p08GammaReal k fp.u * S) :
    |fp.fl_add t (fp.fl_mul x y) - (s + x * y)| ≤
      p08GammaReal (k + 1) fp.u * (S + |x * y|) := by
  obtain ⟨δm, hδm, hm⟩ := fp.model_mul x y
  obtain ⟨δa, hδa, ha⟩ := fp.model_add t (fp.fl_mul x y)
  rw [ha, hm]
  have hδa1 : |1 + δa| ≤ 1 + fp.u := by
    calc
      |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδa 1
  have hδma : |δm + δa + δm * δa| ≤ 2 * fp.u + fp.u ^ 2 := by
    calc
      |δm + δa + δm * δa| ≤ |δm| + |δa| + |δm * δa| := by
        exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ ≤ 2 * fp.u + fp.u ^ 2 := by
        rw [abs_mul]
        nlinarith [mul_le_mul hδm hδa (abs_nonneg _) fp.u_nonneg]
  have hγ := p08_gamma_step fp.u k fp.u_nonneg hk hvalid
  have hγ0 : 0 ≤ p08GammaReal k fp.u :=
    p08_gamma_nonneg fp.u k fp.u_nonneg (by linarith) (by nlinarith)
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) hS
  have hmain :
      (t + x * y * (1 + δm)) * (1 + δa) - (s + x * y) =
        (t - s) * (1 + δa) + s * δa + (x * y) * (δm + δa + δm * δa) := by ring
  rw [hmain]
  calc
    |(t - s) * (1 + δa) + s * δa + (x * y) * (δm + δa + δm * δa)|
        ≤ |t - s| * |1 + δa| + |s| * |δa| +
          |x * y| * |δm + δa + δm * δa| := by
          calc
            _ ≤ |(t - s) * (1 + δa)| + |s * δa| +
                |(x * y) * (δm + δa + δm * δa)| :=
              (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
            _ = _ := by simp only [abs_mul]
    _ ≤ (p08GammaReal k fp.u * S) * (1 + fp.u) + S * fp.u +
          |x * y| * (2 * fp.u + fp.u ^ 2) := by
          gcongr
    _ ≤ p08GammaReal (k + 1) fp.u * (S + |x * y|) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hγ.1) hS0,
            mul_nonneg (sub_nonneg.mpr hγ.2) (abs_nonneg (x * y))]

private theorem p08_round_fold_bound (fp : StandardFPModel) :
    ∀ (n k : ℕ) (x y : Fin n → ℝ) (t s S : ℝ),
      1 ≤ k → ((k + n : ℕ) : ℝ) * fp.u < 1 →
      |s| ≤ S → |t - s| ≤ p08GammaReal (k : ℝ) fp.u * S →
      |Fin.foldl n (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) t -
        (s + ∑ i : Fin n, x i * y i)| ≤
        p08GammaReal ((k + n : ℕ) : ℝ) fp.u *
          (S + ∑ i : Fin n, |x i * y i|) := by
  intro n
  induction n with
  | zero =>
      intro k x y t s S hk hv hS herr
      simpa using herr
  | succ n ih =>
      intro k x y t s S hk hv hS herr
      have hv' : (((k + 1 : ℕ) : ℝ) : ℝ) * fp.u < 1 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at hv ⊢
        nlinarith [fp.u_nonneg]
      have hstep := p08_round_step fp (k : ℝ) t s S (x 0) (y 0)
        (by exact_mod_cast hk) (by simpa only [Nat.cast_add, Nat.cast_one] using hv') hS herr
      have hs' : |s + x 0 * y 0| ≤ S + |x 0 * y 0| :=
        (abs_add_le _ _).trans (add_le_add_left hS _)
      have htail := ih (k + 1) (fun i => x i.succ) (fun i => y i.succ)
        (fp.fl_add t (fp.fl_mul (x 0) (y 0)))
        (s + x 0 * y 0) (S + |x 0 * y 0|)
        (by omega) (by
          have he : k + 1 + n = k + (n + 1) := by omega
          simpa only [he] using hv) hs'
        (by simpa only [Nat.cast_add, Nat.cast_one] using hstep)
      have he : k + 1 + n = k + (n + 1) := by omega
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, he, add_assoc] using htail

private theorem p08_gamma_one_ge (u : ℝ) (hv : u < 1) :
    u ≤ p08GammaReal 1 u := by
  unfold p08GammaReal
  have hd : 0 < 1 - 1 * u := by linarith
  apply (le_div_iff₀ hd).2
  nlinarith [sq_nonneg u]

private theorem p08_gamma_one_add (u k : ℝ) (hvalid : k * u < 1) :
    1 + p08GammaReal k u = 1 / (1 - k * u) := by
  unfold p08GammaReal
  have hd : 1 - k * u ≠ 0 := ne_of_gt (by linarith)
  apply (eq_div_iff hd).2
  have hcancel := div_mul_cancel₀ (k * u) hd
  nlinarith

private theorem p08_gamma_combine (u a d : ℝ) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hv : (a + d) * u < 1) :
    p08GammaReal a u + p08GammaReal d u +
      p08GammaReal a u * p08GammaReal d u ≤ p08GammaReal (a + d) u := by
  have hva : a * u < 1 := by nlinarith [mul_nonneg hd hu]
  have hvd : d * u < 1 := by nlinarith [mul_nonneg ha hu]
  have hda : 0 < 1 - a * u := by linarith
  have hdd : 0 < 1 - d * u := by linarith
  have hds : 0 < 1 - (a + d) * u := by linarith
  have hprod : 0 < (1 - a * u) * (1 - d * u) := mul_pos hda hdd
  have hle : 1 - (a + d) * u ≤ (1 - a * u) * (1 - d * u) := by
    nlinarith [mul_nonneg (mul_nonneg ha hu) (mul_nonneg hd hu)]
  have hfrac : 1 / ((1 - a * u) * (1 - d * u)) ≤
      1 / (1 - (a + d) * u) := by
    apply (div_le_div_iff₀ hprod hds).2
    nlinarith
  have ha' := p08_gamma_one_add u a hva
  have hd' := p08_gamma_one_add u d hvd
  have hs' := p08_gamma_one_add u (a + d) hv
  have hcalc : (1 + p08GammaReal a u) * (1 + p08GammaReal d u) ≤
      1 + p08GammaReal (a + d) u := by
    rw [ha', hd', hs']
    calc
      _ = 1 / ((1 - a * u) * (1 - d * u)) := by
        simp only [one_div, mul_inv_rev]
        ring
      _ ≤ _ := hfrac
  nlinarith [hcalc]

private theorem p08_gamma_scaled (u a s : ℝ) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hs : 1 ≤ s) (hv : (a * s) * u < 1) :
    p08GammaReal a u * s ≤ p08GammaReal (a * s) u := by
  have hden1 : 0 < 1 - a * u := by
    nlinarith [mul_nonneg (mul_nonneg ha hu) (sub_nonneg.mpr hs)]
  have hden2 : 0 < 1 - a * s * u := by linarith
  have hnum : 0 ≤ a * s * u := by positivity
  have hle : 1 - a * s * u ≤ 1 - a * u := by
    nlinarith [mul_nonneg (mul_nonneg ha hu) (sub_nonneg.mpr hs)]
  unfold p08GammaReal
  have heq : a * u / (1 - a * u) * s = a * s * u / (1 - a * u) := by ring
  rw [heq]
  apply (div_le_div_iff₀ hden1 hden2).2
  nlinarith [mul_nonneg hnum (sub_nonneg.mpr hle)]

private theorem p08_gamma_cost (fp : StandardFPModel) (b r : ℕ)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    p08GammaReal (b : ℝ) fp.u +
        p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) +
        p08GammaReal (b : ℝ) fp.u * p08GammaReal (r : ℝ) fp.u *
          Real.sqrt (r : ℝ) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
  cases r with
  | zero => simp [p08GammaReal]
  | succ n =>
      let s := Real.sqrt ((n + 1 : ℕ) : ℝ)
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
      have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
      have hs1 : 1 ≤ s := by nlinarith
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      have hr0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have htu : ((n + 1 : ℕ) : ℝ) * s * fp.u < 1 := by
        dsimp [s] at hvalid ⊢
        nlinarith [mul_nonneg hb0 fp.u_nonneg]
      have hbu : (b : ℝ) * fp.u < 1 := by
        nlinarith [mul_nonneg (mul_nonneg hr0 hs0) fp.u_nonneg]
      have hscaled := p08_gamma_scaled fp.u ((n + 1 : ℕ) : ℝ) s
        fp.u_nonneg hr0 hs1 htu
      have hcomb := p08_gamma_combine fp.u (b : ℝ)
        (((n + 1 : ℕ) : ℝ) * s) fp.u_nonneg hb0
        (mul_nonneg hr0 hs0) hvalid
      have hγb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
        p08_gamma_nonneg fp.u (b : ℝ) fp.u_nonneg hb0 hbu
      change p08GammaReal (b : ℝ) fp.u +
          p08GammaReal ((n + 1 : ℕ) : ℝ) fp.u * s +
          p08GammaReal (b : ℝ) fp.u *
            p08GammaReal ((n + 1 : ℕ) : ℝ) fp.u * s ≤
        p08GammaReal ((b : ℝ) + ((n + 1 : ℕ) : ℝ) * s) fp.u
      nlinarith [mul_nonneg hγb (sub_nonneg.mpr hscaled)]

private theorem p08_rounded_dot_bound (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : (n : ℝ) * fp.u < 1) :
    |roundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p08GammaReal (n : ℝ) fp.u * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero => simp [roundedDotProduct]
  | succ n =>
      have hu1 : fp.u < 1 := by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at hvalid
        nlinarith [fp.u_nonneg]
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      have hfirst :
          |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
            p08GammaReal (1 : ℝ) fp.u * |x 0 * y 0| := by
        rw [hmul]
        have heq : x 0 * y 0 * (1 + δ) - x 0 * y 0 = x 0 * y 0 * δ := by ring
        rw [heq, abs_mul]
        exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg _)).trans
          (by simpa only [mul_comm] using
            (mul_le_mul_of_nonneg_right
              (p08_gamma_one_ge fp.u hu1) (abs_nonneg (x 0 * y 0))))
      have htail := p08_round_fold_bound fp n 1
        (fun i => x i.succ) (fun i => y i.succ)
        (fp.fl_mul (x 0) (y 0)) (x 0 * y 0) |x 0 * y 0|
        (by omega) (by simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hvalid)
        le_rfl (by simpa using hfirst)
      simpa only [roundedDotProduct, Fin.sum_univ_succ, Nat.cast_add,
        Nat.cast_one, Nat.add_comm 1 n, add_assoc] using htail

private noncomputable def p08VecNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, v i ^ 2)

private theorem p08_vec_norm_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p08VecNorm v := Real.sqrt_nonneg _

private theorem p08_vec_norm_sq {n : ℕ} (v : Fin n → ℝ) :
    p08VecNorm v ^ 2 = ∑ i : Fin n, v i ^ 2 := by
  unfold p08VecNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

private theorem p08_vec_norm_eq {n : ℕ} (v : Fin n → ℝ) :
    p08VecNorm v = ‖toLp 2 v‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [p08VecNorm, Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]

private theorem p08_vec_norm_add {n : ℕ} (v w : Fin n → ℝ) :
    p08VecNorm (v + w) ≤ p08VecNorm v + p08VecNorm w := by
  rw [p08_vec_norm_eq, p08_vec_norm_eq, p08_vec_norm_eq]
  simpa using norm_add_le (toLp 2 v) (toLp 2 w)

private theorem p08_vec_norm_smul {n : ℕ} (a : ℝ) (v : Fin n → ℝ) :
    p08VecNorm (a • v) = |a| * p08VecNorm v := by
  rw [p08_vec_norm_eq, p08_vec_norm_eq]
  simpa only [Real.norm_eq_abs] using norm_smul a (toLp 2 v)

private theorem p08_vec_norm_eq_zero {n : ℕ} {v : Fin n → ℝ}
    (hv : p08VecNorm v = 0) : v = 0 := by
  have hsq := p08_vec_norm_sq v
  rw [hv, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  funext i
  have hi : v i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).1 hsq.symm i
      (Finset.mem_univ i)
  change v i = 0
  nlinarith

private theorem p08_rect_norm_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = ‖A‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def]
  simp only [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs, Real.rpow_two]

private theorem p08_rect_norm_nonneg {m n : ℕ} (A : P08RectMatrix m n) :
    0 ≤ p08RectFrobNorm A := Real.sqrt_nonneg _

private theorem p08_rect_norm_sq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A ^ 2 = ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
  unfold p08RectFrobNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)]

private theorem p08_sum_abs_mul_sq_le {n : ℕ} (a v : Fin n → ℝ) :
    (∑ j : Fin n, |a j * v j|) ^ 2 ≤
      (∑ j : Fin n, a j ^ 2) * (∑ j : Fin n, v j ^ 2) := by
  simpa only [abs_mul, sq_abs] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => |a j|) (g := fun j => |v j|))

private theorem p08_rounded_matvec_error_norm (fp : StandardFPModel)
    {m n : ℕ} (A : P08RectMatrix m n) (v : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    p08VecNorm (p08RoundedRectMatVec fp A v - p08RectMatVec A v) ≤
      p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm A * p08VecNorm v := by
  let e : Fin m → ℝ := p08RoundedRectMatVec fp A v - p08RectMatVec A v
  let γ := p08GammaReal (n : ℝ) fp.u
  have hγ : 0 ≤ γ := p08_gamma_nonneg fp.u (n : ℝ) fp.u_nonneg
    (Nat.cast_nonneg n) hvalid
  have hrow (i : Fin m) :
      (e i) ^ 2 ≤ γ ^ 2 *
        (∑ j : Fin n, A i j ^ 2) * (∑ j : Fin n, v j ^ 2) := by
    have hd : |e i| ≤ γ * ∑ j : Fin n, |A i j * v j| := by
      simpa [e, p08RoundedRectMatVec, roundedMatVec, p08RectMatVec, γ] using
        p08_rounded_dot_bound fp n (A i) v hvalid
    have hsum0 : 0 ≤ ∑ j : Fin n, |A i j * v j| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsmall : (e i) ^ 2 ≤ (γ * ∑ j : Fin n, |A i j * v j|) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (e i)) (mul_nonneg hγ hsum0)).2 hd
    have hcs := p08_sum_abs_mul_sq_le (A i) v
    nlinarith [mul_nonneg (sq_nonneg γ)
      (sub_nonneg.mpr hcs)]
  have hsum : (∑ i : Fin m, (e i) ^ 2) ≤
      γ ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) *
        (∑ j : Fin n, v j ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, γ ^ 2 * (∑ j : Fin n, A i j ^ 2) *
          (∑ j : Fin n, v j ^ 2) := Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have he0 : 0 ≤ p08VecNorm e := p08_vec_norm_nonneg e
  have hr0 : 0 ≤ γ * p08RectFrobNorm A * p08VecNorm v :=
    mul_nonneg (mul_nonneg hγ (p08_rect_norm_nonneg A)) (p08_vec_norm_nonneg v)
  have heq := p08_vec_norm_sq e
  have hAq := p08_rect_norm_sq A
  have hvq := p08_vec_norm_sq v
  change p08VecNorm e ≤ _
  have hsq : p08VecNorm e ^ 2 ≤
      (γ * p08RectFrobNorm A * p08VecNorm v) ^ 2 := by
    calc
      _ = ∑ i : Fin m, e i ^ 2 := heq
      _ ≤ _ := hsum
      _ = _ := by rw [← hAq, ← hvq]; ring
  exact (sq_le_sq₀ he0 hr0).1 hsq

private theorem p08_matvec_norm_le {m n : ℕ}
    (A : P08RectMatrix m n) (v : Fin n → ℝ) :
    p08VecNorm (p08RectMatVec A v) ≤ p08RectFrobNorm A * p08VecNorm v := by
  have heq : Matrix.replicateCol (Fin 1) (p08RectMatVec A v) =
      A * Matrix.replicateCol (Fin 1) v := by
    ext i j
    simp [Matrix.mul_apply, p08RectMatVec, Matrix.replicateCol]
  calc
    _ = ‖Matrix.replicateCol (Fin 1) (p08RectMatVec A v)‖ := by
      rw [p08_vec_norm_eq]
      exact (Matrix.frobenius_norm_replicateCol (ι := Fin 1) _).symm
    _ = ‖A * Matrix.replicateCol (Fin 1) v‖ := by rw [heq]
    _ ≤ ‖A‖ * ‖Matrix.replicateCol (Fin 1) v‖ :=
      Matrix.frobenius_norm_mul _ _
    _ = p08RectFrobNorm A * p08VecNorm v := by
      calc
        _ = ‖A‖ * ‖toLp 2 v‖ :=
          congrArg (fun t : ℝ => ‖A‖ * t)
            (Matrix.frobenius_norm_replicateCol (ι := Fin 1) v)
        _ = _ := by rw [p08_rect_norm_eq, p08_vec_norm_eq]

private theorem p08_rect_matvec_sub {m n : ℕ}
    (A : P08RectMatrix m n) (v w : Fin n → ℝ) :
    p08RectMatVec A (v - w) =
      p08RectMatVec A v - p08RectMatVec A w := by
  funext i
  simp [p08RectMatVec, mul_sub, Finset.sum_sub_distrib]

private theorem p08_lowrank_matvec {b r : ℕ}
    (X Y : P08RectMatrix b r) (v : Fin b → ℝ) :
    p08RectMatVec X (p08RectMatVec (p08RectTranspose Y) v) =
      p08MatVec (p08LowRankMatrix X Y) v := by
  change X *ᵥ (Yᵀ *ᵥ v) = (X * Yᵀ) *ᵥ v
  exact Matrix.mulVec_mulVec v X Yᵀ

private theorem p08_orthonormal_transpose_mul {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    Xᵀ * X = 1 := by
  ext j k
  simp [Matrix.mul_apply, Matrix.transpose_apply, p08OrthonormalColumns] at hX ⊢
  exact hX j k

private theorem p08_orthonormal_vec_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (w : Fin r → ℝ) :
    p08VecNorm (p08RectMatVec X w) = p08VecNorm w := by
  have hmul := p08_orthonormal_transpose_mul X hX
  have hvec : p08RectMatVec X w = X *ᵥ w := rfl
  have hsq : ∑ i : Fin b, (p08RectMatVec X w i) ^ 2 =
      ∑ j : Fin r, w j ^ 2 := by
    calc
      _ = (X *ᵥ w) ⬝ᵥ (X *ᵥ w) := by simp [hvec, dotProduct, pow_two]
      _ = (w ᵥ* Xᵀ) ⬝ᵥ (X *ᵥ w) := by rw [Matrix.vecMul_transpose]
      _ = w ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ w)) :=
        (Matrix.dotProduct_mulVec w Xᵀ (X *ᵥ w)).symm
      _ = w ⬝ᵥ ((Xᵀ * X) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = w ⬝ᵥ w := by rw [hmul, Matrix.one_mulVec]
      _ = _ := by simp [dotProduct, pow_two]
  have hn1 := p08_vec_norm_sq (p08RectMatVec X w)
  have hn2 := p08_vec_norm_sq w
  nlinarith [p08_vec_norm_nonneg (p08RectMatVec X w), p08_vec_norm_nonneg w]

private theorem p08_orthonormal_left_norm {b r p : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (B : P08RectMatrix r p) :
    p08RectFrobNorm (p08RectMatMul X B) = p08RectFrobNorm B := by
  have hcol (j : Fin p) :
      (∑ i : Fin b, (p08RectMatMul X B i j) ^ 2) =
        ∑ k : Fin r, B k j ^ 2 := by
    have h := p08_orthonormal_vec_norm X hX (fun k => B k j)
    have hs := congrArg (fun a : ℝ => a ^ 2) h
    change p08VecNorm (p08RectMatVec X (fun k => B k j)) ^ 2 =
      p08VecNorm (fun k => B k j) ^ 2 at hs
    rw [p08_vec_norm_sq, p08_vec_norm_sq] at hs
    simpa [p08RectMatMul, p08RectMatVec] using hs
  have hs : p08RectFrobNorm (p08RectMatMul X B) ^ 2 =
      p08RectFrobNorm B ^ 2 := by
    rw [p08_rect_norm_sq, p08_rect_norm_sq]
    calc
      (∑ i : Fin b, ∑ j : Fin p, (p08RectMatMul X B i j) ^ 2) =
          ∑ j : Fin p, ∑ i : Fin b, (p08RectMatMul X B i j) ^ 2 :=
        Finset.sum_comm
      _ = ∑ j : Fin p, ∑ k : Fin r, B k j ^ 2 := by
        exact Finset.sum_congr rfl fun j _ => hcol j
      _ = ∑ k : Fin r, ∑ j : Fin p, B k j ^ 2 := Finset.sum_comm
  nlinarith [p08_rect_norm_nonneg (p08RectMatMul X B), p08_rect_norm_nonneg B]

private theorem p08_rect_norm_transpose {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  rw [p08_rect_norm_eq, p08_rect_norm_eq]
  change ‖Aᵀ‖ = ‖A‖
  exact Matrix.frobenius_norm_transpose A

private theorem p08_lowrank_norm_eq {b r : ℕ}
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  unfold p08FrobNorm p08LowRankMatrix
  rw [p08_orthonormal_left_norm X hX, p08_rect_norm_transpose]

private theorem p08_orthonormal_frob_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  have hcol (j : Fin r) : ∑ i : Fin b, X i j ^ 2 = 1 := by
    simpa only [pow_two, if_pos rfl] using hX j j
  have hsq : p08RectFrobNorm X ^ 2 = (r : ℝ) := by
    rw [p08_rect_norm_sq]
    calc
      (∑ i : Fin b, ∑ j : Fin r, X i j ^ 2) =
          ∑ j : Fin r, ∑ i : Fin b, X i j ^ 2 := Finset.sum_comm
      _ = ∑ j : Fin r, (1 : ℝ) := by
        exact Finset.sum_congr rfl fun j _ => hcol j
      _ = (r : ℝ) := by simp
  have hroot : (Real.sqrt (r : ℝ)) ^ 2 = (r : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg r)
  nlinarith [p08_rect_norm_nonneg X, Real.sqrt_nonneg (r : ℝ)]

private theorem p08_backward_from_forward {m n : ℕ}
    (A : P08RectMatrix m n) (v : Fin n → ℝ) (z : Fin m → ℝ) (η : ℝ)
    (hη : 0 ≤ η)
    (hforward : p08VecNorm (z - p08RectMatVec A v) ≤
      η * p08RectFrobNorm A * p08VecNorm v) :
    ∃ Δ : P08RectMatrix m n,
      z = p08RectMatVec (p08RectAdd A Δ) v ∧
      p08RectFrobNorm Δ ≤ η * p08RectFrobNorm A := by
  by_cases hv0 : p08VecNorm v = 0
  · have he0 : p08VecNorm (z - p08RectMatVec A v) = 0 := by
      apply le_antisymm
      · simpa [hv0] using hforward
      · exact p08_vec_norm_nonneg _
    have hz : z = p08RectMatVec A v := sub_eq_zero.mp (p08_vec_norm_eq_zero he0)
    refine ⟨0, ?_, ?_⟩
    · have hmat : p08RectAdd A (0 : P08RectMatrix m n) = A := by
        ext i j
        simp [p08RectAdd]
      rw [hmat]
      exact hz
    · rw [p08_rect_norm_eq]
      simpa using mul_nonneg hη (p08_rect_norm_nonneg A)
  · let e : Fin m → ℝ := z - p08RectMatVec A v
    let Q : ℝ := ∑ j : Fin n, v j ^ 2
    have hvpos : 0 < p08VecNorm v := lt_of_le_of_ne (p08_vec_norm_nonneg v) (Ne.symm hv0)
    have hQ : 0 < Q := by
      dsimp [Q]
      rw [← p08_vec_norm_sq]
      positivity
    let Δ : P08RectMatrix m n := fun i j => e i * v j / Q
    have hΔv : p08RectMatVec Δ v = e := by
      funext i
      change (∑ j : Fin n, (e i * v j / Q) * v j) = e i
      calc
        _ = e i / Q * (∑ j : Fin n, v j ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = e i := by
          change e i / Q * Q = e i
          exact div_mul_cancel₀ _ (ne_of_gt hQ)
    have hz : z = p08RectMatVec (p08RectAdd A Δ) v := by
      funext i
      have he : e i = z i - p08RectMatVec A v i := rfl
      have hd := congrFun hΔv i
      change z i = ∑ j : Fin n, (A i j + Δ i j) * v j
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      change z i = p08RectMatVec A v i + p08RectMatVec Δ v i
      rw [hΔv]
      nlinarith [hd]
    have houter : Δ = Q⁻¹ •
        (Matrix.replicateCol (Fin 1) e * Matrix.replicateRow (Fin 1) v) := by
      ext i j
      simp [Δ, Matrix.mul_apply, Q, Matrix.replicateCol, Matrix.replicateRow]
      ring
    have hΔbound : p08RectFrobNorm Δ ≤
        (1 / Q) * p08VecNorm e * p08VecNorm v := by
      calc
        _ = ‖Δ‖ := p08_rect_norm_eq Δ
        _ = (1 / Q) * ‖Matrix.replicateCol (Fin 1) e *
            Matrix.replicateRow (Fin 1) v‖ := by
          rw [houter, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_pos hQ]
          ring
        _ ≤ (1 / Q) *
            (‖Matrix.replicateCol (Fin 1) e‖ *
              ‖Matrix.replicateRow (Fin 1) v‖) :=
          mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul _ _) (by positivity)
        _ = (1 / Q) * p08VecNorm e * p08VecNorm v := by
          have hecol : ‖Matrix.replicateCol (Fin 1) e‖ = p08VecNorm e :=
            (Matrix.frobenius_norm_replicateCol (ι := Fin 1) e).trans
              (p08_vec_norm_eq e).symm
          have hvrow : ‖Matrix.replicateRow (Fin 1) v‖ = p08VecNorm v :=
            (Matrix.frobenius_norm_replicateRow (ι := Fin 1) v).trans
              (p08_vec_norm_eq v).symm
          rw [hecol, hvrow]
          ring
    refine ⟨Δ, hz, ?_⟩
    have hfe : p08VecNorm e ≤ η * p08RectFrobNorm A * p08VecNorm v := hforward
    have hfactor : 0 ≤ (1 / Q) * p08VecNorm v := by positivity
    have hmult := mul_le_mul_of_nonneg_left hfe hfactor
    have hcancel : (1 / Q) * p08VecNorm v * p08VecNorm v = 1 := by
      have hQeq : Q = p08VecNorm v ^ 2 := (p08_vec_norm_sq v).symm
      rw [hQeq]
      field_simp [hv0]
    apply hΔbound.trans
    calc
      (1 / Q) * p08VecNorm e * p08VecNorm v =
          ((1 / Q) * p08VecNorm v) * p08VecNorm e := by ring
      _ ≤ ((1 / Q) * p08VecNorm v) *
          (η * p08RectFrobNorm A * p08VecNorm v) := hmult
      _ = η * p08RectFrobNorm A := by
        calc
          _ = η * p08RectFrobNorm A *
              ((1 / Q) * p08VecNorm v * p08VecNorm v) := by ring
          _ = _ := by rw [hcancel]; ring

private theorem p08_lowrank_forward_bound {b r : ℕ}
    (fp : StandardFPModel) (X Y : P08RectMatrix b r) (v : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    p08VecNorm (p08RoundedLowRankMatVec fp X Y v -
      p08MatVec (p08LowRankMatrix X Y) v) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
        p08FrobNorm (p08LowRankMatrix X Y) * p08VecNorm v := by
  let B := p08RectTranspose Y
  let w := p08RectMatVec B v
  let wHat := p08RoundedRectMatVec fp B v
  let zHat := p08RoundedRectMatVec fp X wHat
  let L := p08LowRankMatrix X Y
  let γb := p08GammaReal (b : ℝ) fp.u
  let γr := p08GammaReal (r : ℝ) fp.u
  let γc := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  have hsqrt0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg (mul_nonneg hr0 hsqrt0) fp.u_nonneg]
  have hrvalid : (r : ℝ) * fp.u < 1 := by
    cases r with
    | zero => norm_num
    | succ n =>
        have hs2 : (Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 =
            ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
        have hs1 : 1 ≤ Real.sqrt (((n + 1 : ℕ) : ℝ)) := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
          nlinarith [Real.sqrt_nonneg (((n + 1 : ℕ) : ℝ))]
        have hterm : (((n + 1 : ℕ) : ℝ) * fp.u) ≤
            (((n + 1 : ℕ) : ℝ) * Real.sqrt (((n + 1 : ℕ) : ℝ))) * fp.u :=
          mul_le_mul_of_nonneg_right
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg (n + 1)))) fp.u_nonneg
        nlinarith [hterm, mul_nonneg hb0 fp.u_nonneg]
  have hγr : 0 ≤ γr := p08_gamma_nonneg fp.u (r : ℝ) fp.u_nonneg hr0 hrvalid
  have hL0 : 0 ≤ p08FrobNorm L := p08_rect_norm_nonneg L
  have hv0 : 0 ≤ p08VecNorm v := p08_vec_norm_nonneg v
  have hw : p08VecNorm w ≤ p08FrobNorm L * p08VecNorm v := by
    have h := p08_matvec_norm_le B v
    dsimp [B, w] at h ⊢
    rw [p08_rect_norm_transpose Y, ← p08_lowrank_norm_eq X Y hX] at h
    exact h
  have he1 : p08VecNorm (wHat - w) ≤ γb * p08FrobNorm L * p08VecNorm v := by
    have h := p08_rounded_matvec_error_norm fp B v hbvalid
    dsimp [B, w, wHat, γb] at h ⊢
    rw [p08_rect_norm_transpose Y, ← p08_lowrank_norm_eq X Y hX] at h
    exact h
  have he2 : p08VecNorm (zHat - p08RectMatVec X wHat) ≤
      γr * Real.sqrt (r : ℝ) * p08VecNorm wHat := by
    have h := p08_rounded_matvec_error_norm fp X wHat hrvalid
    dsimp [γr] at h ⊢
    rw [p08_orthonormal_frob_norm X hX] at h
    exact h
  have hwhat : p08VecNorm wHat ≤
      (1 + γb) * p08FrobNorm L * p08VecNorm v := by
    have heq : wHat = (wHat - w) + w := by abel
    rw [heq]
    calc
      _ ≤ p08VecNorm (wHat - w) + p08VecNorm w := p08_vec_norm_add _ _
      _ ≤ γb * p08FrobNorm L * p08VecNorm v +
          p08FrobNorm L * p08VecNorm v := add_le_add he1 hw
      _ = _ := by ring
  have hz : p08RectMatVec X w = p08MatVec L v := p08_lowrank_matvec X Y v
  have hdecomp : zHat - p08MatVec L v =
      (zHat - p08RectMatVec X wHat) +
        p08RectMatVec X (wHat - w) := by
    rw [p08_rect_matvec_sub, hz]
    abel
  change p08VecNorm (zHat - p08MatVec L v) ≤ γc * p08FrobNorm L * p08VecNorm v
  rw [hdecomp]
  calc
    _ ≤ p08VecNorm (zHat - p08RectMatVec X wHat) +
        p08VecNorm (p08RectMatVec X (wHat - w)) := p08_vec_norm_add _ _
    _ = p08VecNorm (zHat - p08RectMatVec X wHat) +
        p08VecNorm (wHat - w) := by rw [p08_orthonormal_vec_norm X hX]
    _ ≤ γr * Real.sqrt (r : ℝ) * p08VecNorm wHat +
        γb * p08FrobNorm L * p08VecNorm v := add_le_add he2 he1
    _ ≤ γr * Real.sqrt (r : ℝ) *
          ((1 + γb) * p08FrobNorm L * p08VecNorm v) +
        γb * p08FrobNorm L * p08VecNorm v := by
      gcongr
    _ = (γb + γr * Real.sqrt (r : ℝ) +
          γb * γr * Real.sqrt (r : ℝ)) *
          p08FrobNorm L * p08VecNorm v := by ring
    _ ≤ γc * p08FrobNorm L * p08VecNorm v := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right (p08_gamma_cost fp b r hvalid) hL0
      · exact hv0

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
  let L : P08Matrix b := p08LowRankMatrix X Y
  let c : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let γ : ℝ := p08GammaReal c fp.u
  let zHat : P08Vector b := p08RoundedLowRankMatVec fp X Y v
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hγ : 0 ≤ γ := p08_gamma_nonneg fp.u c fp.u_nonneg hc0 hvalid
  have hfwd : p08VecNorm (zHat - p08RectMatVec L v) ≤
      γ * p08RectFrobNorm L * p08VecNorm v := by
    exact p08_lowrank_forward_bound fp X Y v hX hvalid
  obtain ⟨ΔT, hZT, hNT⟩ :=
    p08_backward_from_forward L v zHat γ hγ hfwd
  have happrox' : p08RectFrobNorm (A - L) ≤ ε * β := happrox
  have hL : p08RectFrobNorm L ≤ p08RectFrobNorm A + ε * β := by
    have heq : L = A - (A - L) := by abel
    calc
      p08RectFrobNorm L = ‖L‖ := p08_rect_norm_eq L
      _ = ‖A - (A - L)‖ := by rw [← heq]
      _ ≤ ‖A‖ + ‖A - L‖ := norm_sub_le _ _
      _ = p08RectFrobNorm A + p08RectFrobNorm (A - L) := by
        rw [p08_rect_norm_eq, p08_rect_norm_eq]
      _ ≤ p08RectFrobNorm A + ε * β := add_le_add_right happrox' _
  have hdiff : p08RectFrobNorm (L - A) ≤ ε * β := by
    rw [p08_rect_norm_eq] at happrox' ⊢
    simpa only [norm_sub_rev] using happrox'
  let ΔA : P08Matrix b := L - A + ΔT
  have hZA : zHat = p08RectMatVec (p08RectAdd A ΔA) v := by
    have heq : p08RectAdd A ΔA = p08RectAdd L ΔT := by
      ext i j
      simp [ΔA, p08RectAdd]
      ring
    rw [heq]
    exact hZT
  have hNA : p08RectFrobNorm ΔA ≤
      γ * p08RectFrobNorm A + ε * (1 + γ) * β := by
    have htri : p08RectFrobNorm ΔA ≤
        p08RectFrobNorm (L - A) + p08RectFrobNorm ΔT := by
      change p08RectFrobNorm (L - A + ΔT) ≤ _
      rw [p08_rect_norm_eq, p08_rect_norm_eq, p08_rect_norm_eq]
      exact norm_add_le _ _
    have hmul : γ * p08RectFrobNorm L ≤
        γ * (p08RectFrobNorm A + ε * β) :=
      mul_le_mul_of_nonneg_left hL hγ
    calc
      _ ≤ p08RectFrobNorm (L - A) + p08RectFrobNorm ΔT := htri
      _ ≤ ε * β + γ * p08RectFrobNorm L := add_le_add hdiff hNT
      _ ≤ ε * β + γ * (p08RectFrobNorm A + ε * β) :=
        add_le_add_right hmul _
      _ = γ * p08RectFrobNorm A + ε * (1 + γ) * β := by ring
  refine ⟨ΔT, ΔA, ?_, ?_, ?_, ?_⟩
  · exact hZT
  · exact hNT
  · exact hZA
  · exact hNA

end VSCLReuse

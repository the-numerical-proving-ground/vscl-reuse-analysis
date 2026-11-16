import VSCLReuse.P52.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Recursive.Core

set_option maxHeartbeats 1000000

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p52AsFPModel (fp : P52FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    simp

private lemma p52_gamma_quad (fp : P52FPModel) (k : ℕ)
    (hsmall : (k : ℝ) * fp.u ≤ 1 / 2) :
    NumStability.gamma (p52AsFPModel fp) k ≤
      (k : ℝ) * fp.u + 2 * (k : ℝ) ^ 2 * fp.u ^ 2 := by
  have hvalid : NumStability.gammaValid (p52AsFPModel fp) k := by
    simpa [NumStability.gammaValid, p52AsFPModel] using (show (k : ℝ) * fp.u < 1 by linarith)
  rw [NumStability.gamma_eq_linear_plus_quadratic_remainder _ k hvalid]
  simp only [p52AsFPModel]
  have hd : 0 < 1 - (k : ℝ) * fp.u := by linarith
  have hq : ((k : ℝ) * fp.u) ^ 2 / (1 - (k : ℝ) * fp.u) ≤
      2 * ((k : ℝ) * fp.u) ^ 2 := by
    apply (div_le_iff₀ hd).2
    nlinarith [sq_nonneg ((k : ℝ) * fp.u)]
  nlinarith [hq]

private lemma p52_mul_error {u x y Lx Kx Ly Ky : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hLx : 0 ≤ Lx) (hKx : 0 ≤ Kx) (hLy : 0 ≤ Ly) (hKy : 0 ≤ Ky)
    (hx : |x - 1| ≤ Lx * u + Kx * u ^ 2)
    (hy : |y - 1| ≤ Ly * u + Ky * u ^ 2) :
    |x * y - 1| ≤
      (Lx + Ly) * u + (Kx + Ky + (Lx + Kx) * (Ly + Ky)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hx0 : 0 ≤ Lx * u + Kx * u ^ 2 := by positivity
  have hy0 : 0 ≤ Ly * u + Ky * u ^ 2 := by positivity
  have hx' : |x - 1| ≤ (Lx + Kx) * u := by
    nlinarith [mul_nonneg hKx (sub_nonneg.mpr hu2)]
  have hy' : |y - 1| ≤ (Ly + Ky) * u := by
    nlinarith [mul_nonneg hKy (sub_nonneg.mpr hu2)]
  have hprod : |x - 1| * |y - 1| ≤
      ((Lx + Kx) * u) * ((Ly + Ky) * u) :=
    mul_le_mul hx' hy' (abs_nonneg _) (by positivity)
  calc
    |x * y - 1| = |(x - 1) + (y - 1) + (x - 1) * (y - 1)| := by congr 1; ring
    _ ≤ |x - 1| + |y - 1| + |x - 1| * |y - 1| := by
      calc
        _ ≤ |(x - 1) + (y - 1)| + |(x - 1) * (y - 1)| :=
          abs_add_le _ _
        _ ≤ |x - 1| + |y - 1| + |(x - 1) * (y - 1)| :=
          by simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right (abs_add_le (x - 1) (y - 1))
              |(x - 1) * (y - 1)|)
        _ = _ := by rw [abs_mul]
    _ ≤ _ := by nlinarith [hx, hy, hprod]

private lemma p52_ratio_error {D S t : ℝ}
    (hD : D ≠ 0) (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2)
    (he : |S - D| ≤ t * |D|) :
    S ≠ 0 ∧ |D / S - 1| ≤ t + 2 * t ^ 2 := by
  have hd : 0 < |D| := abs_pos.mpr hD
  have hs : (1 - t) * |D| ≤ |S| := by
    have htri : |D| ≤ |S - D| + |S| := by
      calc
        |D| = |-(S - D) + S| := by congr 1; ring
        _ ≤ |-(S - D)| + |S| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    nlinarith
  have hden : 0 < 1 - t := by linarith
  have hspos : 0 < |S| := lt_of_lt_of_le (mul_pos hden hd) hs
  have hS : S ≠ 0 := abs_pos.mp hspos
  constructor
  · exact hS
  have hratio : |D / S - 1| = |S - D| / |S| := by
    have hid : D / S - 1 = (D - S) / S := by field_simp
    rw [hid, abs_div, abs_sub_comm]
  rw [hratio]
  have hfirst : |S - D| / |S| ≤ t / (1 - t) := by
    apply (div_le_div_iff₀ hspos hden).2
    have hleft : |S - D| * (1 - t) ≤ (t * |D|) * (1 - t) :=
      mul_le_mul_of_nonneg_right he (le_of_lt hden)
    have hright : t * ((1 - t) * |D|) ≤ t * |S| :=
      mul_le_mul_of_nonneg_left hs ht
    nlinarith
  have hsecond : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    apply (div_le_iff₀ hden).2
    have hnonneg : 0 ≤ t ^ 2 * (1 - 2 * t) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  exact le_trans hfirst hsecond

theorem p52_c3_theorem2_full_named
    (N M : ℕ) (a f : Fin N → ℝ) (b : Fin M → ℝ)
    (A B CA CB betaBound : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hN : 0 < N) (hM : 0 < M)
    (hD0 : (∑ j : Fin M, b j) ≠ 0)
    (hbetaBound : p52DenominatorCondition M b ≤ betaBound)
    (hbetaBound0 : 0 ≤ betaBound) :
    ∃ u0 C : ℝ, 0 < u0 ∧ 0 ≤ C ∧
      ∀ (fp : P52FPModel) (ahat : Fin N → ℝ) (bhat : Fin M → ℝ),
      fp.u ≤ u0 →
      (∀ i, ∃ alpha_i : ℝ,
        ahat i = a i * (1 + alpha_i) ∧
          |alpha_i| ≤ A * fp.u + CA * fp.u ^ 2) →
      (∀ j, ∃ beta_j : ℝ,
        bhat j = b j * (1 + beta_j) ∧
          |beta_j| ≤ B * fp.u + CB * fp.u ^ 2) →
      ∃ fhat : Fin N → ℝ,
        p52ComputedQuotient fp N M ahat f bhat =
          (∑ i : Fin N, a i * fhat i) / (∑ j : Fin M, b j) ∧
        ‖fhat - f‖ ≤
          ((((N : ℝ) + 1 + A) +
            (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
            C * fp.u ^ 2) * ‖f‖ := by
  -- PROOF_START P52-C3-H001
  classical
  let nr : ℝ := N
  let mr : ℝ := (M - 1 : ℕ)
  let gn : ℝ := 2 * nr ^ 2
  let gm : ℝ := 2 * mr ^ 2
  let pn : ℝ := A + nr
  let qn : ℝ := CA + gn + (A + CA) * (nr + gn)
  let ln : ℝ := pn + 1
  let kn : ℝ := qn + (pn + qn)
  let ld : ℝ := B + mr
  let kd : ℝ := CB + gm + (B + CB) * (mr + gm)
  let hb : ℝ := (ld + kd) * betaBound
  let lq : ℝ := ld * betaBound
  let kq : ℝ := kd * betaBound + 2 * hb ^ 2
  let C : ℝ := kn + kq + (ln + kn) * (lq + kq)
  let T : ℝ := 1 + nr + mr + hb
  let u0 : ℝ := 1 / (2 * T)
  have hnr : 0 ≤ nr := by dsimp [nr]; positivity
  have hmr : 0 ≤ mr := by dsimp [mr]; positivity
  have hgn : 0 ≤ gn := by dsimp [gn]; positivity
  have hgm : 0 ≤ gm := by dsimp [gm]; positivity
  have hpn : 0 ≤ pn := by dsimp [pn]; positivity
  have hqn : 0 ≤ qn := by dsimp [qn]; positivity
  have hln : 0 ≤ ln := by dsimp [ln]; positivity
  have hkn : 0 ≤ kn := by dsimp [kn]; positivity
  have hld : 0 ≤ ld := by dsimp [ld]; positivity
  have hkd : 0 ≤ kd := by dsimp [kd]; positivity
  have hhb : 0 ≤ hb := by dsimp [hb]; positivity
  have hlq : 0 ≤ lq := by dsimp [lq]; positivity
  have hkq : 0 ≤ kq := by dsimp [kq]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hu0pos : 0 < u0 := by dsimp [u0]; positivity
  refine ⟨u0, C, hu0pos, hC, ?_⟩
  intro fp ahat bhat hu0 ha hbhat
  let u := fp.u
  have hu : 0 ≤ u := fp.u_nonneg
  have hcap : 2 * T * u ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hu0 (show 0 ≤ 2 * T by positivity)
    dsimp [u0, u] at h ⊢
    convert h using 1 <;> field_simp
  have hu1 : u ≤ 1 := by
    have hT1 : 1 ≤ T := by dsimp [T]; linarith
    have hx : 0 ≤ (T - 1) * u := mul_nonneg (by linarith) hu
    nlinarith only [hcap, hx]
  have hns : nr * u ≤ 1 / 2 := by
    have hx : 0 ≤ (T - nr) * u := by
      apply mul_nonneg _ hu
      dsimp [T]; linarith only [hmr, hhb]
    nlinarith only [hcap, hx]
  have hms : mr * u ≤ 1 / 2 := by
    have hx : 0 ≤ (T - mr) * u := by
      apply mul_nonneg _ hu
      dsimp [T]; linarith only [hnr, hhb]
    nlinarith only [hcap, hx]
  have hbs : hb * u ≤ 1 / 2 := by
    have hx : 0 ≤ (T - hb) * u := by
      apply mul_nonneg _ hu
      dsimp [T]; linarith only [hnr, hmr]
    nlinarith only [hcap, hx]
  have hvalidN : NumStability.gammaValid (p52AsFPModel fp) N := by
    change (N : ℝ) * fp.u < 1
    change (N : ℝ) * fp.u ≤ 1 / 2 at hns
    linarith
  have hvalidM : NumStability.gammaValid (p52AsFPModel fp) (M - 1) := by
    change ((M - 1 : ℕ) : ℝ) * fp.u < 1
    change ((M - 1 : ℕ) : ℝ) * fp.u ≤ 1 / 2 at hms
    linarith
  have hgammaN : NumStability.gamma (p52AsFPModel fp) N ≤ nr * u + gn * u ^ 2 := by
    simpa only [nr, gn, u] using p52_gamma_quad fp N hns
  have hgammaM : NumStability.gamma (p52AsFPModel fp) (M - 1) ≤
      mr * u + gm * u ^ 2 := by
    simpa only [mr, gm, u] using p52_gamma_quad fp (M - 1) hms
  choose alpha halphaEq halpha using ha
  choose beta hbetaEq hbeta using hbhat
  obtain ⟨eta, heta, hdotRaw⟩ :=
    NumStability.dotProduct_backward_error (p52AsFPModel fp) N ahat f hvalidN
  obtain ⟨theta, htheta, hsumRaw⟩ :=
    NumStability.recursiveSum_backward_error (p52AsFPModel fp) M bhat hvalidM
  have heta' (i : Fin N) : |eta i| ≤ nr * u + gn * u ^ 2 :=
    le_trans (heta i) hgammaN
  have htheta' (j : Fin M) : |theta j| ≤ mr * u + gm * u ^ 2 :=
    le_trans (htheta j) hgammaM
  have halpha' (i : Fin N) : |(1 + alpha i) - 1| ≤ A * u + CA * u ^ 2 := by
    simpa only [add_sub_cancel_left] using halpha i
  have hbeta' (j : Fin M) : |(1 + beta j) - 1| ≤ B * u + CB * u ^ 2 := by
    simpa only [add_sub_cancel_left] using hbeta j
  have heta'' (i : Fin N) : |(1 + eta i) - 1| ≤ nr * u + gn * u ^ 2 := by
    simpa only [add_sub_cancel_left] using heta' i
  have htheta'' (j : Fin M) : |(1 + theta j) - 1| ≤ mr * u + gm * u ^ 2 := by
    simpa only [add_sub_cancel_left] using htheta' j
  let D : ℝ := ∑ j : Fin M, b j
  let S : ℝ := p52RecursiveSum fp M bhat
  have hdot : p52RoundedDotProduct fp N ahat f =
      ∑ i : Fin N, a i * f i * ((1 + alpha i) * (1 + eta i)) := by
    change p52RoundedDotProduct fp N ahat f =
      ∑ i : Fin N, a i * f i * ((1 + alpha i) * (1 + eta i))
    rw [show p52RoundedDotProduct fp N ahat f =
      NumStability.fl_dotProduct (p52AsFPModel fp) N ahat f from rfl, hdotRaw]
    apply Finset.sum_congr rfl
    intro i hi
    rw [halphaEq i]
    ring
  have hsum : S = ∑ j : Fin M, b j * ((1 + beta j) * (1 + theta j)) := by
    change p52RecursiveSum fp M bhat = _
    rw [show p52RecursiveSum fp M bhat =
      NumStability.fl_recursiveSum (p52AsFPModel fp) M bhat from rfl, hsumRaw]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbetaEq j]
    ring
  have hdenComp (j : Fin M) :
      |((1 + beta j) * (1 + theta j)) - 1| ≤ ld * u + kd * u ^ 2 := by
    simpa only [ld, kd, gm, mr] using
      p52_mul_error hu hu1 hB hCB hmr hgm (hbeta' j) (htheta'' j)
  let rd : ℝ := ld * u + kd * u ^ 2
  let t : ℝ := rd * betaBound
  have hrd : 0 ≤ rd := by dsimp [rd]; positivity
  have ht : 0 ≤ t := mul_nonneg hrd hbetaBound0
  have hSdiff : S - D =
      ∑ j : Fin M, b j * (((1 + beta j) * (1 + theta j)) - 1) := by
    rw [hsum]
    dsimp [D]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hSerr : |S - D| ≤ rd * (∑ j : Fin M, |b j|) := by
    rw [hSdiff]
    calc
      |∑ j : Fin M, b j * (((1 + beta j) * (1 + theta j)) - 1)| ≤
          ∑ j : Fin M, |b j * (((1 + beta j) * (1 + theta j)) - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin M, |b j| * |((1 + beta j) * (1 + theta j)) - 1| := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul]
      _ ≤ ∑ j : Fin M, |b j| * rd := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hdenComp j) (abs_nonneg _)
      _ = rd * (∑ j : Fin M, |b j|) := by rw [← Finset.sum_mul]; ring
  have hDbeta : (∑ j : Fin M, |b j|) ≤ betaBound * |D| := by
    have hx := hbetaBound
    change (∑ j : Fin M, |b j|) / |D| ≤ betaBound at hx
    exact (div_le_iff₀ (abs_pos.mpr hD0)).mp hx
  have hratioPrem : |S - D| ≤ t * |D| := by
    calc
      |S - D| ≤ rd * (∑ j : Fin M, |b j|) := hSerr
      _ ≤ rd * (betaBound * |D|) :=
        mul_le_mul_of_nonneg_left hDbeta hrd
      _ = t * |D| := by dsimp [t]; ring
  have hu2 : u ^ 2 ≤ u := by nlinarith only [hu, hu1]
  have hrdBound : rd ≤ (ld + kd) * u := by
    dsimp [rd]
    nlinarith only [mul_nonneg hkd (sub_nonneg.mpr hu2)]
  have htBound : t ≤ hb * u := by
    have hx := mul_le_mul_of_nonneg_right hrdBound hbetaBound0
    dsimp [t, hb]
    nlinarith only [hx]
  have htHalf : t ≤ 1 / 2 := le_trans htBound hbs
  obtain ⟨hS0, hratio⟩ := p52_ratio_error hD0 ht htHalf hratioPrem
  have htSq : t ^ 2 ≤ (hb * u) ^ 2 := by
    have hx : 0 ≤ (hb * u - t) * (hb * u + t) :=
      mul_nonneg (sub_nonneg.mpr htBound)
        (add_nonneg (mul_nonneg hhb hu) ht)
    nlinarith only [hx]
  have hq : |D / S - 1| ≤ lq * u + kq * u ^ 2 := by
    calc
      |D / S - 1| ≤ t + 2 * t ^ 2 := hratio
      _ ≤ lq * u + kq * u ^ 2 := by
        dsimp [t, rd, lq, kq]
        nlinarith only [htSq]
  obtain ⟨delta, hdelta, hdiv⟩ :=
    fp.model_div (p52RoundedDotProduct fp N ahat f) S hS0
  have hdelta' : |(1 + delta) - 1| ≤ (1 : ℝ) * u + 0 * u ^ 2 := by
    simpa only [add_sub_cancel_left, one_mul, zero_mul, add_zero, u] using hdelta
  have hnum12 (i : Fin N) :
      |(1 + alpha i) * (1 + eta i) - 1| ≤ pn * u + qn * u ^ 2 := by
    simpa only [pn, qn, gn, nr] using
      p52_mul_error hu hu1 hA hCA hnr hgn (halpha' i) (heta'' i)
  have hnum3 (i : Fin N) :
      |((1 + alpha i) * (1 + eta i)) * (1 + delta) - 1| ≤
        ln * u + kn * u ^ 2 := by
    have hx := p52_mul_error hu hu1 hpn hqn (by norm_num : (0 : ℝ) ≤ 1)
      (le_refl (0 : ℝ)) (hnum12 i) hdelta'
    dsimp [ln, kn]
    convert hx using 1 <;> ring
  have htotal (i : Fin N) :
      |(((1 + alpha i) * (1 + eta i)) * (1 + delta)) * (D / S) - 1| ≤
        (ln + lq) * u + C * u ^ 2 := by
    exact p52_mul_error hu hu1 hln hkn hlq hkq (hnum3 i) hq
  let fhat : Fin N → ℝ := fun i =>
    f i * ((((1 + alpha i) * (1 + eta i)) * (1 + delta)) * (D / S))
  have hsumF : (∑ i : Fin N, a i * fhat i) =
      (∑ i : Fin N, a i * f i * ((1 + alpha i) * (1 + eta i))) *
        ((1 + delta) * (D / S)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [fhat]
    ring
  have hquot : p52ComputedQuotient fp N M ahat f bhat =
      (∑ i : Fin N, a i * fhat i) / D := by
    have hD : D ≠ 0 := hD0
    change fp.fl_div (p52RoundedDotProduct fp N ahat f) S = _
    rw [hdiv, hdot, hsumF]
    field_simp [hS0, hD]
  have hR : 0 ≤ (ln + lq) * u + C * u ^ 2 := by positivity
  have hcomponent (i : Fin N) :
      |fhat i - f i| ≤ ((ln + lq) * u + C * u ^ 2) * |f i| := by
    have hid : fhat i - f i =
        f i * (((((1 + alpha i) * (1 + eta i)) * (1 + delta)) * (D / S)) - 1) := by
      dsimp [fhat]
      ring
    rw [hid, abs_mul]
    calc
      |f i| * |(((1 + alpha i) * (1 + eta i)) * (1 + delta)) * (D / S) - 1| ≤
          |f i| * ((ln + lq) * u + C * u ^ 2) :=
        mul_le_mul_of_nonneg_left (htotal i) (abs_nonneg _)
      _ = _ := by ring
  have hnorm : ‖fhat - f‖ ≤ ((ln + lq) * u + C * u ^ 2) * ‖f‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR (norm_nonneg f))).2
    intro i
    change |fhat i - f i| ≤ ((ln + lq) * u + C * u ^ 2) * ‖f‖
    calc
      |fhat i - f i| ≤ ((ln + lq) * u + C * u ^ 2) * |f i| := hcomponent i
      _ ≤ ((ln + lq) * u + C * u ^ 2) * ‖f‖ := by
        apply mul_le_mul_of_nonneg_left _ hR
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm f i
  refine ⟨fhat, ?_, ?_⟩
  · simpa only [D] using hquot
  · calc
      ‖fhat - f‖ ≤ ((ln + lq) * u + C * u ^ 2) * ‖f‖ := hnorm
      _ = ((((N : ℝ) + 1 + A) +
            (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
            C * fp.u ^ 2) * ‖f‖ := by
        dsimp [ln, pn, lq, ld, nr, mr, u]
        ring

end VSCLReuse

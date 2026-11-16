import VSCLReuse.P52.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

set_option maxHeartbeats 400000

private noncomputable def p52ToFP (fp : P52FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p52_dot_eq (fp : P52FPModel) (N : ℕ) (x y : Fin N → ℝ) :
    p52RoundedDotProduct fp N x y =
      NumStability.fl_dotProduct (p52ToFP fp) N x y := by
  cases N <;> rfl

private lemma p52_sum_eq (fp : P52FPModel) (M : ℕ) (v : Fin M → ℝ) :
    p52RecursiveSum fp M v =
      NumStability.fl_recursiveSum (p52ToFP fp) M v := by
  rfl

private lemma p52_gamma_quadratic (fp : P52FPModel) (k : ℕ)
    (hsmall : (k : ℝ) * fp.u ≤ 1 / 2) :
    NumStability.gamma (p52ToFP fp) k ≤
      (k : ℝ) * fp.u + 2 * (k : ℝ) ^ 2 * fp.u ^ 2 := by
  have hv : NumStability.gammaValid (p52ToFP fp) k := by
    simpa [NumStability.gammaValid, p52ToFP] using (show (k : ℝ) * fp.u < 1 by linarith)
  rw [NumStability.gamma_eq_linear_plus_quadratic_remainder _ _ hv]
  have hd : 0 < 1 - (k : ℝ) * fp.u := by linarith
  have hsq : 0 ≤ ((k : ℝ) * fp.u) ^ 2 := sq_nonneg _
  have hrem : ((k : ℝ) * fp.u) ^ 2 / (1 - (k : ℝ) * fp.u) ≤
      2 * (k : ℝ) ^ 2 * fp.u ^ 2 := by
    rw [div_le_iff₀ hd]
    have hh : 0 ≤ ((k : ℝ) * fp.u) ^ 2 * (1 - 2 * ((k : ℝ) * fp.u)) :=
      mul_nonneg hsq (by linarith)
    nlinarith
  simpa [p52ToFP, pow_mul] using (add_le_add_left hrem ((k : ℝ) * fp.u))

private lemma p52_combine_errors
    (u p p₂ q q₂ x y : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : 0 ≤ p) (hp₂ : 0 ≤ p₂) (hq : 0 ≤ q) (hq₂ : 0 ≤ q₂)
    (hx : |x| ≤ p * u + p₂ * u ^ 2)
    (hy : |y| ≤ q * u + q₂ * u ^ 2) :
    |x + y + x * y| ≤
      (p + q) * u + (p₂ + q₂ + (p + p₂) * (q + q₂)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hx' : |x| ≤ (p + p₂) * u := by
    nlinarith [mul_nonneg hp₂ (sub_nonneg.mpr hu1)]
  have hy' : |y| ≤ (q + q₂) * u := by
    nlinarith [mul_nonneg hq₂ (sub_nonneg.mpr hu1)]
  have hp' : 0 ≤ (p + p₂) * u := mul_nonneg (add_nonneg hp hp₂) hu0
  have hxy : |x * y| ≤ (p + p₂) * (q + q₂) * u ^ 2 := by
    rw [abs_mul]
    have hh := mul_le_mul hx' hy' (abs_nonneg y) hp'
    nlinarith
  calc
    |x + y + x * y| ≤ |x| + |y| + |x * y| := by
      linarith [abs_add_le x y, abs_add_le (x + y) (x * y)]
    _ ≤ (p + q) * u +
        (p₂ + q₂ + (p + p₂) * (q + q₂)) * u ^ 2 := by
      linarith

private lemma p52_ratio_error
    (D R u E δ : ℝ) (hD : D ≠ 0) (hR : R ≠ 0)
    (hu : 0 ≤ u) (hE0 : 0 ≤ E) (hEhalf : E ≤ 1 / 2)
    (herr : |R - D| ≤ E * |D|) (hδ : |δ| ≤ u) :
    |D / R * (1 + δ) - 1| ≤ u + E + 2 * (u + E) * E := by
  have hDa : 0 < |D| := abs_pos.mpr hD
  have hRa : 0 < |R| := abs_pos.mpr hR
  have hden : 0 < 1 - E := by linarith
  have hDtri : |D| ≤ |R| + |R - D| := by
    calc
      |D| = |R + (D - R)| := by ring
      _ ≤ |R| + |D - R| := abs_add_le _ _
      _ = |R| + |R - D| := by rw [abs_sub_comm]
  have hRlower : (1 - E) * |D| ≤ |R| := by linarith
  have hnum : |D * (1 + δ) - R| ≤ (u + E) * |D| := by
    have hh := abs_add_le (D * δ) (D - R)
    have hdδ : |D * δ| ≤ u * |D| := by
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg D)]
    have herr' : |D - R| ≤ E * |D| := by simpa [abs_sub_comm] using herr
    calc
      |D * (1 + δ) - R| = |D * δ + (D - R)| := by ring
      _ ≤ |D * δ| + |D - R| := hh
      _ ≤ (u + E) * |D| := by linarith
  have hfrac : |D * (1 + δ) - R| / |R| ≤ (u + E) / (1 - E) := by
    apply (div_le_div_iff₀ hRa hden).2
    have h1 := mul_le_mul_of_nonneg_right hnum (le_of_lt hden)
    have h2 := mul_le_mul_of_nonneg_left hRlower (add_nonneg hu hE0)
    nlinarith
  have hlast : (u + E) / (1 - E) ≤ u + E + 2 * (u + E) * E := by
    rw [div_le_iff₀ hden]
    have hh : 0 ≤ (u + E) * E * (1 - 2 * E) :=
      mul_nonneg (mul_nonneg (add_nonneg hu hE0) hE0) (by linarith)
    nlinarith
  have heq : D / R * (1 + δ) - 1 = (D * (1 + δ) - R) / R := by
    field_simp
  rw [heq, abs_div]
  exact le_trans hfrac hlast

private lemma p52_ratio_budget (u q K E : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hE0 : 0 ≤ E) (hE : E ≤ q * u + K * u ^ 2) :
    u + E + 2 * (u + E) * E ≤
      (1 + q) * u + (K + 2 * (1 + q + K) * (q + K)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hE' : E ≤ (q + K) * u := by
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hu1)]
  have hUE : u + E ≤ (1 + q + K) * u := by linarith
  have hprod : (u + E) * E ≤ (1 + q + K) * (q + K) * u ^ 2 := by
    have hh := mul_le_mul hUE hE' hE0 (mul_nonneg (by positivity) hu0)
    nlinarith
  linarith

private lemma p52_weighted_sum_error {I : Type*} [Fintype I]
    (v ε : I → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hε : ∀ i, |ε i| ≤ L) :
    |(∑ i, v i * (1 + ε i)) - ∑ i, v i| ≤
      L * ∑ i, |v i| := by
  have heq : (∑ i, v i * (1 + ε i)) - ∑ i, v i = ∑ i, v i * ε i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    |∑ i, v i * ε i| ≤ ∑ i, |v i * ε i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |v i| * L := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hε i) (abs_nonneg _)
    _ = L * ∑ i, |v i| := by rw [← Finset.sum_mul, mul_comm]

private lemma p52_norm_factor_bound {N : ℕ} (hN : 0 < N)
    (f w : Fin N → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hw : ∀ i, |w i - 1| ≤ L) :
    ‖(fun i => f i * w i) - f‖ ≤ L * ‖f‖ := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  have hfi : |f i| ≤ ‖f‖ := by simpa using norm_le_pi_norm f i
  have hcoord : ((fun i => f i * w i) - f) i = f i * (w i - 1) := by
    simp [Pi.sub_apply]
    ring
  rw [hcoord, Real.norm_eq_abs, abs_mul]
  calc
    |f i| * |w i - 1| ≤ |f i| * L :=
      mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
    _ ≤ ‖f‖ * L := mul_le_mul_of_nonneg_right hfi hL
    _ = L * ‖f‖ := mul_comm _ _

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
  let n : ℝ := N
  let k : ℝ := (M - 1 : ℕ)
  let gN : ℝ := 2 * n ^ 2
  let gM : ℝ := 2 * k ^ 2
  let KN : ℝ := CA + gN + (A + CA) * (n + gN)
  let KM : ℝ := CB + gM + (B + CB) * (k + gM)
  let q : ℝ := (k + B) * betaBound
  let K : ℝ := KM * betaBound
  let T : ℝ := K + 2 * (1 + q + K) * (q + K)
  let C : ℝ := KN + T + (A + n + KN) * (1 + q + T)
  let L : ℝ := 1 + n + k + q + K
  let u0 : ℝ := 1 / (2 * L)
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hgN : 0 ≤ gN := by dsimp [gN]; positivity
  have hgM : 0 ≤ gM := by dsimp [gM]; positivity
  have hKN : 0 ≤ KN := by dsimp [KN]; positivity
  have hKM : 0 ≤ KM := by dsimp [KM]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hu0 : 0 < u0 := by dsimp [u0]; positivity
  refine ⟨u0, C, hu0, hC, ?_⟩
  intro fp ahat bhat hu hahat hbhat
  have hu_nonneg : 0 ≤ fp.u := fp.u_nonneg
  have hLu0 : L * u0 = 1 / 2 := by
    dsimp [u0]
    field_simp [ne_of_gt hL]
  have hLu : L * fp.u ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hu (le_of_lt hL)
    linarith only [hh, hLu0]
  have h1L : 1 ≤ L := by dsimp [L]; linarith only [hn0, hk0, hq, hK]
  have hnL : n ≤ L := by dsimp [L]; linarith only [hk0, hq, hK]
  have hkL : k ≤ L := by dsimp [L]; linarith only [hn0, hq, hK]
  have hqKL : q + K ≤ L := by dsimp [L]; linarith only [hn0, hk0]
  have hu1 : fp.u ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right h1L hu_nonneg
    linarith only [hh, hLu]
  have hnsmall : n * fp.u ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hnL hu_nonneg
    linarith only [hh, hLu]
  have hksmall : k * fp.u ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hkL hu_nonneg
    linarith only [hh, hLu]
  have hvN : NumStability.gammaValid (p52ToFP fp) N := by
    simpa [NumStability.gammaValid, p52ToFP, n] using
      (show (N : ℝ) * fp.u < 1 by simpa [n] using (lt_of_le_of_lt hnsmall (by norm_num : (1 / 2 : ℝ) < 1)))
  have hvM : NumStability.gammaValid (p52ToFP fp) (M - 1) := by
    simpa [NumStability.gammaValid, p52ToFP, k] using
      (show ((M - 1 : ℕ) : ℝ) * fp.u < 1 by simpa [k] using
        (lt_of_le_of_lt hksmall (by norm_num : (1 / 2 : ℝ) < 1)))
  have hgammaN : NumStability.gamma (p52ToFP fp) N ≤
      n * fp.u + gN * fp.u ^ 2 := by
    simpa [n, gN] using p52_gamma_quadratic fp N (by simpa [n] using hnsmall)
  have hgammaM : NumStability.gamma (p52ToFP fp) (M - 1) ≤
      k * fp.u + gM * fp.u ^ 2 := by
    simpa [k, gM] using p52_gamma_quadratic fp (M - 1) (by simpa [k] using hksmall)
  let α : Fin N → ℝ := fun i => Classical.choose (hahat i)
  have hα : ∀ i, ahat i = a i * (1 + α i) ∧
      |α i| ≤ A * fp.u + CA * fp.u ^ 2 := by
    intro i
    exact Classical.choose_spec (hahat i)
  let β : Fin M → ℝ := fun j => Classical.choose (hbhat j)
  have hβ : ∀ j, bhat j = b j * (1 + β j) ∧
      |β j| ≤ B * fp.u + CB * fp.u ^ 2 := by
    intro j
    exact Classical.choose_spec (hbhat j)
  obtain ⟨η, hη, hdot⟩ :=
    NumStability.dotProduct_backward_error (p52ToFP fp) N ahat f hvN
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.recursiveSum_backward_error (p52ToFP fp) M bhat hvM
  let w : Fin N → ℝ := fun i => (1 + α i) * (1 + η i)
  have hwerr : ∀ i, |w i - 1| ≤ (A + n) * fp.u + KN * fp.u ^ 2 := by
    intro i
    have hh := p52_combine_errors fp.u A CA n gN (α i) (η i)
      hu_nonneg hu1 hA hCA hn0 hgN (hα i).2 (le_trans (hη i) hgammaN)
    have heq : w i - 1 = α i + η i + α i * η i := by dsimp [w]; ring
    rw [heq]
    simpa [KN] using hh
  let ζ : Fin M → ℝ := fun j => β j + θ j + β j * θ j
  have hζerr : ∀ j, |ζ j| ≤ (k + B) * fp.u + KM * fp.u ^ 2 := by
    intro j
    have hh := p52_combine_errors fp.u B CB k gM (β j) (θ j)
      hu_nonneg hu1 hB hCB hk0 hgM (hβ j).2 (le_trans (hθ j) hgammaM)
    simpa [ζ, KM, add_comm, add_left_comm, add_assoc] using hh
  let D : ℝ := ∑ j : Fin M, b j
  let R : ℝ := p52RecursiveSum fp M bhat
  have hD : D ≠ 0 := hD0
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hRsum : R = ∑ j : Fin M, b j * (1 + ζ j) := by
    change p52RecursiveSum fp M bhat = _
    rw [p52_sum_eq, hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hβ j).1]
    dsimp [ζ]
    ring
  let Ld : ℝ := (k + B) * fp.u + KM * fp.u ^ 2
  have hLd : 0 ≤ Ld := by dsimp [Ld]; positivity
  have hRerr : |R - D| ≤ Ld * ∑ j : Fin M, |b j| := by
    rw [hRsum]
    exact p52_weighted_sum_error b ζ Ld hLd (by simpa [Ld] using hζerr)
  have hbabs : (∑ j : Fin M, |b j|) ≤ betaBound * |D| := by
    apply (div_le_iff₀ hDabs).mp
    simpa [p52DenominatorCondition, D] using hbetaBound
  let E : ℝ := q * fp.u + K * fp.u ^ 2
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEerr : |R - D| ≤ E * |D| := by
    calc
      |R - D| ≤ Ld * ∑ j : Fin M, |b j| := hRerr
      _ ≤ Ld * (betaBound * |D|) := mul_le_mul_of_nonneg_left hbabs hLd
      _ = E * |D| := by dsimp [Ld, E, q, K]; ring
  have hEbudget : E ≤ q * fp.u + K * fp.u ^ 2 := le_rfl
  have hElinear : E ≤ (q + K) * fp.u := by
    have hu2 : fp.u ^ 2 ≤ fp.u := by nlinarith only [hu_nonneg, hu1]
    have hh := mul_le_mul_of_nonneg_left hu2 hK
    dsimp [E]
    linarith only [hh]
  have hEhalf : E ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hqKL hu_nonneg
    linarith only [hElinear, hh, hLu]
  have hR : R ≠ 0 := by
    intro hzero
    have heq : |R - D| = |D| := by rw [hzero]; simp [abs_neg]
    rw [heq] at hEerr
    have hh : E < 1 := by linarith only [hEhalf]
    have hmul := mul_lt_mul_of_pos_right hh hDabs
    nlinarith only [hEerr, hmul]
  obtain ⟨δ, hδ, hdiv⟩ :=
    fp.model_div (p52RoundedDotProduct fp N ahat f) R hR
  let t : ℝ := D / R * (1 + δ)
  have ht : |t - 1| ≤ (1 + q) * fp.u + T * fp.u ^ 2 := by
    calc
      |t - 1| ≤ fp.u + E + 2 * (fp.u + E) * E := by
        exact p52_ratio_error D R fp.u E δ hD hR hu_nonneg hE0 hEhalf hEerr hδ
      _ ≤ (1 + q) * fp.u + T * fp.u ^ 2 := by
        simpa [T] using p52_ratio_budget fp.u q K E hu_nonneg hu1 hq hK hE0 hEbudget
  have hdot' : p52RoundedDotProduct fp N ahat f =
      ∑ i : Fin N, a i * f i * w i := by
    rw [p52_dot_eq, hdot]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hα i).1]
    dsimp [w]
    ring
  have hgerr : ∀ i, |w i * t - 1| ≤
      (A + n + 1 + q) * fp.u + C * fp.u ^ 2 := by
    intro i
    have hh := p52_combine_errors fp.u (A + n) KN (1 + q) T
      (w i - 1) (t - 1) hu_nonneg hu1 (add_nonneg hA hn0) hKN
      (by linarith) hT (hwerr i) ht
    have heq : w i * t - 1 = (w i - 1) + (t - 1) + (w i - 1) * (t - 1) := by ring
    rw [heq]
    simpa [C, add_assoc] using hh
  refine ⟨fun i => f i * (w i * t), ?_, ?_⟩
  · change fp.fl_div (p52RoundedDotProduct fp N ahat f) R =
      (∑ i : Fin N, a i * (f i * (w i * t))) / D
    rw [hdiv, hdot']
    have hfactor : (∑ i : Fin N, a i * (f i * (w i * t))) =
        (∑ i : Fin N, a i * f i * w i) * t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hfactor]
    dsimp [t]
    field_simp [hD, hR]
    <;> ring
  · have hh := p52_norm_factor_bound hN f (fun i => w i * t)
      ((A + n + 1 + q) * fp.u + C * fp.u ^ 2)
      (by positivity) hgerr
    convert hh using 1 <;> dsimp [n, k, q] <;> ring

end VSCLReuse

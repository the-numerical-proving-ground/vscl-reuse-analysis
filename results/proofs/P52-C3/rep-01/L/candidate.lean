import VSCLReuse.P52.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Recursive.Core

set_option maxHeartbeats 2000000

namespace VSCLReuse

open scoped BigOperators

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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private lemma p52_gamma_bound (k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hhalf : (k : ℝ) * t ≤ 1 / 2) :
    (k : ℝ) * t / (1 - (k : ℝ) * t) ≤
      (k : ℝ) * t + 2 * (k : ℝ) ^ 2 * t ^ 2 := by
  let z : ℝ := (k : ℝ) * t
  have hz : 0 ≤ z := mul_nonneg (Nat.cast_nonneg _) ht
  have hzhalf : z ≤ 1 / 2 := hhalf
  have hden : 0 < 1 - z := by linarith
  have hsq : 0 ≤ z ^ 2 := sq_nonneg z
  have h : z / (1 - z) ≤ z + 2 * z ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hsq (sub_nonneg.mpr (by linarith : 0 ≤ 1 - 2*z))]
  convert h using 1 <;> simp [z, mul_pow] <;> ring

private lemma p52_mul_error {t x y p q r s : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : |x| ≤ p*t + q*t^2) (hy : |y| ≤ r*t+s*t^2) :
    |(1+x)*(1+y)-1| ≤
      (p+r)*t + (q+s+(p+q)*(r+s))*t^2 := by
  have hxt : |x| ≤ (p+q)*t := by
    nlinarith [mul_nonneg hq (mul_nonneg ht (sub_nonneg.mpr ht1))]
  have hyt : |y| ≤ (r+s)*t := by
    nlinarith [mul_nonneg hs (mul_nonneg ht (sub_nonneg.mpr ht1))]
  have hxy : |x*y| ≤ (p+q)*(r+s)*t^2 := by
    rw [abs_mul]
    calc
      |x| * |y| ≤ ((p+q)*t)*((r+s)*t) :=
        mul_le_mul hxt hyt (abs_nonneg _) (mul_nonneg (by positivity) ht)
      _ = _ := by ring
  have hid : (1+x)*(1+y)-1 = x+y+x*y := by ring
  rw [hid]
  calc
    |x+y+x*y| ≤ |x|+|y|+|x*y| := by
      calc
        _ ≤ |x+y|+|x*y| := abs_add_le _ _
        _ ≤ (|x|+|y|)+|x*y| := by
          linarith [abs_add_le x y]
    _ ≤ (p*t+q*t^2)+(r*t+s*t^2)+(p+q)*(r+s)*t^2 := by gcongr
    _ = _ := by ring

private lemma p52_sum_change {n : ℕ} (v w : Fin n → ℝ) (e : ℝ)
    (h : ∀ i, |w i - v i| ≤ e * |v i|) :
    |(∑ i, w i) - ∑ i, v i| ≤ e * ∑ i, |v i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin n, (w i - v i)| ≤ ∑ i : Fin n, |w i - v i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, e * |v i| := Finset.sum_le_sum (by intro i _; exact h i)
    _ = _ := by rw [← Finset.mul_sum]

private lemma p52_abs_one_add (x : ℝ) : 1-|x| ≤ |1+x| := by
  have h := abs_add_le (1+x) (-x)
  simp only [add_neg_cancel_right, abs_one, abs_neg] at h
  linarith

private lemma p52_den_condition (M : ℕ) (b : Fin M → ℝ) (D : ℝ)
    (hD : D = ∑ j, b j) (hD0 : D ≠ 0)
    (betaBound : ℝ) (hb : p52DenominatorCondition M b ≤ betaBound) :
    (∑ j, |b j|) ≤ betaBound * |D| := by
  have hpos : 0 < |D| := abs_pos.mpr hD0
  unfold p52DenominatorCondition at hb
  rw [← hD] at hb
  exact (div_le_iff₀ hpos).mp hb

private lemma p52_norm_of_componentwise {N : ℕ} (f g : Fin N → ℝ) (e : ℝ)
    (he : 0 ≤ e) (h : ∀ i, |g i - f i| ≤ e * |f i|) :
    ‖g-f‖ ≤ e * ‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg he (norm_nonneg _))).2
  intro i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  calc
    |g i - f i| ≤ e * |f i| := h i
    _ ≤ e * ‖f‖ := mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm f i) he

private lemma p52_div_error {t x d L Q D R : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hx : |x| ≤ L*t + Q*t^2)
    (hd : |d| ≤ D*t + R*t^2)
    (hdhalf : |d| ≤ 1/2) :
    |(1+x)/(1+d)-1| ≤
      (L+D)*t + (Q+R+2*(D+R)*(L+D+Q+R))*t^2 := by
  have hd1 : |d| < 1 := by linarith
  have hden : 1+d ≠ 0 := by
    intro he
    have hdneg : d = -1 := by linarith
    have : |d| = 1 := by rw [hdneg]; norm_num
    linarith
  have hdenabs : 0 < |1+d| := abs_pos.mpr hden
  have hinv : 1 / |1+d| ≤ 1+2*|d| := by
    apply (div_le_iff₀ hdenabs).2
    have hlow := p52_abs_one_add d
    have hpos : 0 ≤ 1+2*|d| := by positivity
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hlow),
      mul_nonneg (abs_nonneg d) (sub_nonneg.mpr (by linarith : 0 ≤ 1-2*|d|))]
  have hxt : |x| ≤ (L+Q)*t := by
    nlinarith [mul_nonneg hQ (mul_nonneg ht (sub_nonneg.mpr ht1))]
  have hdt : |d| ≤ (D+R)*t := by
    nlinarith [mul_nonneg hR (mul_nonneg ht (sub_nonneg.mpr ht1))]
  have heq : (1+x)/(1+d)-1 = (x-d)/(1+d) := by
    field_simp
    ring
  rw [heq, abs_div]
  have hxd : |x-d| ≤ (L+D)*t + (Q+R)*t^2 := by
    calc
      |x-d| ≤ |x|+|d| := by simpa only [abs_neg] using (abs_add_le x (-d))
      _ ≤ (L*t+Q*t^2)+(D*t+R*t^2) := by linarith
      _ = _ := by ring
  have hxd_t : |x-d| ≤ (L+D+Q+R)*t := by
    nlinarith [hxd, mul_nonneg (add_nonneg hQ hR) (mul_nonneg ht (sub_nonneg.mpr ht1))]
  have hdiv : |x-d| / |1+d| ≤ |x-d| * (1+2*|d|) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hinv) (abs_nonneg _)
  have hcross : |x-d| * |d| ≤ (L+D+Q+R)*(D+R)*t^2 := by
    calc
      _ ≤ ((L+D+Q+R)*t)*((D+R)*t) :=
        mul_le_mul hxd_t hdt (abs_nonneg _) (mul_nonneg (by positivity) ht)
      _ = _ := by ring
  calc
    |x-d| / |1+d| ≤ |x-d| * (1+2*|d|) := hdiv
    _ = |x-d|+2*(|x-d| * |d|) := by ring
    _ ≤ ((L+D)*t+(Q+R)*t^2)+2*((L+D+Q+R)*(D+R)*t^2) := by gcongr
    _ = _ := by ring

-- PROOF_HELPERS_END

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
  let nR : ℝ := N
  let mR : ℝ := (M - 1 : ℕ)
  let qN : ℝ := 2 * nR^2
  let qM : ℝ := 2 * mR^2
  let EN : ℝ := A+nR
  let QN : ℝ := CA+qN+(A+CA)*(nR+qN)
  let ED : ℝ := B+mR
  let QD : ℝ := CB+qM+(B+CB)*(mR+qM)
  let L : ℝ := EN+1
  let Q : ℝ := QN+(EN+QN)
  let Dcoef : ℝ := ED*betaBound
  let Rcoef : ℝ := QD*betaBound
  let C : ℝ := Q+Rcoef+2*(Dcoef+Rcoef)*(L+Dcoef+Q+Rcoef)
  let S : ℝ := nR+(M:ℝ)+Dcoef+Rcoef+1
  have hnR : 0 ≤ nR := Nat.cast_nonneg _
  have hmR : 0 ≤ mR := Nat.cast_nonneg _
  have hqN : 0 ≤ qN := by dsimp [qN]; positivity
  have hqM : 0 ≤ qM := by dsimp [qM]; positivity
  have hEN : 0 ≤ EN := by dsimp [EN]; positivity
  have hQN : 0 ≤ QN := by dsimp [QN]; positivity
  have hED : 0 ≤ ED := by dsimp [ED]; positivity
  have hQD : 0 ≤ QD := by dsimp [QD]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDc : 0 ≤ Dcoef := by dsimp [Dcoef]; positivity
  have hRc : 0 ≤ Rcoef := by dsimp [Rcoef]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hMN : 0 ≤ (M:ℝ) := Nat.cast_nonneg _
  refine ⟨1/(2*S), C, by positivity, hC, ?_⟩
  intro fp ahat bhat hu hahat hbhat
  let t : ℝ := fp.u
  have ht : 0 ≤ t := fp.u_nonneg
  have hSt : 2*S*t ≤ 1 := by
    have h2S : 0 < 2*S := by positivity
    have := (le_div_iff₀ h2S).mp hu
    dsimp [t] at *
    nlinarith
  have ht1 : t ≤ 1 := by
    have hSone : 1 ≤ S := by dsimp [S]; linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hSone) ht]
  have hnHalf : nR*t ≤ 1/2 := by
    have hSn : 0 ≤ S-nR := by dsimp [S]; linarith
    nlinarith [mul_nonneg hSn ht]
  have hmHalf : mR*t ≤ 1/2 := by
    have hSm : 0 ≤ S-mR := by
      dsimp [S, mR, nR]
      have : (M-1:ℕ) ≤ M := Nat.sub_le M 1
      have hcast : ((M-1:ℕ):ℝ) ≤ (M:ℝ) := by exact_mod_cast this
      linarith [Nat.cast_nonneg (α := ℝ) N]
    nlinarith [mul_nonneg hSm ht]
  have hdcHalf : (Dcoef+Rcoef)*t ≤ 1/2 := by
    have hSd : 0 ≤ S-(Dcoef+Rcoef) := by dsimp [S]; linarith
    nlinarith [mul_nonneg hSd ht]
  let nfp := p52ToFP fp
  have hnValid : NumStability.gammaValid nfp N := by
    change (N:ℝ)*fp.u < 1
    change nR*t < 1
    linarith
  have hmValid : NumStability.gammaValid nfp (M-1) := by
    change ((M-1:ℕ):ℝ)*fp.u < 1
    change mR*t < 1
    linarith
  obtain ⟨η, hη, hdot⟩ := NumStability.dotProduct_backward_error nfp N ahat f hnValid
  obtain ⟨θ, hθ, hsum⟩ := NumStability.recursiveSum_backward_error nfp M bhat hmValid
  let α : Fin N → ℝ := fun i => Classical.choose (hahat i)
  have hα : ∀ i, ahat i = a i*(1+α i) ∧ |α i| ≤ A*t+CA*t^2 := by
    intro i
    exact Classical.choose_spec (hahat i)
  let β : Fin M → ℝ := fun j => Classical.choose (hbhat j)
  have hβ : ∀ j, bhat j = b j*(1+β j) ∧ |β j| ≤ B*t+CB*t^2 := by
    intro j
    exact Classical.choose_spec (hbhat j)
  have hηbound : ∀ i, |η i| ≤ nR*t+qN*t^2 := by
    intro i
    calc
      |η i| ≤ NumStability.gamma nfp N := hη i
      _ ≤ nR*t+qN*t^2 := by
        convert p52_gamma_bound N t ht hnHalf using 1 <;>
          simp [NumStability.gamma, nfp, p52ToFP, nR, qN]
  have hθbound : ∀ j, |θ j| ≤ mR*t+qM*t^2 := by
    intro j
    calc
      |θ j| ≤ NumStability.gamma nfp (M-1) := hθ j
      _ ≤ mR*t+qM*t^2 := by
        convert p52_gamma_bound (M-1) t ht hmHalf using 1 <;>
          simp [NumStability.gamma, nfp, p52ToFP, mR, qM]
  let exactD : ℝ := ∑ j : Fin M, b j
  let den : ℝ := p52RecursiveSum fp M bhat
  have hsum' : den = ∑ j : Fin M, bhat j*(1+θ j) := by
    simpa [den, p52RecursiveSum, NumStability.fl_recursiveSum, nfp, p52ToFP] using hsum
  have hdenrep : den = ∑ j : Fin M, b j*((1+β j)*(1+θ j)) := by
    rw [hsum']
    apply Finset.sum_congr rfl
    intro j _
    rw [(hβ j).1]
    ring
  have hdenlocal : ∀ j, |(1+β j)*(1+θ j)-1| ≤ ED*t+QD*t^2 := by
    intro j
    convert p52_mul_error ht ht1 hB hCB hmR hqM (hβ j).2 (hθbound j) using 1 <;>
      simp [ED, QD]
  have hdenchange : |den-exactD| ≤ (ED*t+QD*t^2)*(∑ j : Fin M, |b j|) := by
    rw [hdenrep]
    apply p52_sum_change
    intro j
    have hlocal := hdenlocal j
    have heq : b j*((1+β j)*(1+θ j))-b j =
        b j*((1+β j)*(1+θ j)-1) := by ring
    rw [heq, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlocal (abs_nonneg (b j))
  have hcondition : (∑ j : Fin M, |b j|) ≤ betaBound*|exactD| :=
    p52_den_condition M b exactD rfl hD0 betaBound hbetaBound
  have hEcoef : 0 ≤ ED*t+QD*t^2 := by positivity
  have hdenchange' : |den-exactD| ≤
      (ED*t+QD*t^2)*betaBound*|exactD| := by
    calc
      _ ≤ (ED*t+QD*t^2)*(∑ j : Fin M, |b j|) := hdenchange
      _ ≤ (ED*t+QD*t^2)*(betaBound*|exactD|) :=
        mul_le_mul_of_nonneg_left hcondition hEcoef
      _ = _ := by ring
  let d : ℝ := (den-exactD)/exactD
  have hexactD0 : exactD ≠ 0 := hD0
  have hDabs : 0 < |exactD| := abs_pos.mpr hexactD0
  have hd : |d| ≤ Dcoef*t+Rcoef*t^2 := by
    have h := hdenchange'
    rw [show |d| = |den-exactD|/|exactD| by simp [d, abs_div]]
    apply (div_le_iff₀ hDabs).2
    dsimp [Dcoef, Rcoef]
    nlinarith [h]
  have hdhalf : |d| ≤ 1/2 := by
    have hdt : |d| ≤ (Dcoef+Rcoef)*t := by
      nlinarith [hd, mul_nonneg hRc (mul_nonneg ht (sub_nonneg.mpr ht1))]
    linarith
  have hdenfactor : den = exactD*(1+d) := by
    dsimp [d]
    field_simp
    ring
  have hden0 : den ≠ 0 := by
    rw [hdenfactor]
    apply mul_ne_zero hexactD0
    intro hzero
    have hdneg : d = -1 := by linarith
    have habs : |d| = 1 := by rw [hdneg]; norm_num
    linarith
  have hnumrep : p52RoundedDotProduct fp N ahat f =
      ∑ i : Fin N, a i*f i*((1+α i)*(1+η i)) := by
    have hd' : p52RoundedDotProduct fp N ahat f =
        ∑ i : Fin N, ahat i*f i*(1+η i) := by
      simpa [p52RoundedDotProduct, NumStability.fl_dotProduct, nfp, p52ToFP] using hdot
    rw [hd']
    apply Finset.sum_congr rfl
    intro i _
    rw [(hα i).1]
    ring
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div (p52RoundedDotProduct fp N ahat f) den hden0
  have hδbound : |δ| ≤ (1:ℝ)*t+0*t^2 := by simpa [t] using hδ
  have hnumlocal : ∀ i, |(1+α i)*(1+η i)-1| ≤ EN*t+QN*t^2 := by
    intro i
    convert p52_mul_error ht ht1 hA hCA hnR hqN (hα i).2 (hηbound i) using 1 <;>
      simp [EN, QN]
  have htotal : ∀ i,
      |((1+α i)*(1+η i))*(1+δ)-1| ≤ L*t+Q*t^2 := by
    intro i
    have h := p52_mul_error ht ht1 hEN hQN (by norm_num : (0:ℝ) ≤ 1)
      (le_refl (0:ℝ)) (hnumlocal i) hδbound
    convert h using 1 <;> simp [L, Q]
  have hfrac : ∀ i,
      |(((1+α i)*(1+η i))*(1+δ))/(1+d)-1| ≤
        (L+Dcoef)*t+C*t^2 := by
    intro i
    have h := p52_div_error ht ht1 hL hQ hDc hRc (htotal i) hd hdhalf
    have hid : 1 + (((1+α i)*(1+η i))*(1+δ)-1) = ((1+α i)*(1+η i))*(1+δ) := by ring
    rw [hid] at h
    simpa only [C] using h
  let fhat : Fin N → ℝ := fun i =>
    f i * ((((1+α i)*(1+η i))*(1+δ))/(1+d))
  have hcomponent : ∀ i, |fhat i-f i| ≤ ((L+Dcoef)*t+C*t^2)*|f i| := by
    intro i
    have heq : fhat i-f i = f i *
        (((1+α i)*(1+η i))*(1+δ)/(1+d)-1) := by dsimp [fhat]; ring
    rw [heq, abs_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hfrac i) (abs_nonneg (f i))
  have hcoeff : ((L+Dcoef)*t+C*t^2) =
      ((((N:ℝ)+1+A)+(((M-1:ℕ):ℝ)+B)*betaBound)*fp.u+C*fp.u^2) := by
    dsimp [L, EN, Dcoef, ED, nR, mR, t]
    ring
  have hnorm : ‖fhat-f‖ ≤ ((L+Dcoef)*t+C*t^2)*‖f‖ := by
    apply p52_norm_of_componentwise f fhat
    · positivity
    · exact hcomponent
  have h1d0 : 1+d ≠ 0 := by
    intro he
    have hdneg : d = -1 := by linarith
    have habs : |d| = 1 := by rw [hdneg]; norm_num
    linarith
  have hsumfactor : (∑ i : Fin N, a i*fhat i) =
      ((∑ i : Fin N, a i*f i*((1+α i)*(1+η i)))*(1+δ))/(1+d) := by
    calc
      (∑ i : Fin N, a i*fhat i) =
          ∑ i : Fin N, (a i*f i*((1+α i)*(1+η i)))*(1+δ)/(1+d) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [fhat]
        ring
      _ = _ := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have hcomputed : p52ComputedQuotient fp N M ahat f bhat =
      ((∑ i : Fin N, a i*f i*((1+α i)*(1+η i)))/den)*(1+δ) := by
    simpa [p52ComputedQuotient, den, hnumrep] using hdiv
  refine ⟨fhat, ?_, ?_⟩
  · rw [hcomputed, hdenfactor]
    change ((∑ i : Fin N, a i*f i*((1+α i)*(1+η i))) /
        (exactD*(1+d)))*(1+δ) = (∑ i : Fin N, a i*fhat i)/exactD
    rw [hsumfactor]
    field_simp [hexactD0, h1d0]
  · rw [← hcoeff]
    exact hnorm

end VSCLReuse

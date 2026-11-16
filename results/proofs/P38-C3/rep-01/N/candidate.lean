import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators


private lemma gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u m) : 0 ≤ p38Gamma u m := by
  unfold P38GammaValid at hm
  unfold p38Gamma
  apply div_nonneg
  · positivity
  · linarith

private lemma one_add_gamma (u : ℝ) (m : ℕ)
    (hm : P38GammaValid u m) :
    1 + p38Gamma u m = 1 / (1 - (m : ℝ) * u) := by
  have h : 1 - (m : ℝ) * u ≠ 0 := by
    unfold P38GammaValid at hm
    linarith
  unfold p38Gamma
  field_simp
  ring

private lemma gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m+1)) :
    p38Gamma u m + p38Gamma u 1 +
      p38Gamma u m * p38Gamma u 1 ≤ p38Gamma u (m+1) := by
  have hm' : (m : ℝ) * u < 1 := by
    unfold P38GammaValid at hm
    push_cast at hm
    nlinarith
  have hu' : u < 1 := by
    unfold P38GammaValid at hm
    push_cast at hm
    nlinarith
  have h₁ : 0 < 1 - (m : ℝ) * u := by linarith
  have h₂ : 0 < 1 - u := by linarith
  have h₃ : 0 < 1 - ((m : ℝ) + 1) * u := by
    unfold P38GammaValid at hm
    push_cast at hm
    linarith
  have hid := one_add_gamma u m (show P38GammaValid u m from hm')
  have hid1 := one_add_gamma u 1 (show P38GammaValid u 1 by simpa [P38GammaValid] using hu')
  have hid3 := one_add_gamma u (m+1) hm
  have hden : 1 - ((m : ℝ) + 1) * u ≤
      (1 - (m : ℝ) * u) * (1-u) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg m) (sq_nonneg u)]
  have hprod : 0 < (1 - (m : ℝ) * u) * (1-u) := mul_pos h₁ h₂
  have hrec : 1 / ((1 - (m : ℝ) * u) * (1-u)) ≤
      1 / (1 - ((m : ℝ) + 1) * u) := by
    apply (div_le_div_iff₀ hprod h₃).2
    nlinarith
  have hrec' : (1 + p38Gamma u m) * (1 + p38Gamma u 1) ≤
      1 + p38Gamma u (m+1) := by
    rw [hid, hid1, hid3]
    simpa [one_div, mul_inv_rev, mul_comm] using hrec
  nlinarith

private lemma gamma_one_ge_u (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    u ≤ p38Gamma u 1 := by
  have h : 0 < 1-u := by linarith
  unfold p38Gamma
  norm_num
  apply (le_div_iff₀ h).2
  nlinarith [sq_nonneg u]

private lemma gamma_mono (u : ℝ) (m n : ℕ) (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : P38GammaValid u n) :
    p38Gamma u m ≤ p38Gamma u n := by
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hm : P38GammaValid u m := by
    unfold P38GammaValid at *
    linarith
  have hmpos : 0 < 1 - (m : ℝ) * u := by
    unfold P38GammaValid at hm
    linarith
  have hnpos : 0 < 1 - (n : ℝ) * u := by
    unfold P38GammaValid at hn
    linarith
  have hr : 1 / (1 - (m : ℝ) * u) ≤
      1 / (1 - (n : ℝ) * u) := by
    apply (div_le_div_iff₀ hmpos hnpos).2
    nlinarith
  rw [← one_add_gamma u m hm, ← one_add_gamma u n hn] at hr
  linarith

private lemma gamma_dot_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hnext : P38GammaValid u (k+1)) :
    p38Gamma u k * (1+u) + u ≤ p38Gamma u (k+1) ∧
    2*u+u^2 ≤ p38Gamma u (k+1) := by
  have hu1 : u < 1 := by
    unfold P38GammaValid at hnext
    push_cast at hnext
    have : (1 : ℝ) ≤ (k+1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ k+1)
    have h := mul_le_mul_of_nonneg_right this hu
    nlinarith
  have hku : P38GammaValid u k := by
    unfold P38GammaValid at *
    push_cast at hnext
    nlinarith
  have hG : 0 ≤ p38Gamma u k := gamma_nonneg u k hu hku
  have hG1 : u ≤ p38Gamma u 1 := gamma_one_ge_u u hu hu1
  have hstep := gamma_step u k hu hnext
  have hmulp := mul_le_mul_of_nonneg_left hG1 hG
  have hmain : p38Gamma u k * (1+u)+u ≤ p38Gamma u (k+1) := by
    nlinarith
  have htwo : P38GammaValid u 2 := by
    unfold P38GammaValid at *
    push_cast at hnext
    norm_num at *
    have hcast : (2 : ℝ) ≤ (k+1 : ℝ) := by exact_mod_cast (by omega : 2 ≤ k+1)
    have h := mul_le_mul_of_nonneg_right hcast hu
    nlinarith
  have hstep1 := gamma_step u 1 hu htwo
  have hG1nonneg : 0 ≤ p38Gamma u 1 :=
    gamma_nonneg u 1 hu (by simpa [P38GammaValid] using hu1)
  have hsq : u^2 ≤ (p38Gamma u 1)^2 := by nlinarith
  have hmono := gamma_mono u 2 (k+1) hu (by omega) hnext
  constructor
  · exact hmain
  · nlinarith

private lemma rounded_mul_error (fp : P38FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x*y| ≤ fp.u * |x*y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul x y
  rw [heq]
  calc
    |(x*y)*(1+δ)-x*y| = |x*y| * |δ| := by
      rw [show (x*y)*(1+δ)-x*y = (x*y)*δ by ring, abs_mul]
    _ ≤ fp.u * |x*y| := by nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (x*y))]

private lemma rounded_add_error (fp : P38FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x+y)| ≤ fp.u * |x+y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add x y
  rw [heq]
  calc
    |(x+y)*(1+δ)-(x+y)| = |x+y| * |δ| := by
      rw [show (x+y)*(1+δ)-(x+y) = (x+y)*δ by ring, abs_mul]
    _ ≤ fp.u * |x+y| := by nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (x+y))]

private lemma rounded_backward_error (u x y δ : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hδ : |δ| ≤ u)
    (heq : x = y * (1+δ)) :
    |x-y| ≤ p38Gamma u 1 * |x| := by
  have hq : 0 < 1+δ := by
    have := neg_abs_le δ
    linarith
  have hden : 0 < 1-u := by linarith
  have hδ' : 0 ≤ |δ| := abs_nonneg _
  have hr : |δ| / (1+δ) ≤ u/(1-u) := by
    apply (div_le_div_iff₀ hq hden).2
    have hlow := neg_abs_le δ
    nlinarith
  have hident : x-y = x*δ/(1+δ) := by
    rw [heq]
    field_simp
    ring
  rw [hident, abs_div, abs_mul, abs_of_pos hq]
  have hprod := mul_le_mul_of_nonneg_left hr (abs_nonneg x)
  simpa [p38Gamma, mul_div_assoc, mul_comm] using hprod

private lemma rounded_sub_mul_step (fp : P38FPModel) (a b c : ℝ)
    (hu : fp.u < 1) :
    |a - (fp.fl_sub a (fp.fl_mul b c) + b*c)| ≤
      p38Gamma fp.u 1 *
        (|fp.fl_sub a (fp.fl_mul b c)| + |b*c|) := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_sub a (fp.fl_mul b c)
  have hback := rounded_backward_error fp.u
      (fp.fl_sub a (fp.fl_mul b c))
      (a - fp.fl_mul b c) δ fp.u_nonneg hu hδ heq
  have hmul := rounded_mul_error fp b c
  have hu' := gamma_one_ge_u fp.u fp.u_nonneg hu
  have habs : 0 ≤ |b*c| := abs_nonneg _
  have hmul' : |fp.fl_mul b c - b*c| ≤
      p38Gamma fp.u 1 * |b*c| := by
    nlinarith [mul_le_mul_of_nonneg_right hu' habs]
  have htri : |a - (fp.fl_sub a (fp.fl_mul b c) + b*c)| ≤
      |(a - fp.fl_mul b c) - fp.fl_sub a (fp.fl_mul b c)| +
      |fp.fl_mul b c - b*c| := by
    have := abs_add_le
      ((a - fp.fl_mul b c) - fp.fl_sub a (fp.fl_mul b c))
      (fp.fl_mul b c - b*c)
    convert this using 1 <;> ring
  rw [abs_sub_comm] at hback
  nlinarith [htri]

private lemma rounded_div_step (fp : P38FPModel) (s d : ℝ)
    (hd : d ≠ 0) (hu : fp.u < 1) :
    |d * fp.fl_div s d - s| ≤
      p38Gamma fp.u 1 * |d * fp.fl_div s d| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_div s d hd
  have heq' : d * fp.fl_div s d = s * (1+δ) := by
    rw [heq]
    field_simp
  exact rounded_backward_error fp.u _ _ δ fp.u_nonneg hu hδ heq'

private lemma rounded_dot_step (fp : P38FPModel) (s b c : ℝ) :
    |fp.fl_add s (fp.fl_mul b c) - (s+b*c)| ≤
      fp.u * |s| + (2*fp.u+fp.u^2)*|b*c| := by
  let z := fp.fl_mul b c
  let a := b*c
  have hm : |z-a| ≤ fp.u*|a| := rounded_mul_error fp b c
  have ha : |fp.fl_add s z-(s+z)| ≤ fp.u*|s+z| := rounded_add_error fp s z
  have hz : |z| ≤ (1+fp.u)*|a| := by
    have h := abs_add_le (z-a) a
    have heq : z-a+a = z := by ring
    rw [heq] at h
    nlinarith
  have hsz : |s+z| ≤ |s|+|z| := abs_add_le s z
  have hdiff : |fp.fl_add s z - (s+a)| ≤
      |fp.fl_add s z-(s+z)|+|z-a| := by
    have h := abs_add_le (fp.fl_add s z-(s+z)) (z-a)
    convert h using 1 <;> ring
  have hsz' := mul_le_mul_of_nonneg_left hsz fp.u_nonneg
  have hz' := mul_le_mul_of_nonneg_left hz fp.u_nonneg
  dsimp [z, a] at *
  nlinarith

private lemma sub_fold_error (u : ℝ) (hu : 0 ≤ u) :
    ∀ (m : ℕ) (hm : P38GammaValid u m)
      (a : Fin m → ℝ) (F : ℝ → Fin m → ℝ) (b : ℝ),
      (∀ s i, |s - (F s i + a i)| ≤
        p38Gamma u 1 * (|F s i| + |a i|)) →
      |b - (Fin.foldl m F b + ∑ i : Fin m, a i)| ≤
        p38Gamma u m *
          (|Fin.foldl m F b| + ∑ i : Fin m, |a i|) := by
  intro m
  induction m with
  | zero =>
      intro hm a F b hF
      simp [p38Gamma]
  | succ m ih =>
      intro hm a F b hF
      have hm' : P38GammaValid u m := by
        unfold P38GammaValid at *
        push_cast at hm
        have : (m : ℝ) * u ≤ ((m : ℝ)+1)*u := by nlinarith
        linarith
      let s := Fin.foldl m (fun x i => F x i.castSucc) b
      let t := F s (Fin.last m)
      let A := ∑ i : Fin m, a i.castSucc
      let B := ∑ i : Fin m, |a i.castSucc|
      let c := a (Fin.last m)
      have hpre : |b - (s + A)| ≤ p38Gamma u m * (|s| + B) := by
        exact ih hm' (fun i => a i.castSucc) (fun x i => F x i.castSucc) b
          (fun x i => hF x i.castSucc)
      have hlast : |s - (t+c)| ≤ p38Gamma u 1 * (|t|+|c|) := hF s (Fin.last m)
      have hs : |s| ≤ (1+p38Gamma u 1) * (|t|+|c|) := by
        have h₁ : |s| ≤ |s-(t+c)| + |t+c| := by
          convert abs_add_le (s-(t+c)) (t+c) using 1 <;> ring
        have h₂ : |t+c| ≤ |t|+|c| := abs_add_le t c
        nlinarith
      have htri : |b - (t + (A+c))| ≤ |b-(s+A)| + |s-(t+c)| := by
        convert abs_add_le (b-(s+A)) (s-(t+c)) using 1 <;> ring
      have hg : p38Gamma u m + p38Gamma u 1 +
          p38Gamma u m * p38Gamma u 1 ≤ p38Gamma u (m+1) :=
        gamma_step u m hu hm
      have hgm : 0 ≤ p38Gamma u m := gamma_nonneg u m hu hm'
      have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      have hT : 0 ≤ |t|+|c| := by positivity
      have hgm_le : p38Gamma u m ≤ p38Gamma u (m+1) :=
        gamma_mono u m (m+1) hu (by omega) hm
      have hbound_s := mul_le_mul_of_nonneg_left hs hgm
      have hbound_T := mul_le_mul_of_nonneg_right hg hT
      have hbound_B := mul_le_mul_of_nonneg_right hgm_le hB
      simp only [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
      dsimp [s, t, A, B, c] at *
      nlinarith [hbound_s, hbound_T, hbound_B]

private lemma dot_fold_error (u : ℝ) (hu : 0 ≤ u) :
    ∀ (m : ℕ) (hm : P38GammaValid u (m+1))
      (a : Fin m → ℝ) (F : ℝ → Fin m → ℝ) (s₀ a₀ : ℝ),
      |s₀-a₀| ≤ p38Gamma u 1 * |a₀| →
      (∀ s i, |F s i-(s+a i)| ≤
        u*|s| + (2*u+u^2)*|a i|) →
      |Fin.foldl m F s₀ - (a₀ + ∑ i : Fin m, a i)| ≤
        p38Gamma u (m+1) * (|a₀| + ∑ i : Fin m, |a i|) := by
  intro m
  induction m with
  | zero =>
      intro hm a F s₀ a₀ h₀ hF
      simpa using h₀
  | succ m ih =>
      intro hm a F s₀ a₀ h₀ hF
      have hm' : P38GammaValid u (m+1) := by
        unfold P38GammaValid at *
        push_cast at hm
        have hcast : ((m+1 : ℕ) : ℝ) ≤ ((m+2 : ℕ) : ℝ) := by exact_mod_cast (by omega : m+1 ≤ m+2)
        have h := mul_le_mul_of_nonneg_right hcast hu
        norm_num at *
        linarith
      let s := Fin.foldl m (fun x i => F x i.castSucc) s₀
      let A := ∑ i : Fin m, a i.castSucc
      let B := ∑ i : Fin m, |a i.castSucc|
      let c := a (Fin.last m)
      let t := F s (Fin.last m)
      have hpre : |s - (a₀+A)| ≤
          p38Gamma u (m+1) * (|a₀|+B) := by
        exact ih hm' (fun i => a i.castSucc) (fun x i => F x i.castSucc)
          s₀ a₀ h₀ (fun x i => hF x i.castSucc)
      have hlast : |t-(s+c)| ≤ u*|s|+(2*u+u^2)*|c| :=
        hF s (Fin.last m)
      have hsize : |s| ≤ (1+p38Gamma u (m+1))*(|a₀|+B) := by
        have h₁ : |s| ≤ |s-(a₀+A)|+|a₀+A| := by
          convert abs_add_le (s-(a₀+A)) (a₀+A) using 1 <;> ring
        have h₂ : |a₀+A| ≤ |a₀|+B := by
          calc
            |a₀+A| ≤ |a₀|+|A| := abs_add_le _ _
            _ ≤ |a₀|+B := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
        nlinarith
      have htri : |t-(a₀+(A+c))| ≤ |t-(s+c)|+|s-(a₀+A)| := by
        convert abs_add_le (t-(s+c)) (s-(a₀+A)) using 1 <;> ring
      have hcoeff := gamma_dot_step u (m+1) hu (by omega) (by simpa [Nat.add_assoc] using hm)
      have hnonneg : 0 ≤ |a₀|+B := by
        have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        positivity
      have hnonnegc : 0 ≤ |c| := abs_nonneg _
      have hsize' := mul_le_mul_of_nonneg_left hsize hu
      have hcoeff₁ := mul_le_mul_of_nonneg_right hcoeff.1 hnonneg
      have hcoeff₂ := mul_le_mul_of_nonneg_right hcoeff.2 hnonnegc
      simp only [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
      dsimp [s, A, B, c, t] at *
      nlinarith [hsize', hcoeff₁, hcoeff₂]

private lemma rounded_dot_product_error (fp : P38FPModel) (n : ℕ)
    (hn : P38GammaValid fp.u n) (x y : Fin n → ℝ) :
    |p38RoundedDotProduct fp n x y - ∑ i : Fin n, x i*y i| ≤
      p38Gamma fp.u n * ∑ i : Fin n, |x i*y i| := by
  cases n with
  | zero => simp [p38RoundedDotProduct]
  | succ m =>
      have hu1 : fp.u < 1 := by
        unfold P38GammaValid at hn
        push_cast at hn
        have hcast : (1 : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m+1)
        have h := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
        nlinarith
      have h₀ : |fp.fl_mul (x 0) (y 0) - x 0*y 0| ≤
          p38Gamma fp.u 1 * |x 0*y 0| := by
        have h := rounded_mul_error fp (x 0) (y 0)
        have hγ := gamma_one_ge_u fp.u fp.u_nonneg hu1
        nlinarith [mul_le_mul_of_nonneg_right hγ (abs_nonneg (x 0*y 0))]
      have h := dot_fold_error fp.u fp.u_nonneg m hn
        (fun i => x i.succ * y i.succ)
        (fun s i => fp.fl_add s (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0)) (x 0*y 0) h₀
        (fun s i => rounded_dot_step fp s (x i.succ) (y i.succ))
      simpa only [p38RoundedDotProduct, Fin.sum_univ_succ] using h

private lemma rounded_solve_row_error (fp : P38FPModel) (m : ℕ)
    (hm : P38GammaValid fp.u (m+1))
    (a x : Fin m → ℝ) (b d : ℝ) (hd : d ≠ 0) :
    let s := Fin.foldl m
      (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) b
    let z := fp.fl_div s d
    |d*z + (∑ i : Fin m, a i*x i) - b| ≤
      p38Gamma fp.u (m+1) *
        (|d*z| + ∑ i : Fin m, |a i*x i|) := by
  have hm' : P38GammaValid fp.u m := by
    unfold P38GammaValid at *
    push_cast at hm
    norm_num at hm
    have hcast : (m : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : m ≤ m+1)
    have h := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
    push_cast at h
    linarith
  have hu : fp.u < 1 := by
    unfold P38GammaValid at hm
    have hcast : (1 : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m+1)
    have h := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
    linarith
  let F : ℝ → Fin m → ℝ := fun acc i =>
    fp.fl_sub acc (fp.fl_mul (a i) (x i))
  let s := Fin.foldl m F b
  let z := fp.fl_div s d
  let A := ∑ i : Fin m, a i*x i
  let B := ∑ i : Fin m, |a i*x i|
  have hsub : |b-(s+A)| ≤ p38Gamma fp.u m * (|s|+B) :=
    sub_fold_error fp.u fp.u_nonneg m hm'
      (fun i => a i*x i) F b
      (fun acc i => rounded_sub_mul_step fp acc (a i) (x i) hu)
  have hdiv : |d*z-s| ≤ p38Gamma fp.u 1 * |d*z| :=
    rounded_div_step fp s d hd hu
  have hs : |s| ≤ (1+p38Gamma fp.u 1)*|d*z| := by
    have h := abs_add_le (s-d*z) (d*z)
    rw [show s-d*z+d*z = s by ring, abs_sub_comm] at h
    nlinarith
  have htri : |d*z+A-b| ≤ |d*z-s|+|b-(s+A)| := by
    have h := abs_add_le (d*z-s) ((s+A)-b)
    rw [show (d*z-s)+((s+A)-b)=d*z+A-b by ring] at h
    simpa only [abs_sub_comm b (s+A)] using h
  have hg := gamma_step fp.u m fp.u_nonneg hm
  have hgm : 0 ≤ p38Gamma fp.u m := gamma_nonneg fp.u m fp.u_nonneg hm'
  have hG : p38Gamma fp.u m ≤ p38Gamma fp.u (m+1) :=
    gamma_mono fp.u m (m+1) fp.u_nonneg (by omega) hm
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hmulhs := mul_le_mul_of_nonneg_left hs hgm
  have hmulcoeff := mul_le_mul_of_nonneg_right hg (abs_nonneg (d*z))
  have hmulB := mul_le_mul_of_nonneg_right hG hB
  dsimp [F, s, z, A, B] at *
  nlinarith

private noncomputable def rowCompute (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        let j : Fin n := ⟨t.val, lt_trans t.isLt i.isLt⟩
        fp.fl_sub acc (fp.fl_mul (L i j) (x j)))
      (b i))
    (L i i)

private lemma forward_steps_preserve (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n-k → p38ForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n-k-1, by omega⟩
      let s := Fin.foldl (n-k-1)
        (fun acc (t : Fin (n-k-1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hrec : p38ForwardSubSteps fp n L b (k+1) hk x =
          p38ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' := rfl
      rw [hrec, ih]
      · have hne : i ≠ ik := by
          intro e
          have he := congrArg Fin.val e
          dsimp [ik] at he
          omega
        simp [x', hne]
      · dsimp [ik] at *
        omega

private lemma forward_steps_row (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n-k ≤ i.val →
      let y := p38ForwardSubSteps fp n L b k hk x
      y i = rowCompute fp n L b y i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      have := i.isLt
      omega
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n-k-1, by omega⟩
      let s := Fin.foldl (n-k-1)
        (fun acc (t : Fin (n-k-1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let y := p38ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hrec : p38ForwardSubSteps fp n L b (k+1) hk x = y := rfl
      rw [hrec]
      dsimp only
      by_cases heq : i.val = n-k-1
      · have hieq : i = ik := by
          apply Fin.ext
          simpa [ik] using heq
        rw [hieq]
        have hpres : y ik = x' ik := by
          exact forward_steps_preserve fp n L b k (Nat.le_of_succ_le hk)
            x' ik (by dsimp [ik]; omega)
        have hlow (t : Fin ik.val) :
            y ⟨t.val, lt_trans t.isLt ik.isLt⟩ =
              x ⟨t.val, lt_trans t.isLt ik.isLt⟩ := by
          let j : Fin n := ⟨t.val, lt_trans t.isLt ik.isLt⟩
          have hj : j.val < n-k := by
            dsimp [j, ik] at *
            omega
          have hne : j ≠ ik := by
            intro e
            have he := congrArg Fin.val e
            dsimp [j] at he
            exact (Nat.ne_of_lt t.isLt) he
          calc
            y j = x' j := forward_steps_preserve fp n L b k (Nat.le_of_succ_le hk) x' j hj
            _ = x j := by simp [x', hne]
        rw [hpres]
        simp only [rowCompute]
        simp only [x', Function.update_self]
        change fp.fl_div s (L ik ik) =
          fp.fl_div
            (Fin.foldl ik.val
              (fun acc (t : Fin ik.val) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩)
                    (y ⟨t.val, lt_trans t.isLt ik.isLt⟩)))
              (b ik))
            (L ik ik)
        congr 1
        dsimp [s, ik]
        congr 1
        funext acc t
        rw [hlow t]
      · have hi' : n-k ≤ i.val := by
          dsimp [ik] at *
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hi'

private lemma sum_lower (n : ℕ) (f : Fin n → ℝ) (i : Fin n)
    (hupper : ∀ k : Fin n, i.val < k.val → f k = 0) :
    (∑ k : Fin n, f k) =
      (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hi : i.val = n
      · have hieq : i = Fin.last n := by
          apply Fin.ext
          simpa using hi
        subst i
        rw [Fin.sum_univ_castSucc]
        congr 1
      · let i' : Fin n := ⟨i.val, by omega⟩
        have hupper' : ∀ k : Fin n, i'.val < k.val → f k.castSucc = 0 := by
          intro k hk
          exact hupper k.castSucc (by simpa [i'] using hk)
        have hlast : f (Fin.last n) = 0 := by
          apply hupper
          simp
          omega
        have hh := ih (fun k : Fin n => f k.castSucc) i' hupper'
        rw [Fin.sum_univ_castSucc, hlast, add_zero]
        convert hh using 1 <;> simp [i']

private lemma forward_sub_residual (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : P38GammaValid fp.u n) :
    ∀ i : Fin n,
      |(∑ k : Fin n, L i k * p38ForwardSub fp n L b k) - b i| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L i k| * |p38ForwardSub fp n L b k|) := by
  intro i
  let x := p38ForwardSub fp n L b
  have hrow : x i = rowCompute fp n L b x i := by
    exact forward_steps_row fp n L b n (le_refl n) (fun _ => 0) i (by simp)
  have hm : P38GammaValid fp.u (i.val+1) := by
    unfold P38GammaValid at *
    have hcast : ((i.val+1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast i.isLt
    have h := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
    linarith
  let j : Fin i.val → Fin n := fun t => ⟨t.val, lt_trans t.isLt i.isLt⟩
  let s := Fin.foldl i.val
    (fun acc (t : Fin i.val) =>
      fp.fl_sub acc (fp.fl_mul (L i (j t)) (x (j t)))) (b i)
  have hrow' : x i = fp.fl_div s (L i i) := by
    simpa only [rowCompute, s, j] using hrow
  have hlocal := rounded_solve_row_error fp i.val hm
    (fun t => L i (j t)) (fun t => x (j t)) (b i) (L i i) (hdiag i)
  dsimp only at hlocal
  have hlocal' : |L i i * x i +
      (∑ t : Fin i.val, L i (j t) * x (j t)) - b i| ≤
      p38Gamma fp.u (i.val+1) *
        (|L i i * x i| + ∑ t : Fin i.val, |L i (j t) * x (j t)|) := by
    rw [hrow']
    simpa only [s, j] using hlocal
  have hsum : (∑ k : Fin n, L i k * x k) =
      (∑ t : Fin i.val, L i (j t) * x (j t)) + L i i * x i := by
    exact sum_lower n (fun k => L i k*x k) i
      (fun k hk => by simp [hlower i k hk])
  have habssum : (∑ k : Fin n, |L i k| * |x k|) =
      (∑ t : Fin i.val, |L i (j t)| * |x (j t)|) + |L i i| * |x i| := by
    exact sum_lower n (fun k => |L i k| * |x k|) i
      (fun k hk => by simp [hlower i k hk])
  have hg : p38Gamma fp.u (i.val+1) ≤ p38Gamma fp.u n :=
    gamma_mono fp.u (i.val+1) n fp.u_nonneg (by omega) hn
  have habseq : |L i i * x i| +
      (∑ t : Fin i.val, |L i (j t) * x (j t)|) =
      (∑ k : Fin n, |L i k| * |x k|) := by
    rw [habssum]
    simp_rw [abs_mul]
    ring
  have hcoeff := mul_le_mul_of_nonneg_right hg
    (show 0 ≤ |L i i * x i| +
      (∑ t : Fin i.val, |L i (j t) * x (j t)|) by positivity)
  change |(∑ k : Fin n, L i k * x k) - b i| ≤
    p38Gamma fp.u n * (∑ k : Fin n, |L i k| * |x k|)
  calc
    |(∑ k : Fin n, L i k * x k) - b i| =
        |L i i * x i + (∑ t : Fin i.val, L i (j t) * x (j t)) - b i| := by
      rw [hsum]
      congr 1
      ring
    _ ≤ p38Gamma fp.u (i.val+1) *
        (|L i i * x i| + ∑ t : Fin i.val, |L i (j t) * x (j t)|) := hlocal'
    _ ≤ p38Gamma fp.u n * (∑ k : Fin n, |L i k| * |x k|) := by
      rw [← habseq]
      exact hcoeff

/-- The Method B off-diagonal block estimate in the proof of (6.1). -/
theorem p38_c3_methodB_offdiagonal_residual
    (fp : P38FPModel) (n r p : ℕ)
    (L22 : P38Matrix n n) (L21 : P38Matrix n r)
    (X11 : P38Matrix r p)
    (hdiag : ∀ i, L22 i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L22 i j = 0)
    (hn : P38GammaValid fp.u n)
    (hr : P38GammaValid fp.u r) :
    ∀ i j,
      |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
      p38Gamma fp.u r *
        (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
  -- PROOF_START P38-C3-H001
  intro i j
  let R : P38Matrix n p := p38MethodBOffDiagonal fp L22 L21 X11
  let Q : P38Matrix n p := p38RoundedMatMul fp L21 X11
  have hsolve :
      |(∑ k : Fin n, L22 i k * R k j) + Q i j| ≤
        p38Gamma fp.u n *
          (∑ k : Fin n, |L22 i k| * |R k j|) := by
    have h := forward_sub_residual fp n L22
      (fun k => -(Q k j)) hdiag hlower hn i
    change |(∑ k : Fin n, L22 i k * R k j) - -Q i j| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |R k j|) at h
    simpa only [sub_neg_eq_add] using h
  have hprod :
      |Q i j - (∑ k : Fin r, L21 i k * X11 k j)| ≤
        p38Gamma fp.u r *
          (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    have h := rounded_dot_product_error fp r hr
      (L21 i) (fun k => X11 k j)
    simpa only [Q, p38RoundedMatMul, abs_mul] using h
  have htri :
      |(∑ k : Fin n, L22 i k * R k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      |(∑ k : Fin n, L22 i k * R k j) + Q i j| +
      |Q i j - (∑ k : Fin r, L21 i k * X11 k j)| := by
    have h := abs_add_le
      ((∑ k : Fin n, L22 i k * R k j) + Q i j)
      ((∑ k : Fin r, L21 i k * X11 k j) - Q i j)
    rw [abs_sub_comm (∑ k : Fin r, L21 i k * X11 k j) (Q i j)] at h
    convert h using 1 <;> ring
  dsimp [R] at *
  nlinarith [htri, hsolve, hprod]

end VSCLReuse

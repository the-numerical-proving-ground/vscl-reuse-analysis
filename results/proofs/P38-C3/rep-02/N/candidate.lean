import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p38_gamma_basic (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u m) :
    0 ≤ p38Gamma u m ∧
      p38Gamma u m * (1 - (m : ℝ) * u) = (m : ℝ) * u := by
  have hmu : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hden : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hm
  constructor
  · exact div_nonneg hmu hden.le
  · simp [p38Gamma, div_mul_cancel₀ _ (ne_of_gt hden)]

private theorem p38_gamma_mono (u : ℝ) (m n : ℕ) (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : P38GammaValid u n) :
    p38Gamma u m ≤ p38Gamma u n := by
  have hmn' : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  have hm : P38GammaValid u m := lt_of_le_of_lt hmn' hn
  obtain ⟨hgm, hgm_eq⟩ := p38_gamma_basic u m hu hm
  obtain ⟨hgn, hgn_eq⟩ := p38_gamma_basic u n hu hn
  have hdm : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hm
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  nlinarith

private theorem p38_gamma_step_mul (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) :
    p38Gamma u m + u * (p38Gamma u m + 1) ≤ p38Gamma u (m + 1) := by
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hnonneg : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hm' : P38GammaValid u m := by
    dsimp [P38GammaValid] at *
    rw [hcast] at hm
    nlinarith
  obtain ⟨hgm, hgm_eq⟩ := p38_gamma_basic u m hu hm'
  obtain ⟨hgn, hgn_eq⟩ := p38_gamma_basic u (m + 1) hu hm
  rw [hcast] at hgn_eq
  have hden : 0 < 1 - ((m : ℝ) + 1) * u := by
    simpa [P38GammaValid, hcast] using (sub_pos.mpr hm)
  nlinarith

private theorem p38_gamma_step_div (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) :
    p38Gamma u m + u ≤ p38Gamma u (m + 1) * (1 - u) := by
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hnonneg : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hm' : P38GammaValid u m := by
    dsimp [P38GammaValid] at *
    rw [hcast] at hm
    nlinarith
  obtain ⟨hgm, hgm_eq⟩ := p38_gamma_basic u m hu hm'
  obtain ⟨hgn, hgn_eq⟩ := p38_gamma_basic u (m + 1) hu hm
  rw [hcast] at hgn_eq
  have hden : 0 < 1 - ((m : ℝ) + 1) * u := by
    simpa [P38GammaValid, hcast] using (sub_pos.mpr hm)
  nlinarith

private theorem p38_coeff_mul (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) {c δ : ℝ}
    (hc : |c - 1| ≤ p38Gamma u m) (hδ : |δ| ≤ u) :
    |c * (1 + δ) - 1| ≤ p38Gamma u (m + 1) := by
  let g := p38Gamma u m
  have hcabs : |c| ≤ g + 1 := by
    calc
      |c| = |(c - 1) + 1| := by ring
      _ ≤ |c - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ g + 1 := by simpa [g] using add_le_add_right hc 1
  have htri : |c * (1 + δ) - 1| ≤ |c - 1| + |c| * |δ| := by
    calc
      |c * (1 + δ) - 1| = |(c - 1) + c * δ| := by ring
      _ ≤ |c - 1| + |c * δ| := abs_add_le _ _
      _ = |c - 1| + |c| * |δ| := by rw [abs_mul]
  have hm' : P38GammaValid u m := by
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at *
    rw [hcast] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
  have hg : 0 ≤ g := (p38_gamma_basic u m hu hm').1
  have hprod : |c| * |δ| ≤ (g + 1) * u := by
    exact mul_le_mul hcabs hδ (abs_nonneg _) (by linarith)
  calc
    |c * (1 + δ) - 1| ≤ |c - 1| + |c| * |δ| := htri
    _ ≤ g + (g + 1) * u := add_le_add hc hprod
    _ ≤ p38Gamma u (m + 1) := by
      simpa [g, mul_comm u] using p38_gamma_step_mul u m hu hm

private theorem p38_coeff_div (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) {c δ : ℝ}
    (hc : |c - 1| ≤ p38Gamma u m) (hδ : |δ| ≤ u) :
    |c / (1 + δ) - 1| ≤ p38Gamma u (m + 1) := by
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1
  have hmu : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hu1 : u < 1 := by
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at hm
    rw [hcast] at hm
    nlinarith
  have hpos : 0 < 1 + δ := by linarith
  have hgn : 0 ≤ p38Gamma u (m + 1) :=
    (p38_gamma_basic u (m + 1) hu hm).1
  have hnum : |(c - 1) - δ| ≤ p38Gamma u m + u := by
    calc
      |(c - 1) - δ| ≤ |c - 1| + |δ| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (c - 1) (-δ)
      _ ≤ p38Gamma u m + u := add_le_add hc hδ
  have hbound : |(c - 1) - δ| ≤ p38Gamma u (m + 1) * (1 + δ) := by
    calc
      |(c - 1) - δ| ≤ p38Gamma u m + u := hnum
      _ ≤ p38Gamma u (m + 1) * (1 - u) := p38_gamma_step_div u m hu hm
      _ ≤ p38Gamma u (m + 1) * (1 + δ) :=
        mul_le_mul_of_nonneg_left (by linarith) hgn
  have hid : c / (1 + δ) - 1 = ((c - 1) - δ) / (1 + δ) := by
    field_simp
    <;> ring
  rw [hid, abs_div, abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr hbound

private theorem p38_mul_error (fp : P38FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul x y
  rw [heq]
  have hid : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [hid, abs_mul]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y)))

private theorem p38_sub_step (u old q new δ : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hδ : |δ| ≤ u)
    (heq : new = (old - q) * (1 + δ)) :
    |old - q - new| ≤ (u / (1 - u)) * |new| ∧
      |old| ≤ |q| + |new| / (1 - u) := by
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1
  have hpos : 0 < 1 + δ := by linarith
  have hden : 0 < 1 - u := by linarith
  have hscale : |old - q| ≤ |new| / (1 - u) := by
    apply (le_div_iff₀ hden).mpr
    rw [heq, abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  constructor
  · have hid : old - q - new = -(old - q) * δ := by rw [heq]; ring
    rw [hid, abs_mul, abs_neg]
    calc
      |old - q| * |δ| ≤ (|new| / (1 - u)) * u :=
        mul_le_mul hscale hδ (abs_nonneg _) (div_nonneg (abs_nonneg _) hden.le)
      _ = (u / (1 - u)) * |new| := by ring
  · calc
      |old| = |(old - q) + q| := by ring
      _ ≤ |old - q| + |q| := abs_add_le _ _
      _ ≤ |q| + |new| / (1 - u) := by linarith

private theorem p38_backward_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1))
    (b S A old a q new δ : ℝ)
    (hA : 0 ≤ A)
    (hprev : |b - S - old| ≤ p38Gamma u m * (A + |old|))
    (hq : |q - a| ≤ u * |a|)
    (hδ : |δ| ≤ u)
    (heq : new = (old - q) * (1 + δ)) :
    |b - (S + a) - new| ≤
      p38Gamma u (m + 1) * (A + |a| + |new|) := by
  let g := p38Gamma u m
  let G := p38Gamma u (m + 1)
  have hm' : P38GammaValid u m := by
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at *
    rw [hc] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
  have hg : 0 ≤ g := (p38_gamma_basic u m hu hm').1
  have hG : 0 ≤ G := (p38_gamma_basic u (m + 1) hu hm).1
  have hmono : g ≤ G := p38_gamma_mono u m (m + 1) hu (by omega) hm
  have hmul : g * (1 + u) + u ≤ G := by
    calc
      g * (1 + u) + u = g + u * (g + 1) := by ring
      _ ≤ G := p38_gamma_step_mul u m hu hm
  have hdiv : g + u ≤ G * (1 - u) := p38_gamma_step_div u m hu hm
  have hu1 : u < 1 := by
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at hm
    rw [hc] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
  have hd : 0 < 1 - u := by linarith
  obtain ⟨hloc, hold⟩ := p38_sub_step u old q new δ hu hu1 hδ heq
  have hqabs : |q| ≤ (1 + u) * |a| := by
    have htri : |q| ≤ |q - a| + |a| := by
      calc
        |q| = |(q - a) + a| := by ring
        _ ≤ |q - a| + |a| := abs_add_le _ _
    nlinarith
  have hold' : |old| ≤ (1 + u) * |a| + |new| / (1 - u) := by
    linarith
  have htri : |b - (S + a) - new| ≤
      |b - S - old| + |q - a| + |old - q - new| := by
    have hid : b - (S + a) - new =
        (b - S - old) + (q - a) + (old - q - new) := by ring
    rw [hid]
    calc
      |(b - S - old) + (q - a) + (old - q - new)| ≤
          |(b - S - old) + (q - a)| + |old - q - new| := abs_add_le _ _
      _ ≤ |b - S - old| + |q - a| + |old - q - new| := by
        linarith [abs_add_le (b - S - old) (q - a)]
  have hfirst : |b - (S + a) - new| ≤
      g * (A + |old|) + u * |a| + (u / (1 - u)) * |new| := by
    linarith
  have hsecond : g * (A + |old|) ≤
      g * (A + (1 + u) * |a| + |new| / (1 - u)) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hg
  have hcoefdiv : (g + u) / (1 - u) ≤ G :=
    (div_le_iff₀ hd).mpr hdiv
  have hAprod := mul_le_mul_of_nonneg_right hmono hA
  have haprod := mul_le_mul_of_nonneg_right hmul (abs_nonneg a)
  have hnprod := mul_le_mul_of_nonneg_right hcoefdiv (abs_nonneg new)
  calc
    |b - (S + a) - new| ≤
        g * (A + (1 + u) * |a| + |new| / (1 - u)) +
          u * |a| + (u / (1 - u)) * |new| := by linarith
    _ = g * A + (g * (1 + u) + u) * |a| +
          ((g + u) / (1 - u)) * |new| := by ring
    _ ≤ G * A + G * |a| + G * |new| := by linarith
    _ = G * (A + |a| + |new|) := by ring

private theorem p38_fold_sub_bound (fp : P38FPModel) :
    ∀ (m : ℕ) (b : ℝ) (a q : Fin m → ℝ),
      P38GammaValid fp.u m →
      (∀ t, |q t - a t| ≤ fp.u * |a t|) →
      |b - (∑ t : Fin m, a t) -
          Fin.foldl m (fun acc t => fp.fl_sub acc (q t)) b| ≤
        p38Gamma fp.u m *
          ((∑ t : Fin m, |a t|) +
            |Fin.foldl m (fun acc t => fp.fl_sub acc (q t)) b|) := by
  intro m
  induction m with
  | zero =>
      intro b a q hm hq
      simp [p38Gamma]
  | succ m ih =>
      intro b a q hm hq
      let old := Fin.foldl m
        (fun acc (t : Fin m) => fp.fl_sub acc (q t.castSucc)) b
      let new := fp.fl_sub old (q (Fin.last m))
      have hm' : P38GammaValid fp.u m := by
        have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        dsimp [P38GammaValid] at *
        rw [hc] at hm
        nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
      have hprev :
          |b - (∑ t : Fin m, a t.castSucc) - old| ≤
            p38Gamma fp.u m * ((∑ t : Fin m, |a t.castSucc|) + |old|) := by
        exact ih b (fun t => a t.castSucc) (fun t => q t.castSucc) hm'
          (fun t => hq t.castSucc)
      obtain ⟨δ, hδ, heq⟩ := fp.model_sub old (q (Fin.last m))
      have hstep := p38_backward_step fp.u m fp.u_nonneg hm
        b (∑ t : Fin m, a t.castSucc)
        (∑ t : Fin m, |a t.castSucc|) old
        (a (Fin.last m)) (q (Fin.last m)) new δ
        (Finset.sum_nonneg (fun t ht => abs_nonneg (a t.castSucc)))
        hprev (hq (Fin.last m)) hδ heq
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc] using hstep

private theorem p38_gamma_ge_u (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hmpos : 1 ≤ m) (hm : P38GammaValid u m) :
    u ≤ p38Gamma u m := by
  obtain ⟨hg, heq⟩ := p38_gamma_basic u m hu hm
  have hmc : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
  have hmu : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  nlinarith

private theorem p38_forward_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hmpos : 1 ≤ m) (hm : P38GammaValid u (m + 1))
    (S A old a q new δ : ℝ)
    (hA : 0 ≤ A) (hS : |S| ≤ A)
    (hprev : |old - S| ≤ p38Gamma u m * A)
    (hq : |q - a| ≤ u * |a|)
    (hδ : |δ| ≤ u)
    (heq : new = (old + q) * (1 + δ)) :
    |new - (S + a)| ≤ p38Gamma u (m + 1) * (A + |a|) := by
  let g := p38Gamma u m
  let G := p38Gamma u (m + 1)
  have hm' : P38GammaValid u m := by
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at *
    rw [hc] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hu]
  have hgm : u ≤ g := p38_gamma_ge_u u m hu hmpos hm'
  have hg : 0 ≤ g := by linarith
  have hmul : g * (1 + u) + u ≤ G := by
    calc
      g * (1 + u) + u = g + u * (g + 1) := by ring
      _ ≤ G := p38_gamma_step_mul u m hu hm
  have hnew : u * (1 + u) + u ≤ G := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hgm) hu]
  have hδabs : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  have hsum : |S + a| ≤ A + |a| :=
    (abs_add_le S a).trans (add_le_add hS (le_refl _))
  have htri : |new - (S + a)| ≤
      |old - S| * |1 + δ| + |q - a| * |1 + δ| + |S + a| * |δ| := by
    have hid : new - (S + a) =
        (old - S) * (1 + δ) + (q - a) * (1 + δ) + (S + a) * δ := by
      rw [heq]; ring
    rw [hid]
    calc
      |(old - S) * (1 + δ) + (q - a) * (1 + δ) + (S + a) * δ| ≤
          |(old - S) * (1 + δ)| + |(q - a) * (1 + δ)| + |(S + a) * δ| := by
        linarith [abs_add_le ((old - S) * (1 + δ)) ((q - a) * (1 + δ)),
          abs_add_le ((old - S) * (1 + δ) + (q - a) * (1 + δ)) ((S + a) * δ)]
      _ = _ := by simp [abs_mul]
  have h1 : |old - S| * |1 + δ| ≤ g * A * (1 + u) :=
    mul_le_mul hprev hδabs (abs_nonneg _) (mul_nonneg hg hA)
  have h2 : |q - a| * |1 + δ| ≤ u * |a| * (1 + u) :=
    mul_le_mul hq hδabs (abs_nonneg _) (mul_nonneg hu (abs_nonneg _))
  have h3 : |S + a| * |δ| ≤ (A + |a|) * u :=
    mul_le_mul hsum hδ (abs_nonneg _) (by positivity)
  have hAprod := mul_le_mul_of_nonneg_right hmul hA
  have haprod := mul_le_mul_of_nonneg_right hnew (abs_nonneg a)
  calc
    |new - (S + a)| ≤ g * A * (1 + u) + u * |a| * (1 + u) +
        (A + |a|) * u := by linarith
    _ = (g * (1 + u) + u) * A + (u * (1 + u) + u) * |a| := by ring
    _ ≤ G * A + G * |a| := by linarith
    _ = G * (A + |a|) := by ring

private theorem p38_fold_add_bound (fp : P38FPModel) :
    ∀ (m : ℕ) (a q : Fin m → ℝ),
      P38GammaValid fp.u m →
      (∀ t, |q t - a t| ≤ fp.u * |a t|) →
      |Fin.foldl m (fun acc t => fp.fl_add acc (q t)) 0 -
          (∑ t : Fin m, a t)| ≤
        p38Gamma fp.u m * (∑ t : Fin m, |a t|) := by
  intro m
  induction m with
  | zero =>
      intro a q hm hq
      simp [p38Gamma]
  | succ m ih =>
      intro a q hm hq
      by_cases hmpos : 1 ≤ m
      · let old := Fin.foldl m
          (fun acc (t : Fin m) => fp.fl_add acc (q t.castSucc)) 0
        let new := fp.fl_add old (q (Fin.last m))
        have hm' : P38GammaValid fp.u m := by
          have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          dsimp [P38GammaValid] at *
          rw [hc] at hm
          nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
        have hprev :
            |old - (∑ t : Fin m, a t.castSucc)| ≤
              p38Gamma fp.u m * (∑ t : Fin m, |a t.castSucc|) := by
          exact ih (fun t => a t.castSucc) (fun t => q t.castSucc) hm'
            (fun t => hq t.castSucc)
        obtain ⟨δ, hδ, heq⟩ := fp.model_add old (q (Fin.last m))
        have hstep := p38_forward_step fp.u m fp.u_nonneg hmpos hm
          (∑ t : Fin m, a t.castSucc)
          (∑ t : Fin m, |a t.castSucc|)
          old (a (Fin.last m)) (q (Fin.last m)) new δ
          (Finset.sum_nonneg (fun t ht => abs_nonneg (a t.castSucc)))
          (Finset.abs_sum_le_sum_abs _ _)
          hprev (hq (Fin.last m)) hδ heq
        simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc] using hstep
      · have hmzero : m = 0 := by omega
        subst m
        have hgamma : fp.u ≤ p38Gamma fp.u 1 :=
          p38_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hm
        have hq0 := hq (0 : Fin 1)
        have hmul := mul_le_mul_of_nonneg_right hgamma (abs_nonneg (a 0))
        have hbound : |q 0 - a 0| ≤ p38Gamma fp.u 1 * |a 0| :=
          hq0.trans hmul
        simpa [Fin.foldl_succ_last, fp.fl_add_zero] using hbound

private theorem p38_dot_as_fold (fp : P38FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p38RoundedDotProduct fp n x y =
      Fin.foldl n (fun acc t => fp.fl_add acc (fp.fl_mul (x t) (y t))) 0 := by
  cases n with
  | zero => simp [p38RoundedDotProduct]
  | succ n =>
      simp only [p38RoundedDotProduct, Fin.foldl_succ, fp.fl_add_zero]

private theorem p38_dot_bound (fp : P38FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P38GammaValid fp.u n) :
    |p38RoundedDotProduct fp n x y -
      (∑ t : Fin n, x t * y t)| ≤
      p38Gamma fp.u n * (∑ t : Fin n, |x t| * |y t|) := by
  rw [p38_dot_as_fold]
  have h := p38_fold_add_bound fp n (fun t => x t * y t)
    (fun t => fp.fl_mul (x t) (y t)) hn
    (fun t => p38_mul_error fp (x t) (y t))
  simpa only [abs_mul] using h

private theorem p38_scalar_solve_bound (fp : P38FPModel) (m : ℕ)
    (b d : ℝ) (a q : Fin m → ℝ)
    (hd : d ≠ 0) (hm : P38GammaValid fp.u (m + 1))
    (hq : ∀ t, |q t - a t| ≤ fp.u * |a t|) :
    let s := Fin.foldl m (fun acc t => fp.fl_sub acc (q t)) b
    let x := fp.fl_div s d
    |b - ((∑ t : Fin m, a t) + d * x)| ≤
      p38Gamma fp.u (m + 1) *
        ((∑ t : Fin m, |a t|) + |d * x|) := by
  dsimp
  let s := Fin.foldl m (fun acc t => fp.fl_sub acc (q t)) b
  let x := fp.fl_div s d
  have hm' : P38GammaValid fp.u m := by
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    dsimp [P38GammaValid] at *
    rw [hc] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
  have hprev : |b - (∑ t : Fin m, a t) - s| ≤
      p38Gamma fp.u m * ((∑ t : Fin m, |a t|) + |s|) :=
    p38_fold_sub_bound fp m b a q hm' hq
  obtain ⟨δ, hδ, heq⟩ := fp.model_div s d hd
  have hdx : d * x = (s - 0) * (1 + δ) := by
    dsimp [x]
    rw [heq]
    field_simp
    <;> ring
  have hstep := p38_backward_step fp.u m fp.u_nonneg hm
    b (∑ t : Fin m, a t) (∑ t : Fin m, |a t|)
    s 0 0 (d * x) δ
    (Finset.sum_nonneg (fun t ht => abs_nonneg (a t)))
    hprev (by simp) hδ hdx
  simpa only [add_zero, abs_zero, add_zero, sub_add_eq_sub_sub] using hstep

private theorem p38_steps_preserve (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k →
      p38ForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hi : i.val < n - k := by omega
      have hne : i ≠ ik := by
        intro heq
        have hv : i.val = n - k - 1 := by
          simpa only [ik] using congrArg Fin.val heq
        omega
      change p38ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' i hi]
      simp [x', hne]

private def p38PrefixFin {n : ℕ} (i : Fin n) (t : Fin i.val) : Fin n :=
  ⟨t.val, lt_trans t.isLt i.isLt⟩

private theorem p38_steps_row (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
      let y := p38ForwardSubSteps fp n L b k hk x
      y i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i (p38PrefixFin i t)) (y (p38PrefixFin i t))))
          (b i)) (L i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      have := i.isLt
      omega
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let y := p38ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      change y i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i (p38PrefixFin i t)) (y (p38PrefixFin i t))))
          (b i)) (L i i)
      by_cases hieq : i = ik
      · rw [hieq]
        have hpres : y ik = x' ik :=
          p38_steps_preserve fp n L b k (Nat.le_of_succ_le hk) x' ik (by dsimp [ik]; omega)
        have hpre (t : Fin ik.val) :
            y (p38PrefixFin ik t) = x (p38PrefixFin ik t) := by
          have ht : (p38PrefixFin ik t).val < n - k := by
            dsimp [p38PrefixFin, ik]
            omega
          have hne : p38PrefixFin ik t ≠ ik := by
            intro heq
            have hv : t.val = ik.val := by
              simpa only [p38PrefixFin] using congrArg Fin.val heq
            exact (Nat.ne_of_lt t.isLt) hv
          have hpr : y (p38PrefixFin ik t) = x' (p38PrefixFin ik t) :=
            p38_steps_preserve fp n L b k (Nat.le_of_succ_le hk) x'
              (p38PrefixFin ik t) ht
          rw [hpr]
          simp [x', hne]
        have hfold :
            Fin.foldl ik.val
              (fun acc (t : Fin ik.val) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik (p38PrefixFin ik t))
                    (y (p38PrefixFin ik t)))) (b ik) = s := by
          have hf :
              (fun acc (t : Fin ik.val) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik (p38PrefixFin ik t))
                    (y (p38PrefixFin ik t)))) =
              (fun acc (t : Fin ik.val) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik (p38PrefixFin ik t))
                    (x (p38PrefixFin ik t)))) := by
            funext acc t
            rw [hpre t]
          rw [hf]
          rfl
        calc
          y ik = x' ik := hpres
          _ = fp.fl_div s (L ik ik) := by simp [x']
          _ = fp.fl_div
            (Fin.foldl ik.val
              (fun acc (t : Fin ik.val) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik (p38PrefixFin ik t))
                    (y (p38PrefixFin ik t)))) (b ik)) (L ik ik) := by rw [hfold]
      · have hinext : n - k ≤ i.val := by
          have hv : ik.val = n - k - 1 := rfl
          have hneq : i.val ≠ ik.val := by
            intro heq
            exact hieq (Fin.ext heq)
          dsimp [ik] at hneq
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hinext

private theorem p38_sum_lower_row {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ k : Fin n, i.val < k.val → f k = 0) :
    (∑ k : Fin n, f k) =
      (∑ t : Fin i.val, f (p38PrefixFin i t)) + f i := by
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j, h⟩ else 0
  have htotal : (∑ k : Fin n, f k) = ∑ j ∈ Finset.range n, g j := by
    rw [Finset.sum_fin_eq_sum_range]
  have hprefix : (∑ t : Fin i.val, f (p38PrefixFin i t)) =
      ∑ j ∈ Finset.range i.val, g j := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j < i.val := Finset.mem_range.mp hj
    have hjn : j < n := by omega
    simp [g, hjn, hji, p38PrefixFin]
  have hat : g i.val = f i := by
    simp [g, i.isLt]
  have htail : (∑ j ∈ Finset.range (n - (i.val + 1)), g (i.val + 1 + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hlt : i.val + 1 + j < n
    · have hz : f ⟨i.val + 1 + j, hlt⟩ = 0 :=
        hzero _ (by dsimp; omega)
      simp [g, hlt, hz]
    · simp [g, hlt]
  have hadd : n = (i.val + 1) + (n - (i.val + 1)) := by omega
  calc
    (∑ k : Fin n, f k) = ∑ j ∈ Finset.range n, g j := htotal
    _ = ∑ j ∈ Finset.range ((i.val + 1) + (n - (i.val + 1))), g j :=
      congrArg (fun m : ℕ => ∑ j ∈ Finset.range m, g j) hadd
    _ = (∑ j ∈ Finset.range (i.val + 1), g j) +
          (∑ j ∈ Finset.range (n - (i.val + 1)), g (i.val + 1 + j)) :=
      Finset.sum_range_add _ _ _
    _ = (∑ t : Fin i.val, f (p38PrefixFin i t)) + f i := by
      rw [htail, add_zero, Finset.sum_range_succ, ← hprefix, hat]

private theorem p38_forward_sub_bound (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : P38GammaValid fp.u n) (i : Fin n) :
    let x := p38ForwardSub fp n L b
    |(∑ k : Fin n, L i k * x k) - b i| ≤
      p38Gamma fp.u n * (∑ k : Fin n, |L i k| * |x k|) := by
  dsimp
  let x := p38ForwardSub fp n L b
  have hvalid : P38GammaValid fp.u (i.val + 1) := by
    have hle : (i.val + 1 : ℕ) ≤ n := i.isLt
    have hle' : ((i.val + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hle) fp.u_nonneg
    exact lt_of_le_of_lt hle' hn
  have hgam : p38Gamma fp.u (i.val + 1) ≤ p38Gamma fp.u n :=
    p38_gamma_mono fp.u (i.val + 1) n fp.u_nonneg i.isLt hn
  have hrow : x i = fp.fl_div
      (Fin.foldl i.val
        (fun acc (t : Fin i.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L i (p38PrefixFin i t)) (x (p38PrefixFin i t))))
        (b i)) (L i i) := by
    exact p38_steps_row fp n L b n (le_refl n) (fun _ => 0) i (by simp)
  have hscalar := p38_scalar_solve_bound fp i.val (b i) (L i i)
    (fun t => L i (p38PrefixFin i t) * x (p38PrefixFin i t))
    (fun t => fp.fl_mul (L i (p38PrefixFin i t)) (x (p38PrefixFin i t)))
    (hdiag i) hvalid
    (fun t => p38_mul_error fp (L i (p38PrefixFin i t)) (x (p38PrefixFin i t)))
  dsimp at hscalar
  rw [← hrow] at hscalar
  simp_rw [abs_mul] at hscalar
  have hsum : (∑ k : Fin n, L i k * x k) =
      (∑ t : Fin i.val, L i (p38PrefixFin i t) * x (p38PrefixFin i t)) +
        L i i * x i := by
    exact p38_sum_lower_row i (fun k => L i k * x k)
      (by intro k h; change L i k * x k = 0; rw [hlower i k h]; ring)
  have habs : (∑ k : Fin n, |L i k| * |x k|) =
      (∑ t : Fin i.val, |L i (p38PrefixFin i t)| * |x (p38PrefixFin i t)|) +
        |L i i| * |x i| := by
    exact p38_sum_lower_row i (fun k => |L i k| * |x k|)
      (by intro k h; change |L i k| * |x k| = 0; rw [hlower i k h]; simp)
  have hnonneg : 0 ≤ (∑ k : Fin n, |L i k| * |x k|) :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    |(∑ k : Fin n, L i k * x k) - b i| =
        |b i - ((∑ t : Fin i.val,
          L i (p38PrefixFin i t) * x (p38PrefixFin i t)) + L i i * x i)| := by
      rw [hsum]
      exact abs_sub_comm _ _
    _ ≤ p38Gamma fp.u (i.val + 1) *
        ((∑ t : Fin i.val,
          |L i (p38PrefixFin i t)| * |x (p38PrefixFin i t)|) +
          |L i i| * |x i|) := hscalar
    _ ≤ p38Gamma fp.u n * (∑ k : Fin n, |L i k| * |x k|) := by
      rw [habs]
      exact mul_le_mul_of_nonneg_right hgam (by simpa [habs] using hnonneg)

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
  let d := p38RoundedMatMul fp L21 X11 i j
  have hsolve :
      |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) + d| ≤
        p38Gamma fp.u n *
          (∑ k : Fin n, |L22 i k| *
            |p38MethodBOffDiagonal fp L22 L21 X11 k j|) := by
    have h := p38_forward_sub_bound fp n L22
      (fun k => -(p38RoundedMatMul fp L21 X11 k j)) hdiag hlower hn i
    simpa only [p38MethodBOffDiagonal, sub_neg_eq_add] using h
  have hdot :
      |d - (∑ k : Fin r, L21 i k * X11 k j)| ≤
        p38Gamma fp.u r *
          (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    exact p38_dot_bound fp r (L21 i) (fun k => X11 k j) hr
  have hdot' :
      |(∑ k : Fin r, L21 i k * X11 k j) - d| ≤
        p38Gamma fp.u r *
          (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    simpa only [abs_sub_comm] using hdot
  calc
    |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| =
      |((∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) + d) +
        ((∑ k : Fin r, L21 i k * X11 k j) - d)| := by ring
    _ ≤ |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) + d| +
        |(∑ k : Fin r, L21 i k * X11 k j) - d| := abs_add_le _ _
    _ ≤ p38Gamma fp.u n *
          (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
        p38Gamma fp.u r *
          (∑ k : Fin r, |L21 i k| * |X11 k j|) := add_le_add hsolve hdot'

end VSCLReuse

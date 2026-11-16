import VSCLReuse.P46.Definitions

namespace VSCLReuse

open scoped BigOperators


private theorem gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u k) : 0 ≤ p46Gamma u k := by
  unfold p46Gamma P46GammaValid at *
  apply div_nonneg
  · positivity
  · linarith

private theorem gamma_mono (u : ℝ) (k n : ℕ) (hu : 0 ≤ u)
    (hkn : k ≤ n) (hn : P46GammaValid u n) :
    p46Gamma u k ≤ p46Gamma u n := by
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hk : (k : ℝ) * u < 1 := lt_of_le_of_lt hku hn
  dsimp [P46GammaValid] at hn
  unfold p46Gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (k : ℝ) * u)
    (by linarith : 0 < 1 - (n : ℝ) * u)).2
  nlinarith

private theorem gamma_step_add (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u (k + 1)) :
    (1 + u) * p46Gamma u k + u ≤ p46Gamma u (k + 1) := by
  have hku : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
    gcongr
    omega
  dsimp [P46GammaValid] at hk
  have hk' : (k : ℝ) * u < 1 := lt_of_le_of_lt hku hk
  have hkn : ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by push_cast; ring
  unfold p46Gamma
  rw [hkn]
  have hd : 0 < 1 - (k : ℝ) * u := by linarith
  have he : 0 < 1 - ((k : ℝ) * u + u) := by rw [← hkn]; linarith
  have ha : 0 ≤ (k : ℝ) * u + u := by positivity
  calc
    (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
        ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
          have hd0 : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hd]
          field_simp [ne_of_gt hd, hd0]
          ring
    _ ≤ ((k : ℝ) * u + u) / (1 - ((k : ℝ) * u + u)) := by
      apply (div_le_div_iff₀ hd he).2
      nlinarith

private theorem fp_mul_error (fp : P46FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul]
  have he : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [he, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private theorem fp_mul_abs (fp : P46FPModel) (a b : ℝ) :
    |fp.fl_mul a b| ≤ (1 + fp.u) * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul, abs_mul]
  have h : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  simpa [mul_comm] using mul_le_mul_of_nonneg_left h (abs_nonneg (a * b))

private theorem fp_add_error (fp : P46FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  rw [hadd]
  have he : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [he, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private theorem fp_dot_step (fp : P46FPModel) (r s a b : ℝ) :
    |fp.fl_add r (fp.fl_mul a b) - (s + a * b)| ≤
      (1 + fp.u) * |r - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |a * b| := by
  let v := fp.fl_mul a b
  have hm : |v - a * b| ≤ fp.u * |a * b| := fp_mul_error fp a b
  have hma : |v| ≤ (1 + fp.u) * |a * b| := fp_mul_abs fp a b
  have ha : |fp.fl_add r v - (r + v)| ≤ fp.u * |r + v| := fp_add_error fp r v
  have hs : |r + v| ≤ |r - s| + |s| + |v| := by
    calc
      |r + v| = |(r - s) + (s + v)| := by congr 1; ring
      _ ≤ |r - s| + |s + v| := abs_add_le _ _
      _ ≤ |r - s| + |s| + |v| := by linarith [abs_add_le s v]
  have he : |fp.fl_add r v - (s + a * b)| ≤
      |fp.fl_add r v - (r + v)| + |r - s| + |v - a * b| := by
    calc
      |fp.fl_add r v - (s + a * b)| =
          |(fp.fl_add r v - (r + v)) + ((r - s) + (v - a * b))| := by
            congr 1; ring
      _ ≤ |fp.fl_add r v - (r + v)| + |(r - s) + (v - a * b)| :=
        abs_add_le _ _
      _ ≤ |fp.fl_add r v - (r + v)| + |r - s| + |v - a * b| := by
        linarith [abs_add_le (r - s) (v - a * b)]
  have hu : 0 ≤ fp.u := fp.u_nonneg
  calc
    |fp.fl_add r v - (s + a * b)| ≤
        fp.u * |r + v| + |r - s| + fp.u * |a * b| := by linarith
    _ ≤ fp.u * (|r - s| + |s| + (1 + fp.u) * |a * b|) +
        |r - s| + fp.u * |a * b| := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hma), mul_nonneg hu (sub_nonneg.mpr hs)]
    _ = (1 + fp.u) * |r - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |a * b| := by ring

private theorem gamma_ge_u (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hkpos : 1 ≤ k) (hk : P46GammaValid u k) : u ≤ p46Gamma u k := by
  have h1 : P46GammaValid u 1 := by
    have hc : (1 : ℝ) * u ≤ (k : ℝ) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hkpos) hu
    simpa [P46GammaValid] using lt_of_le_of_lt hc hk
  have hmono := gamma_mono u 1 k hu hkpos hk
  have hu1 : u ≤ p46Gamma u 1 := by
    dsimp [p46Gamma, P46GammaValid] at *
    norm_num at h1 ⊢
    apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
    nlinarith
  exact le_trans hu1 hmono

private theorem gamma_step_term (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hkpos : 1 ≤ k) (hk : P46GammaValid u (k + 1)) :
    2 * u + u ^ 2 ≤ p46Gamma u (k + 1) := by
  have hsmall : P46GammaValid u k := by
    dsimp [P46GammaValid] at hk ⊢
    have hc : (k : ℝ) * u ≤ ((k+1:ℕ):ℝ) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ k + 1 by omega)) hu
    linarith
  have hge := gamma_ge_u u k hu hkpos hsmall
  have hstep := gamma_step_add u k hu hk
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hge)]

private theorem dot_fold_bound (fp : P46FPModel) (q : ℕ)
    (z₀ r₀ : ℝ) (a b : Fin q → ℝ)
    (hvalid : P46GammaValid fp.u (q + 1))
    (hr₀ : |r₀ - z₀| ≤ fp.u * |z₀|) :
    |Fin.foldl q (fun acc t => fp.fl_add acc (fp.fl_mul (a t) (b t))) r₀ -
        (z₀ + ∑ t : Fin q, a t * b t)| ≤
      p46Gamma fp.u (q + 1) *
        (|z₀| + ∑ t : Fin q, |a t * b t|) := by
  induction q with
  | zero =>
      simp only [Fin.foldl_zero]
      simp
      exact le_trans hr₀ (mul_le_mul_of_nonneg_right
        (gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hvalid) (abs_nonneg z₀))
  | succ q ih =>
      let a' : Fin q → ℝ := fun t => a t.castSucc
      let b' : Fin q → ℝ := fun t => b t.castSucc
      let r := Fin.foldl q (fun acc t => fp.fl_add acc (fp.fl_mul (a' t) (b' t))) r₀
      let s := z₀ + ∑ t : Fin q, a' t * b' t
      let w := |z₀| + ∑ t : Fin q, |a' t * b' t|
      let al := a (Fin.last q)
      let bl := b (Fin.last q)
      have hq : P46GammaValid fp.u (q + 1) := by
        dsimp [P46GammaValid] at *
        have hc : ((q+1:ℕ):ℝ) * fp.u ≤ ((q+1+1:ℕ):ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show q + 1 ≤ q + 1 + 1 by omega)) fp.u_nonneg
        linarith
      have hi : |r - s| ≤ p46Gamma fp.u (q + 1) * w := ih a' b' hq
      have hs : |s| ≤ w := by
        have hsum : |∑ t : Fin q, a' t * b' t| ≤
            ∑ t : Fin q, |a' t * b' t| := Finset.abs_sum_le_sum_abs _ _
        exact le_trans (abs_add_le _ _) (by linarith)
      have hw : 0 ≤ w := by dsimp [w]; positivity
      have hterm := gamma_step_term fp.u (q + 1) fp.u_nonneg (by omega) hvalid
      have hstep := gamma_step_add fp.u (q + 1) fp.u_nonneg hvalid
      have hmult : 0 ≤ |al * bl| := abs_nonneg _
      have hdot := fp_dot_step fp r s al bl
      have hcalc : |fp.fl_add r (fp.fl_mul al bl) - (s + al * bl)| ≤
          p46Gamma fp.u (q + 1 + 1) * (w + |al * bl|) := by
        calc
          _ ≤ (1 + fp.u) * |r - s| + fp.u * |s| +
              (2 * fp.u + fp.u ^ 2) * |al * bl| := hdot
          _ ≤ ((1 + fp.u) * p46Gamma fp.u (q + 1) + fp.u) * w +
              (2 * fp.u + fp.u ^ 2) * |al * bl| := by
                have hu : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
                nlinarith [mul_nonneg hu (sub_nonneg.mpr hi),
                  mul_nonneg fp.u_nonneg (sub_nonneg.mpr hs)]
          _ ≤ p46Gamma fp.u (q + 1 + 1) * (w + |al * bl|) := by
                nlinarith [mul_nonneg hw (sub_nonneg.mpr hstep),
                  mul_nonneg hmult (sub_nonneg.mpr hterm)]
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc, r, s, w, a', b', al,
        bl, ← add_assoc] using hcalc

private theorem rounded_dot_bound (fp : P46FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P46GammaValid fp.u n) :
    |p46RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p46Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero => simp [p46RoundedDotProduct]
  | succ q =>
      have h := dot_fold_bound fp q (x 0 * y 0) (fp.fl_mul (x 0) (y 0))
        (fun t => x t.succ) (fun t => y t.succ) hvalid
        (fp_mul_error fp (x 0) (y 0))
      simpa [p46RoundedDotProduct, Fin.sum_univ_succ] using h

private theorem fp_submul_reverse (fp : P46TriFPModel) (hu : fp.u < 1)
    (s a x : ℝ) :
    ∃ α β : ℝ,
      |α| ≤ fp.u / (1 - fp.u) ∧ |β| ≤ fp.u ∧
      s = fp.fl_sub s (fp.fl_mul a x) +
          α * fp.fl_sub s (fp.fl_mul a x) + a * x + β * (a * x) := by
  obtain ⟨β, hβ, hmul⟩ := fp.model_mul a x
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub s (fp.fl_mul a x)
  have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
  have hd : 0 < 1 + δ := by linarith
  have hd₀ : 1 + δ ≠ 0 := ne_of_gt hd
  have h1 : 0 < 1 - fp.u := by linarith
  let α := -δ / (1 + δ)
  have hα : |α| ≤ fp.u / (1 - fp.u) := by
    dsimp [α]
    rw [abs_div, abs_neg, abs_of_pos hd]
    calc
      |δ| / (1 + δ) ≤ fp.u / (1 + δ) :=
        div_le_div_of_nonneg_right hδ (le_of_lt hd)
      _ ≤ fp.u / (1 - fp.u) := by
        apply (div_le_div_iff₀ hd h1).2
        nlinarith [mul_nonneg fp.u_nonneg (show 0 ≤ δ + fp.u by linarith)]
  refine ⟨α, β, hα, hβ, ?_⟩
  rw [hmul] at hsub ⊢
  dsimp [α]
  field_simp [hd₀]
  nlinarith [hsub]

private theorem gamma_step_reverse (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u (k + 1)) :
    (p46Gamma u k + u) / (1 - u) ≤ p46Gamma u (k + 1) := by
  dsimp [P46GammaValid] at hk
  have hkn : ((k+1:ℕ):ℝ) * u = (k:ℝ) * u + u := by push_cast; ring
  have ha : 0 ≤ (k:ℝ) * u := by positivity
  have he : 0 < 1 - ((k:ℝ)*u + u) := by rw [← hkn]; linarith
  have hd : 0 < 1 - (k:ℝ)*u := by linarith
  have h1 : 0 < 1 - u := by linarith
  unfold p46Gamma
  rw [hkn]
  have hrewrite : ((k:ℝ)*u / (1-(k:ℝ)*u) + u) / (1-u) =
      ((k:ℝ)*u + u - u*((k:ℝ)*u)) /
        ((1-(k:ℝ)*u)*(1-u)) := by
    have hd₀ : 1 - u * (k:ℝ) ≠ 0 := by nlinarith [hd]
    field_simp [ne_of_gt hd, ne_of_gt h1, hd₀]
    ring
  rw [hrewrite]
  apply (div_le_div_iff₀ (mul_pos hd h1) he).2
  nlinarith [mul_nonneg ha hu]

private theorem reverse_error_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u (k + 1))
    (base s t q w z α β : ℝ)
    (hw : 0 ≤ w)
    (hprev : |base - (s + q)| ≤ p46Gamma u k * (|s| + w))
    (hα : |α| ≤ u / (1 - u)) (hβ : |β| ≤ u)
    (hs : s = t + α * t + z + β * z) :
    |base - (t + (q + z))| ≤
      p46Gamma u (k + 1) * (|t| + (w + |z|)) := by
  have hk₀ : P46GammaValid u k := by
    dsimp [P46GammaValid] at hk ⊢
    have hc : (k:ℝ)*u ≤ ((k+1:ℕ):ℝ)*u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ k+1 by omega)) hu
    linarith
  let g := p46Gamma u k
  let G := p46Gamma u (k + 1)
  have hg : 0 ≤ g := gamma_nonneg u k hu hk₀
  have hG : 0 ≤ G := gamma_nonneg u (k + 1) hu hk
  have hmono : g ≤ G := gamma_mono u k (k+1) hu (by omega) hk
  have h1 : 0 < 1 - u := by
    have hklt : ((k+1:ℕ):ℝ)*u < 1 := hk
    have hc : u ≤ ((k+1:ℕ):ℝ)*u := by
      have hn : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hn)]
    linarith
  have hct : g + (g + 1) * |α| ≤ G := by
    have hmul : (g + 1) * |α| ≤ (g + 1) * (u / (1-u)) :=
      mul_le_mul_of_nonneg_left hα (by linarith)
    have heq : g + (g + 1) * (u / (1-u)) = (g+u)/(1-u) := by
      field_simp [ne_of_gt h1]
      ring
    calc
      _ ≤ g + (g + 1) * (u / (1-u)) := by linarith
      _ = (g+u)/(1-u) := heq
      _ ≤ G := gamma_step_reverse u k hu hk
  have hcz : g + (g + 1) * |β| ≤ G := by
    have hmul : (g + 1) * |β| ≤ (g + 1) * u :=
      mul_le_mul_of_nonneg_left hβ (by linarith)
    have hstep := gamma_step_add u k hu hk
    nlinarith
  have hsabs : |s| ≤ (1 + |α|) * |t| + (1 + |β|) * |z| := by
    rw [hs]
    rw [show t + α*t + z + β*z = (t + α*t) + (z + β*z) by ring]
    have hA := abs_add_le (t + α*t) (z + β*z)
    have hB := abs_add_le t (α*t)
    have hC := abs_add_le z (β*z)
    rw [abs_mul] at hB hC
    nlinarith [hA, hB, hC]
  have he : |base - (t + (q + z))| ≤
      |base - (s + q)| + |α| * |t| + |β| * |z| := by
    have heq : base - (t + (q + z)) = (base - (s + q)) + α*t + β*z := by
      rw [hs]
      ring
    rw [heq]
    have hA := abs_add_le ((base - (s + q)) + α*t) (β*z)
    have hB := abs_add_le (base - (s + q)) (α*t)
    rw [abs_mul] at hA hB
    linarith
  have htw : 0 ≤ |t| := abs_nonneg _
  have hzw : 0 ≤ |z| := abs_nonneg _
  calc
    _ ≤ g * (|s| + w) + |α| * |t| + |β| * |z| := by linarith
    _ ≤ g * ((1 + |α|) * |t| + (1 + |β|) * |z| + w) +
          |α| * |t| + |β| * |z| := by
      nlinarith [mul_nonneg hg (sub_nonneg.mpr hsabs)]
    _ = (g + (g + 1)*|α|)*|t| + g*w +
          (g + (g + 1)*|β|)*|z| := by ring
    _ ≤ G * (|t| + (w + |z|)) := by
      nlinarith [mul_nonneg htw (sub_nonneg.mpr hct),
        mul_nonneg hw (sub_nonneg.mpr hmono),
        mul_nonneg hzw (sub_nonneg.mpr hcz)]

private theorem sub_fold_bound (fp : P46TriFPModel) (q : ℕ)
    (base : ℝ) (a x : Fin q → ℝ)
    (hvalid : P46GammaValid fp.u (q + 1)) :
    |base - (Fin.foldl q
        (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) base +
        ∑ t : Fin q, a t * x t)| ≤
      p46Gamma fp.u q *
        (|Fin.foldl q
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) base| +
          ∑ t : Fin q, |a t * x t|) := by
  induction q with
  | zero => simp [p46Gamma]
  | succ q ih =>
      let a' : Fin q → ℝ := fun t => a t.castSucc
      let x' : Fin q → ℝ := fun t => x t.castSucc
      let r := Fin.foldl q
        (fun acc t => fp.fl_sub acc (fp.fl_mul (a' t) (x' t))) base
      let t := fp.fl_sub r (fp.fl_mul (a (Fin.last q)) (x (Fin.last q)))
      let z := a (Fin.last q) * x (Fin.last q)
      let sm := ∑ j : Fin q, a' j * x' j
      let w := ∑ j : Fin q, |a' j * x' j|
      have hq : P46GammaValid fp.u (q + 1) := by
        dsimp [P46GammaValid] at hvalid ⊢
        have hc : ((q+1:ℕ):ℝ)*fp.u ≤ ((q+1+1:ℕ):ℝ)*fp.u :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast (show q+1 ≤ q+1+1 by omega)) fp.u_nonneg
        linarith
      have hu : fp.u < 1 := by
        have hc : fp.u ≤ ((q+1+1:ℕ):ℝ)*fp.u := by
          have hn : (1:ℝ) ≤ (q+1+1:ℕ) := by
            exact_mod_cast (show 1 ≤ q+1+1 by omega)
          nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hn)]
        exact lt_of_le_of_lt hc hvalid
      have hi : |base - (r + sm)| ≤ p46Gamma fp.u q * (|r| + w) :=
        ih a' x' hq
      have hw : 0 ≤ w := by dsimp [w]; positivity
      obtain ⟨α, β, hα, hβ, hrepr⟩ :=
        fp_submul_reverse fp hu r (a (Fin.last q)) (x (Fin.last q))
      have hcalc : |base - (t + (sm + z))| ≤
          p46Gamma fp.u (q + 1) * (|t| + (w + |z|)) :=
        reverse_error_step fp.u q fp.u_nonneg hq base r t sm w z α β
          hw hi hα hβ hrepr
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc, r, t, z, sm, w,
        a', x', ← add_assoc] using hcalc

private theorem fp_div_reverse (fp : P46TriFPModel) (hu : fp.u < 1)
    (s d : ℝ) (hd : d ≠ 0) :
    ∃ α : ℝ, |α| ≤ fp.u / (1 - fp.u) ∧
      s = d * fp.fl_div s d + α * (d * fp.fl_div s d) := by
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s d hd
  have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
  have hden : 0 < 1 + δ := by linarith
  have hden₀ : 1 + δ ≠ 0 := ne_of_gt hden
  have h1 : 0 < 1 - fp.u := by linarith
  let α := -δ / (1 + δ)
  have hα : |α| ≤ fp.u / (1 - fp.u) := by
    dsimp [α]
    rw [abs_div, abs_neg, abs_of_pos hden]
    calc
      |δ| / (1+δ) ≤ fp.u/(1+δ) := div_le_div_of_nonneg_right hδ (le_of_lt hden)
      _ ≤ fp.u/(1-fp.u) := by
        apply (div_le_div_iff₀ hden h1).2
        nlinarith [mul_nonneg fp.u_nonneg (show 0 ≤ δ + fp.u by linarith)]
  refine ⟨α, hα, ?_⟩
  rw [hdiv]
  dsimp [α]
  field_simp [hd, hden₀]
  ring

private theorem sub_fold_div_bound (fp : P46TriFPModel) (q : ℕ)
    (base d : ℝ) (a x : Fin q → ℝ)
    (hd : d ≠ 0) (hvalid : P46GammaValid fp.u (q + 1)) :
    let s := Fin.foldl q
      (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) base
    let xi := fp.fl_div s d
    |base - (d * xi + ∑ t : Fin q, a t * x t)| ≤
      p46Gamma fp.u (q + 1) *
        (|d * xi| + ∑ t : Fin q, |a t * x t|) := by
  dsimp
  let s := Fin.foldl q
    (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) base
  let xi := fp.fl_div s d
  let sm := ∑ t : Fin q, a t * x t
  let w := ∑ t : Fin q, |a t * x t|
  have hprev : |base - (s + sm)| ≤ p46Gamma fp.u q * (|s| + w) :=
    sub_fold_bound fp q base a x hvalid
  have hu : fp.u < 1 := by
    have hc : fp.u ≤ ((q+1:ℕ):ℝ)*fp.u := by
      have hn : (1:ℝ) ≤ (q+1:ℕ) := by exact_mod_cast (show 1 ≤ q+1 by omega)
      nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hn)]
    exact lt_of_le_of_lt hc hvalid
  obtain ⟨α, hα, hrepr⟩ := fp_div_reverse fp hu s d hd
  have hresult := reverse_error_step fp.u q fp.u_nonneg hvalid
    base s (d * xi) sm w 0 α 0 (by dsimp [w]; positivity)
    hprev hα (by simp [fp.u_nonneg]) (by simpa [xi] using hrepr)
  simpa [sm, w, xi, s] using hresult

private theorem steps_preserve_ge (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (i : Fin n) (hi : k ≤ i.val) :
    p46BackSubSteps fp n U b k hk x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hkn : k < n := hk
      let ik : Fin n := ⟨k, hkn⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      change p46BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' (by omega)]
      dsimp [x']
      exact Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [ik] at this; omega) _ _

private theorem steps_row (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (i : Fin n) (hi : i.val < k) :
    let y := p46BackSubSteps fp n U b k hk x
    y i = fp.fl_div
      (Fin.foldl (n - i.val - 1)
        (fun acc (t : Fin (n - i.val - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
              (y ⟨i.val + 1 + t.val, by omega⟩)))
        (b i)) (U i i) := by
  induction k generalizing x i with
  | zero => omega
  | succ k ih =>
      have hkn : k < n := hk
      let ik : Fin n := ⟨k, hkn⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      let y := p46BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      change y i = fp.fl_div
        (Fin.foldl (n - i.val - 1)
          (fun acc (t : Fin (n - i.val - 1)) =>
            fp.fl_sub acc
              (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                (y ⟨i.val + 1 + t.val, by omega⟩)))
          (b i)) (U i i)
      by_cases hik : i.val < k
      · exact ih (Nat.le_of_succ_le hk) x' i hik
      · have hieq : i = ik := Fin.ext (by dsimp [ik]; omega)
        subst i
        have hpres : y ik = x' ik :=
          steps_preserve_ge fp n U b k (Nat.le_of_succ_le hk) x' ik (by dsimp [ik]; omega)
        have hval : y ik = fp.fl_div s (U ik ik) := by
          rw [hpres]
          simp [x']
        have hy (t : Fin count) :
            y ⟨k + 1 + t.val, by omega⟩ = x ⟨k + 1 + t.val, by omega⟩ := by
          have hj : k ≤ (⟨k + 1 + t.val, by omega⟩ : Fin n).val := by simp; omega
          dsimp [y]
          rw [steps_preserve_ge fp n U b k (Nat.le_of_succ_le hk) x' _ hj]
          dsimp [x']
          exact Function.update_of_ne
            (by intro h; have := congrArg Fin.val h; dsimp [ik] at this; omega) _ _
        rw [hval]
        have hfold : Fin.foldl count
          (fun acc (t : Fin count) =>
            fp.fl_sub acc
              (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
                (y ⟨k + 1 + t.val, by omega⟩)))
          (b ik) = s := by
          dsimp [s]
          congr 1
          funext acc t
          rw [hy t]
        simpa [count, ik] using (congrArg (fun z => fp.fl_div z (U ik ik)) hfold).symm

private theorem fin_sum_upper {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ := by
  let q := n - i.val - 1
  let g (k : ℕ) : ℝ := if h : k < n then f ⟨k, h⟩ else 0
  have hn : n = i.val + 1 + q := by dsimp [q]; omega
  have hfull : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    rw [Finset.sum_fin_eq_sum_range]
  have hlow : (∑ k ∈ Finset.range i.val, g k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < i.val := Finset.mem_range.mp hk
    have hkn : k < n := lt_trans hklt i.isLt
    simp [g, hkn, hzero ⟨k, hkn⟩ hklt]
  have hdiag : g i.val = f i := by simp [g, i.isLt]
  let g₂ (k : ℕ) : ℝ := if h : i.val + 1 + k < n then
    f ⟨i.val + 1 + k, h⟩ else 0
  have htail : (∑ t : Fin q, f ⟨i.val + 1 + t.val, by omega⟩) =
      ∑ k ∈ Finset.range q, g₂ k := by
    calc
      _ = ∑ t : Fin q, g₂ t.val := by
        apply Finset.sum_congr rfl
        intro t _
        have ht : i.val + 1 + t.val < n := by dsimp [q] at t; omega
        simp [g₂, ht]
      _ = ∑ k ∈ Finset.range q, g₂ k := Fin.sum_univ_eq_sum_range g₂ q
  calc
    (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := hfull
    _ = (∑ k ∈ Finset.range (i.val + 1), g k) +
        ∑ k ∈ Finset.range q, g (i.val + 1 + k) := by
          have hset : Finset.range n = Finset.range (i.val + 1 + q) :=
            congrArg Finset.range hn
          rw [hset, Finset.sum_range_add]
    _ = f i + ∑ k ∈ Finset.range q, g₂ k := by
      rw [Finset.sum_range_succ, hlow, hdiag, zero_add]
    _ = f i + ∑ t : Fin q, f ⟨i.val + 1 + t.val, by omega⟩ := by rw [htail]

private theorem backsub_residual (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hvalid : P46GammaValid fp.u n)
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin n) :
    |(∑ j : Fin n, U i j * p46BackSub fp n U b j) - b i| ≤
      p46Gamma fp.u n *
        ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j| := by
  let y := p46BackSub fp n U b
  let q := n - i.val - 1
  let a : Fin q → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
  let x : Fin q → ℝ := fun t => y ⟨i.val + 1 + t.val, by omega⟩
  have hqle : q + 1 ≤ n := by dsimp [q]; omega
  have hqvalid : P46GammaValid fp.u (q + 1) := by
    have hc : ((q+1:ℕ):ℝ)*fp.u ≤ (n:ℝ)*fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hqle) fp.u_nonneg
    exact lt_of_le_of_lt hc hvalid
  have hrow : y i = fp.fl_div
      (Fin.foldl q
        (fun acc (t : Fin q) => fp.fl_sub acc (fp.fl_mul (a t) (x t)))
        (b i)) (U i i) := by
    simpa [y, q, a, x, p46BackSub] using
      (steps_row fp n U b n (le_refl n) (fun _ => 0) i i.isLt)
  have hlocal := sub_fold_div_bound fp q (b i) (U i i) a x
    (hUdiag i) hqvalid
  dsimp at hlocal
  rw [← hrow] at hlocal
  have hsum : (∑ j : Fin n, U i j * y j) =
      U i i * y i + ∑ t : Fin q, a t * x t := by
    simpa [a, x, q] using
      (fin_sum_upper i (fun j => U i j * y j)
        (by intro j hj; simp [hUupper i j hj]))
  have habs : (∑ j : Fin n, |U i j| * |y j|) =
      |U i i * y i| + ∑ t : Fin q, |a t * x t| := by
    simpa [a, x, q, abs_mul] using
      (fin_sum_upper i (fun j => |U i j * y j|)
        (by intro j hj; simp [hUupper i j hj]))
  have hw : 0 ≤ ∑ j : Fin n, |U i j| * |y j| := by positivity
  have hgamma := gamma_mono fp.u (q + 1) n fp.u_nonneg hqle hvalid
  change |(∑ j : Fin n, U i j * y j) - b i| ≤
    p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |y j|
  rw [hsum, habs]
  rw [habs] at hw
  calc
    |U i i * y i + ∑ t : Fin q, a t * x t - b i| =
        |b i - (U i i * y i + ∑ t : Fin q, a t * x t)| := abs_sub_comm _ _
    _ ≤ p46Gamma fp.u (q + 1) *
      (|U i i * y i| + ∑ t : Fin q, |a t * x t|) := hlocal
    _ ≤ p46Gamma fp.u n *
      (|U i i * y i| + ∑ t : Fin q, |a t * x t|) :=
        mul_le_mul_of_nonneg_right hgamma hw

private theorem gamma_size_bound (u ulow : ℝ) (n : ℕ)
    (hu : 0 < u) (hlow : 0 ≤ ulow)
    (hvalid : P46GammaValid u n)
    (hsize : (n : ℝ) ≤ ulow / (u * (1 + 2 * ulow))) :
    (1 + ulow) * p46Gamma u n ≤ ulow := by
  have hd : 0 < u * (1 + 2 * ulow) := by positivity
  have hs : (n : ℝ) * (u * (1 + 2 * ulow)) ≤ ulow :=
    (le_div_iff₀ hd).1 hsize
  have hv : 0 < 1 - (n : ℝ) * u := by
    dsimp [P46GammaValid] at hvalid
    linarith
  unfold p46Gamma
  calc
    (1 + ulow) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) =
        ((1 + ulow) * ((n : ℝ) * u)) / (1 - (n : ℝ) * u) := by ring
    _ ≤ ulow := (div_le_iff₀ hv).2 (by nlinarith [hs])

/-- Section 3.2: high-precision kernels rounded once to low precision. -/
theorem p46_c3_simulated_product_and_triangular_solve
    (fp : P46TriFPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hu : 0 < fp.u)
    (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    (∀ i j,
      |p46SimulatedMatMul fp.toP46FPModel A B i j - p46MatMul A B i j| ≤
        2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j) ∧
    (∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j|) := by
  -- PROOF_START P46-C3-H001
  constructor
  · intro i j
    let e := p46MatMul A B i j
    let h := p46RoundedMatMul fp.toP46FPModel A B i j
    let l := p46SimulatedMatMul fp.toP46FPModel A B i j
    let w := p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j
    have hw : 0 ≤ w := by
      dsimp [w, p46MatMul, p46AbsMatrix]
      positivity
    have heabs : |e| ≤ w := by
      dsimp [e, w, p46MatMul, p46AbsMatrix]
      simpa [abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (f := fun k : Fin n => A i k * B k j))
    have hhigh : |h - e| ≤ p46Gamma fp.u n * w := by
      simpa [h, e, w, p46RoundedMatMul, p46MatMul, p46AbsMatrix, abs_mul] using
        (rounded_dot_bound fp.toP46FPModel n (A i) (fun k => B k j) hvalid)
    have hlow : |l - h| ≤ fp.u_low * |h| := by
      simpa [l, h, p46SimulatedMatMul, p46RoundedMatMul] using
        (fp.model_low h)
    have hhabs : |h| ≤ p46Gamma fp.u n * w + w := by
      have ha := abs_add_le (h - e) e
      have heq : h - e + e = h := by ring
      rw [heq] at ha
      linarith
    have hcoef : (1 + fp.u_low) * p46Gamma fp.u n ≤ fp.u_low :=
      gamma_size_bound fp.u fp.u_low n hu fp.u_low_nonneg hvalid hsize
    change |l - e| ≤ 2 * fp.u_low * w
    have htri : |l - e| ≤ |l - h| + |h - e| := by
      convert abs_add_le (l - h) (h - e) using 1 <;> ring
    calc
      |l - e| ≤ |l - h| + |h - e| := htri
      _ ≤ fp.u_low * |h| + p46Gamma fp.u n * w := by linarith
      _ ≤ fp.u_low * (p46Gamma fp.u n * w + w) +
          p46Gamma fp.u n * w := by
            nlinarith [mul_nonneg fp.u_low_nonneg (sub_nonneg.mpr hhabs)]
      _ = ((1 + fp.u_low) * p46Gamma fp.u n + fp.u_low) * w := by ring
      _ ≤ 2 * fp.u_low * w := by
        nlinarith [mul_nonneg hw (sub_nonneg.mpr hcoef)]
  · intro i
    let y := p46BackSub fp n U b
    let z := p46SimulatedBackSub fp n U b
    let w := ∑ j : Fin n, |U i j| * |y j|
    have hlow (j : Fin n) : |z j - y j| ≤ fp.u_low * |y j| := by
      simpa [z, y, p46SimulatedBackSub] using fp.model_low (y j)
    have hchange : |(∑ j : Fin n, U i j * z j) -
        ∑ j : Fin n, U i j * y j| ≤ fp.u_low * w := by
      calc
        _ = |∑ j : Fin n, U i j * (z j - y j)| := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ∑ j : Fin n, |U i j * (z j - y j)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |U i j| * |z j - y j| := by simp_rw [abs_mul]
        _ ≤ ∑ j : Fin n, |U i j| * (fp.u_low * |y j|) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hlow j) (abs_nonneg _)
        _ = fp.u_low * w := by
          dsimp [w]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    have hhigh : |(∑ j : Fin n, U i j * y j) - b i| ≤
        p46Gamma fp.u n * w :=
      backsub_residual fp n U b hvalid hUdiag hUupper i
    change |(∑ j : Fin n, U i j * z j) - b i| ≤
      (p46Gamma fp.u n + fp.u_low) * w
    calc
      _ ≤ |(∑ j : Fin n, U i j * z j) - ∑ j : Fin n, U i j * y j| +
          |(∑ j : Fin n, U i j * y j) - b i| := by
            convert abs_add_le
              ((∑ j : Fin n, U i j * z j) - ∑ j : Fin n, U i j * y j)
              ((∑ j : Fin n, U i j * y j) - b i) using 1 <;> ring
      _ ≤ fp.u_low * w + p46Gamma fp.u n * w := by linarith
      _ = (p46Gamma fp.u n + fp.u_low) * w := by ring

end VSCLReuse

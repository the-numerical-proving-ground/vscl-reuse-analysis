import VSCLReuse.P04.Definitions

namespace VSCLReuse

private theorem p04_flAdd_abs_error (model : P04WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤ model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hfl⟩ := model.add_model a b
  rw [hfl]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have ha : |a * θa| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hθa (abs_nonneg a)
  have hb : |b * θb| ≤ |b| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hθb (abs_nonneg b)
  have htri := abs_add_le (a * θa) (b * θb)
  have heq : a * (1 + θa * model.epsilon) + b * (1 + θb * model.epsilon) -
      (a + b) = model.epsilon * (a * θa + b * θb) := by ring
  rw [heq, abs_mul, abs_of_nonneg hε]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add ha hb) hε]

private theorem p04_flMul_abs_error (model : P04WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * |a * b| := by
  obtain ⟨θ, hθ, hfl⟩ := model.mul_model a b
  rw [hfl]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have heq : a * b * (1 + θ * model.epsilon) - a * b =
      model.epsilon * ((a * b) * θ) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left
    (by simpa using mul_le_mul_of_nonneg_left hθ (abs_nonneg (a * b))) hε

private theorem p04_complex_diag_norm_le (x : ℂ) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(⟨a * x.re, b * x.im⟩ : ℂ)‖ ≤ ‖x‖ := by
  have ha2 : a ^ 2 ≤ 1 := by
    have h : a ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa only [abs_one] using ha)
    simpa using h
  have hb2 : b ^ 2 ≤ 1 := by
    have h : b ^ 2 ≤ (1 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa only [abs_one] using hb)
    simpa using h
  have hsq : ‖(⟨a * x.re, b * x.im⟩ : ℂ)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg x.re, sq_nonneg x.im,
      mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg x.re),
      mul_nonneg (sub_nonneg.mpr hb2) (sq_nonneg x.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem p04_roundedComplexAdd_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  obtain ⟨ar, br, har, hbr, hr⟩ := model.add_model x.re y.re
  obtain ⟨ai, bi, hai, hbi, hi⟩ := model.add_model x.im y.im
  let u : ℂ := ⟨ar * x.re, ai * x.im⟩
  let v : ℂ := ⟨br * y.re, bi * y.im⟩
  have hu : ‖u‖ ≤ ‖x‖ := p04_complex_diag_norm_le x ar ai har hai
  have hv : ‖v‖ ≤ ‖y‖ := p04_complex_diag_norm_le y br bi hbr hbi
  have heq : p04RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * (u + v) := by
    apply Complex.ext <;>
      simp [p04RoundedComplexAdd, hr, hi, u, v, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [heq, norm_mul]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  exact (mul_le_mul_of_nonneg_left (le_trans (norm_add_le u v) (add_le_add hu hv)) hε)

private def p04_roundedRealScale (model : P04WilkinsonModel) (a : ℝ) (x : ℂ) : ℂ :=
  ⟨model.flMul a x.re, model.flMul a x.im⟩

private theorem p04_roundedRealScale_error (model : P04WilkinsonModel)
    (a : ℝ) (x : ℂ) :
    ‖p04_roundedRealScale model a x - (a : ℂ) * x‖ ≤
      model.epsilon * |a| * ‖x‖ := by
  obtain ⟨tr, htr, hr⟩ := model.mul_model a x.re
  obtain ⟨ti, hti, hi⟩ := model.mul_model a x.im
  let u : ℂ := ⟨tr * x.re, ti * x.im⟩
  have hu : ‖u‖ ≤ ‖x‖ := p04_complex_diag_norm_le x tr ti htr hti
  have heq : p04_roundedRealScale model a x - (a : ℂ) * x =
      ((model.epsilon * a : ℝ) : ℂ) * u := by
    apply Complex.ext <;>
      simp [p04_roundedRealScale, hr, hi, u, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [heq, norm_mul]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left hu (mul_nonneg hε (abs_nonneg a))

private theorem p04_roundedRealScale_norm (model : P04WilkinsonModel)
    (a : ℝ) (x : ℂ) :
    ‖p04_roundedRealScale model a x‖ ≤
      (1 + model.epsilon) * |a| * ‖x‖ := by
  have h := p04_roundedRealScale_error model a x
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    ‖p04_roundedRealScale model a x‖ =
        ‖(p04_roundedRealScale model a x - (a : ℂ) * x) + (a : ℂ) * x‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖p04_roundedRealScale model a x - (a : ℂ) * x‖ + ‖(a : ℂ) * x‖ :=
      norm_add_le _ _
    _ ≤ model.epsilon * |a| * ‖x‖ + |a| * ‖x‖ := by
      gcongr
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using h
    _ = (1 + model.epsilon) * |a| * ‖x‖ := by ring

private theorem p04_complex_abs_parts_le (x : ℂ) :
    |x.re| + |x.im| ≤ Real.sqrt 2 * ‖x‖ := by
  have h2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hs : (|x.re| + |x.im|) ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := by
    nlinarith [sq_nonneg (|x.re| - |x.im|), sq_abs x.re, sq_abs x.im]
  exact (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hs

private theorem p04_roundedComplexMul_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      Real.sqrt 2 * (2 * model.epsilon + model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  let u := p04_roundedRealScale model x.re y
  let v := Complex.I * p04_roundedRealScale model x.im y
  have huv : p04RoundedComplexMul model x y =
      p04RoundedComplexAdd model u v := by
    apply Complex.ext <;>
      simp [p04RoundedComplexMul, p04RoundedComplexAdd, p04_roundedRealScale,
        u, v, Complex.mul_re, Complex.mul_im] <;> ring
  have hexact : x * y = (x.re : ℂ) * y + Complex.I * ((x.im : ℂ) * y) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have huerr := p04_roundedRealScale_error model x.re y
  have hverr : ‖v - Complex.I * ((x.im : ℂ) * y)‖ ≤
      model.epsilon * |x.im| * ‖y‖ := by
    simpa [v, ← mul_sub] using p04_roundedRealScale_error model x.im y
  have hunorm := p04_roundedRealScale_norm model x.re y
  have hvnorm : ‖v‖ ≤ (1 + model.epsilon) * |x.im| * ‖y‖ := by
    simpa [v] using p04_roundedRealScale_norm model x.im y
  have hadd := p04_roundedComplexAdd_error model u v
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hparts := p04_complex_abs_parts_le x
  rw [huv, hexact]
  have hdecomp : p04RoundedComplexAdd model u v -
      ((x.re : ℂ) * y + Complex.I * ((x.im : ℂ) * y)) =
      (p04RoundedComplexAdd model u v - (u + v)) +
      (u - (x.re : ℂ) * y) +
      (v - Complex.I * ((x.im : ℂ) * y)) := by abel
  rw [hdecomp]
  calc
    ‖(p04RoundedComplexAdd model u v - (u + v)) +
        (u - (x.re : ℂ) * y) + (v - Complex.I * ((x.im : ℂ) * y))‖
        ≤ ‖p04RoundedComplexAdd model u v - (u + v)‖ +
            ‖u - (x.re : ℂ) * y‖ +
            ‖v - Complex.I * ((x.im : ℂ) * y)‖ := by
              exact le_trans (norm_add_le _ _)
                (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
          model.epsilon * |x.re| * ‖y‖ +
          model.epsilon * |x.im| * ‖y‖ := by gcongr
    _ ≤ model.epsilon *
          ((1 + model.epsilon) * |x.re| * ‖y‖ +
            (1 + model.epsilon) * |x.im| * ‖y‖) +
          model.epsilon * |x.re| * ‖y‖ +
          model.epsilon * |x.im| * ‖y‖ := by gcongr
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (|x.re| + |x.im|) * ‖y‖ := by ring
    _ ≤ Real.sqrt 2 * (2 * model.epsilon + model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
          have hc : 0 ≤ 2 * model.epsilon + model.epsilon ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hparts (mul_nonneg hc (norm_nonneg y))]

private theorem p04_stdAddChar_eq_root {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.stdAddChar j =
      ⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ := by
  rw [p04StdAddChar_positive_exp]
  have hangle :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p04RootAngle j : ℂ) * Complex.I := by
    simp only [p04RootAngle]
    push_cast
    ring
  rw [hangle]
  apply Complex.ext
  · simpa using Complex.exp_ofReal_mul_I_re (p04RootAngle j)
  · simpa using Complex.exp_ofReal_mul_I_im (p04RootAngle j)

private theorem p04_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      Real.sqrt 2 * model.gamma * model.epsilon := by
  obtain ⟨tc, htc, hc⟩ := model.cos_model (p04RootAngle j)
  obtain ⟨ts, hts, hs⟩ := model.sin_model (p04RootAngle j)
  have htc2 : tc ^ 2 ≤ 1 := by
    have h := sq_le_sq.mpr (by simpa only [abs_one] using htc : |tc| ≤ |(1 : ℝ)|)
    simpa using h
  have hts2 : ts ^ 2 ≤ 1 := by
    have h := sq_le_sq.mpr (by simpa only [abs_one] using hts : |ts| ≤ |(1 : ℝ)|)
    simpa using h
  let u : ℂ := ⟨tc, ts⟩
  have hunorm : ‖u‖ ≤ Real.sqrt 2 := by
    have hsq : ‖u‖ ^ 2 ≤ (Real.sqrt (2 : ℝ)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [u, Complex.normSq_apply]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq
  have heq : p04RoundedRoot model j - ZMod.stdAddChar j =
      ((model.gamma * model.epsilon : ℝ) : ℂ) * u := by
    rw [p04_stdAddChar_eq_root]
    apply Complex.ext <;>
      simp [p04RoundedRoot, hc, hs, u, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im] <;> ring
  rw [heq, norm_mul]
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hγ, abs_of_nonneg hε]
  nlinarith [mul_le_mul_of_nonneg_left hunorm (mul_nonneg hγ hε)]

private noncomputable def p04_roundedFinSum (model : P04WilkinsonModel)
    (q : ℕ) (v : Fin q → ℂ) : ℂ :=
  ⟨recursiveSum model.flAdd q (fun i => (v i).re),
    recursiveSum model.flAdd q (fun i => (v i).im)⟩

private theorem p04_roundedFinSum_zero (model : P04WilkinsonModel)
    (v : Fin 0 → ℂ) : p04_roundedFinSum model 0 v = 0 := by
  apply Complex.ext <;> simp [p04_roundedFinSum, recursiveSum]

private theorem p04_roundedFinSum_succ (model : P04WilkinsonModel)
    (q : ℕ) (v : Fin (q + 1) → ℂ) :
    p04_roundedFinSum model (q + 1) v =
      if q = 0 then v (Fin.last q)
      else p04RoundedComplexAdd model
        (p04_roundedFinSum model q (fun i => v i.castSucc))
        (v (Fin.last q)) := by
  split_ifs with hq
  · subst q
    apply Complex.ext <;> simp [p04_roundedFinSum, recursiveSum]
  · apply Complex.ext <;>
      simp [p04_roundedFinSum, recursiveSum, hq, p04RoundedComplexAdd]

private theorem p04_roundedFinSum_error (model : P04WilkinsonModel) :
    ∀ (q : ℕ) (v : Fin q → ℂ),
      ‖p04_roundedFinSum model q v - ∑ i : Fin q, v i‖ ≤
        ((1 + model.epsilon) ^ q - 1) * ∑ i : Fin q, ‖v i‖ := by
  intro q
  induction q with
  | zero =>
      intro v
      simp [p04_roundedFinSum_zero]
  | succ q ih =>
      intro v
      let w : Fin q → ℂ := fun i => v i.castSucc
      let z : ℂ := v (Fin.last q)
      let A : ℂ := p04_roundedFinSum model q w
      let B : ℂ := ∑ i : Fin q, w i
      let S : ℝ := ∑ i : Fin q, ‖w i‖
      let P : ℝ := (1 + model.epsilon) ^ q
      have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hP : 1 ≤ P := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + model.epsilon)
      have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hAB : ‖A - B‖ ≤ (P - 1) * S := ih w
      have hB : ‖B‖ ≤ S := by
        simpa [B, S, w] using norm_sum_le (s := Finset.univ) (f := w)
      have hA : ‖A‖ ≤ P * S := by
        calc
          ‖A‖ = ‖(A - B) + B‖ := by rw [sub_add_cancel]
          _ ≤ ‖A - B‖ + ‖B‖ := norm_add_le _ _
          _ ≤ (P - 1) * S + S := add_le_add hAB hB
          _ = P * S := by ring
      rw [p04_roundedFinSum_succ]
      simp only [Fin.sum_univ_castSucc]
      by_cases hq : q = 0
      · subst q
        simpa using (mul_nonneg hε (norm_nonneg (v 0)))
      · simp only [hq, ↓reduceIte]
        change ‖p04RoundedComplexAdd model A z - (B + z)‖ ≤
          ((1 + model.epsilon) ^ (q + 1) - 1) * (S + ‖z‖)
        have hlocal := p04_roundedComplexAdd_error model A z
        have hdecomp : p04RoundedComplexAdd model A z - (B + z) =
            (p04RoundedComplexAdd model A z - (A + z)) + (A - B) := by abel
        rw [hdecomp]
        have hcoeff : model.epsilon ≤ (1 + model.epsilon) ^ (q + 1) - 1 := by
          rw [pow_succ]
          nlinarith [mul_nonneg (sub_nonneg.mpr hP)
            (by linarith : 0 ≤ 1 + model.epsilon)]
        calc
          ‖(p04RoundedComplexAdd model A z - (A + z)) + (A - B)‖
              ≤ ‖p04RoundedComplexAdd model A z - (A + z)‖ + ‖A - B‖ :=
                norm_add_le _ _
          _ ≤ model.epsilon * (‖A‖ + ‖z‖) + (P - 1) * S :=
            add_le_add hlocal hAB
          _ ≤ model.epsilon * (P * S + ‖z‖) + (P - 1) * S := by
            gcongr
          _ = ((1 + model.epsilon) ^ (q + 1) - 1) * S +
              model.epsilon * ‖z‖ := by rw [pow_succ]; ring
          _ ≤ ((1 + model.epsilon) ^ (q + 1) - 1) * (S + ‖z‖) := by
            rw [mul_add]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg z))

private def p04_powSecondCoeff : ℕ → ℝ
  | 0 => 0
  | q + 1 => 2 * p04_powSecondCoeff q + q

private theorem p04_powSecondCoeff_nonneg : ∀ q, 0 ≤ p04_powSecondCoeff q := by
  intro q
  induction q with
  | zero => simp [p04_powSecondCoeff]
  | succ q ih =>
      simp only [p04_powSecondCoeff]
      positivity

private theorem p04_one_add_pow_bound (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ q : ℕ,
      (1 + u) ^ q - 1 ≤ (q : ℝ) * u + p04_powSecondCoeff q * u ^ 2 := by
  intro q
  induction q with
  | zero => simp [p04_powSecondCoeff]
  | succ q ih =>
      let C := p04_powSecondCoeff q
      have hC : 0 ≤ C := p04_powSecondCoeff_nonneg q
      have hε3 : u ^ 3 ≤ u ^ 2 := by
        nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 + u)
      have hsmall := mul_le_mul_of_nonneg_left hε3 hC
      simp only [p04_powSecondCoeff, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      dsimp [C] at *
      nlinarith

private theorem p04_stdAddChar_norm_one {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  rw [p04StdAddChar_positive_exp]
  have hangle :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p04RootAngle j : ℂ) * Complex.I := by
    simp only [p04RootAngle]
    push_cast
    ring
  rw [hangle, Complex.norm_exp_ofReal_mul_I]

private theorem p04_roundedRoot_norm (model : P04WilkinsonModel)
    {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤
      1 + Real.sqrt 2 * model.gamma * model.epsilon := by
  calc
    ‖p04RoundedRoot model j‖ =
        ‖(p04RoundedRoot model j - ZMod.stdAddChar j) + ZMod.stdAddChar j‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ +
          ‖ZMod.stdAddChar j‖ := norm_add_le _ _
    _ ≤ Real.sqrt 2 * model.gamma * model.epsilon + 1 := by
      exact add_le_add (p04_roundedRoot_error model j) (le_of_eq (p04_stdAddChar_norm_one j))
    _ = 1 + Real.sqrt 2 * model.gamma * model.epsilon := by ring

private theorem p04_roundedRootMul_error (model : P04WilkinsonModel)
    {q : ℕ} [NeZero q] (j : ZMod q) (x : ℂ)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      (Real.sqrt 2 * (2 + model.gamma) * model.epsilon +
          (Real.sqrt 2 + 6 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  let r := p04RoundedRoot model j
  let c := ZMod.stdAddChar j
  let u := model.epsilon
  let g := model.gamma
  let s := Real.sqrt 2
  have hu : 0 ≤ u := le_of_lt model.epsilon_pos
  have hg : 0 ≤ g := model.gamma_nonneg
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr := p04_roundedRoot_error model j
  have hrnorm := p04_roundedRoot_norm model j
  have hm := p04_roundedComplexMul_error model r x
  have hcube : u ^ 3 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hε) (sq_nonneg u)]
  have hdecomp : p04RoundedComplexMul model r x - c * x =
      (p04RoundedComplexMul model r x - r * x) + (r - c) * x := by ring
  rw [hdecomp]
  calc
    ‖(p04RoundedComplexMul model r x - r * x) + (r - c) * x‖
        ≤ ‖p04RoundedComplexMul model r x - r * x‖ + ‖(r - c) * x‖ :=
          norm_add_le _ _
    _ ≤ s * (2 * u + u ^ 2) * ‖r‖ * ‖x‖ +
          (s * g * u) * ‖x‖ := by
      rw [norm_mul]
      exact add_le_add hm (mul_le_mul_of_nonneg_right hr (norm_nonneg x))
    _ ≤ s * (2 * u + u ^ 2) * (1 + s * g * u) * ‖x‖ +
          (s * g * u) * ‖x‖ := by
      gcongr
    _ ≤ (s * (2 + g) * u + (s + 6 * g) * u ^ 2) * ‖x‖ := by
      have hbound :
          s * (2 * u + u ^ 2) * (1 + s * g * u) + s * g * u ≤
            s * (2 + g) * u + (s + 6 * g) * u ^ 2 := by
        have hgap : 0 ≤ 2 * g * (u ^ 2 - u ^ 3) :=
          mul_nonneg (mul_nonneg (by norm_num) hg) (sub_nonneg.mpr hcube)
        have hs2a : s ^ 2 * g * u ^ 2 = 2 * g * u ^ 2 := by rw [hs2]
        have hs2b : s ^ 2 * g * u ^ 3 = 2 * g * u ^ 3 := by rw [hs2]
        nlinarith
      convert mul_le_mul_of_nonneg_right hbound (norm_nonneg x) using 1 <;> ring

private theorem p04_roundedComplexSum_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      ((1 + model.epsilon) ^ q - 1) * ∑ j : ZMod q, ‖term j‖ := by
  let e : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  have h := p04_roundedFinSum_error model q (fun i => term (e i))
  have hsum1 : (∑ i : Fin q, term (e i)) = ∑ j : ZMod q, term j := e.sum_comp term
  have hsum2 : (∑ i : Fin q, ‖term (e i)‖) =
      ∑ j : ZMod q, ‖term j‖ := e.sum_comp (fun j => ‖term j‖)
  change ‖p04_roundedFinSum model q (fun i => term (e i)) -
      ∑ j : ZMod q, term j‖ ≤
    ((1 + model.epsilon) ^ q - 1) * ∑ j : ZMod q, ‖term j‖
  rw [hsum1, hsum2] at h
  exact h

private theorem p04_errorProduct_bound
    (u p c a b : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : 0 ≤ p) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (P : ℝ) (hP : P ≤ 1 + p * u + c * u ^ 2) :
    P * (1 + a * u + b * u ^ 2) - 1 ≤
      (p + a) * u + (c + b + (p + c) * (a + b)) * u ^ 2 := by
  have hfactor : 0 ≤ 1 + a * u + b * u ^ 2 := by positivity
  have hu3 : u ^ 3 ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sq_nonneg u)]
  have hu4 : u ^ 4 ≤ u ^ 2 := by
    have hs : u ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg u)]
  have hmul := mul_le_mul_of_nonneg_right hP hfactor
  have h3 := mul_le_mul_of_nonneg_left hu3
    (add_nonneg (mul_nonneg hp hb) (mul_nonneg hc ha))
  have h4 := mul_le_mul_of_nonneg_left hu4 (mul_nonneg hc hb)
  nlinarith

private theorem p04_roundedComplexSum_perturbation {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term exact : ZMod q → ℂ)
    (weight : ZMod q → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hweight : ∀ j, 0 ≤ weight j)
    (hterm : ∀ j, ‖term j - exact j‖ ≤
      (a * model.epsilon + b * model.epsilon ^ 2) * weight j)
    (hexact : ∀ j, ‖exact j‖ ≤ weight j) :
    ‖p04RoundedComplexSum model term - ∑ j : ZMod q, exact j‖ ≤
      ((1 + model.epsilon) ^ q *
          (1 + a * model.epsilon + b * model.epsilon ^ 2) - 1) *
        ∑ j : ZMod q, weight j := by
  let u := model.epsilon
  let e := a * u + b * u ^ 2
  let P := (1 + u) ^ q
  let S := ∑ j : ZMod q, weight j
  have hu : 0 ≤ u := le_of_lt model.epsilon_pos
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hweight j)
  have hdiff :
      ∑ j : ZMod q, ‖term j - exact j‖ ≤ e * S := by
    calc
      _ ≤ ∑ j : ZMod q, e * weight j := by
        apply Finset.sum_le_sum
        intro j _
        exact hterm j
      _ = e * S := by simp [S, Finset.mul_sum]
  have hnorm : (∑ j : ZMod q, ‖term j‖) ≤ (1 + e) * S := by
    calc
      _ ≤ ∑ j : ZMod q, (‖term j - exact j‖ + ‖exact j‖) := by
        apply Finset.sum_le_sum
        intro j _
        simpa [sub_add_cancel] using
          (norm_add_le (term j - exact j) (exact j))
      _ ≤ ∑ j : ZMod q, (e * weight j + weight j) := by
        apply Finset.sum_le_sum
        intro j _
        exact add_le_add (hterm j) (hexact j)
      _ = (1 + e) * S := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
  have hsumerr := p04_roundedComplexSum_error model term
  have hsumdiff :
      ‖(∑ j : ZMod q, term j) - ∑ j : ZMod q, exact j‖ ≤
        ∑ j : ZMod q, ‖term j - exact j‖ := by
    rw [← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  have hdecomp : p04RoundedComplexSum model term - ∑ j : ZMod q, exact j =
      (p04RoundedComplexSum model term - ∑ j : ZMod q, term j) +
      ((∑ j : ZMod q, term j) - ∑ j : ZMod q, exact j) := by abel
  rw [hdecomp]
  calc
    ‖(p04RoundedComplexSum model term - ∑ j : ZMod q, term j) +
        ((∑ j : ZMod q, term j) - ∑ j : ZMod q, exact j)‖
        ≤ ‖p04RoundedComplexSum model term - ∑ j : ZMod q, term j‖ +
            ‖(∑ j : ZMod q, term j) - ∑ j : ZMod q, exact j‖ := norm_add_le _ _
    _ ≤ (P - 1) * (∑ j : ZMod q, ‖term j‖) +
          ∑ j : ZMod q, ‖term j - exact j‖ :=
      add_le_add hsumerr hsumdiff
    _ ≤ (P - 1) * ((1 + e) * S) + e * S := by
      have hP1 : 0 ≤ P - 1 :=
        sub_nonneg.mpr (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + u))
      exact add_le_add (mul_le_mul_of_nonneg_left hnorm hP1) hdiff
    _ = (P * (1 + e) - 1) * S := by ring
    _ = ((1 + model.epsilon) ^ q *
          (1 + a * model.epsilon + b * model.epsilon ^ 2) - 1) *
        ∑ j : ZMod q, weight j := by dsimp [P, e, S, u]; ring

private noncomputable def p04_genericSecondCoeff (q : ℕ) (γ : ℝ) : ℝ :=
  let s := Real.sqrt 2
  let A := s * (2 + γ)
  let D := s + 6 * γ
  let C := p04_powSecondCoeff q
  C + D + ((q : ℝ) + C) * (A + D)

private theorem p04_genericRadixBlock_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (hq : 3 ≤ q) (x : ZMod q → ℂ)
    (k : ZMod q) (hε : model.epsilon ≤ 1) :
    ‖p04RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * ((q : ℝ) + model.gamma) * model.epsilon +
        p04_genericSecondCoeff q model.gamma * model.epsilon ^ 2) *
        ∑ j : ZMod q, ‖x j‖ := by
  let u := model.epsilon
  let g := model.gamma
  let s := Real.sqrt 2
  let A := s * (2 + g)
  let D := s + 6 * g
  let C := p04_powSecondCoeff q
  let B := p04_genericSecondCoeff q g
  have hu : 0 ≤ u := le_of_lt model.epsilon_pos
  have hg : 0 ≤ g := model.gamma_nonneg
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs15 : s ≤ 3 / 2 := by nlinarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := p04_powSecondCoeff_nonneg q
  have hB : 0 ≤ B := by
    change 0 ≤ C + D + ((q : ℝ) + C) * (A + D)
    positivity
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hcoef : (q : ℝ) + A ≤ 2 * ((q : ℝ) + g) := by
    have hsg := mul_le_mul_of_nonneg_right hs15 hg
    dsimp [A]
    nlinarith
  let term : ZMod q → ℂ := fun j =>
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let exact : ZMod q → ℂ := fun j => ZMod.stdAddChar (j * k) * x j
  have hterm : ∀ j, ‖term j - exact j‖ ≤
      (A * u + D * u ^ 2) * ‖x j‖ := by
    intro j
    exact p04_roundedRootMul_error model (j * k) (x j) hε
  have hexact : ∀ j, ‖exact j‖ ≤ ‖x j‖ := by
    intro j
    simp [exact, norm_mul, p04_stdAddChar_norm_one]
  have hraw := p04_roundedComplexSum_perturbation model term exact
    (fun j => ‖x j‖) A D hA hD (fun j => norm_nonneg _) hterm hexact
  have hpow := p04_one_add_pow_bound u hu hε q
  have hprod :
      (1 + u) ^ q * (1 + A * u + D * u ^ 2) - 1 ≤
        ((q : ℝ) + A) * u + B * u ^ 2 := by
    exact p04_errorProduct_bound u q C A D hu hε
      (by positivity) hC hA hD ((1 + u) ^ q) (by nlinarith)
  have hsum : 0 ≤ ∑ j : ZMod q, ‖x j‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  change ‖p04RoundedComplexSum model term - ∑ j : ZMod q, exact j‖ ≤
    (2 * ((q : ℝ) + g) * u + B * u ^ 2) *
      ∑ j : ZMod q, ‖x j‖
  calc
    _ ≤ ((1 + u) ^ q * (1 + A * u + D * u ^ 2) - 1) *
        ∑ j : ZMod q, ‖x j‖ := hraw
    _ ≤ (((q : ℝ) + A) * u + B * u ^ 2) *
        ∑ j : ZMod q, ‖x j‖ :=
      mul_le_mul_of_nonneg_right hprod hsum
    _ ≤ (2 * ((q : ℝ) + g) * u + B * u ^ 2) *
        ∑ j : ZMod q, ‖x j‖ := by
      gcongr

private theorem p04_stdAddChar_zmod2 (j : ZMod 2) :
    ZMod.stdAddChar j = if j = 0 then 1 else -1 := by
  fin_cases j
  · change ZMod.stdAddChar (0 : ZMod 2) =
        if (0 : ZMod 2) = 0 then 1 else -1
    rw [p04_stdAddChar_eq_root]
    simp [p04RootAngle]
    apply Complex.ext <;> simp
  · have hangle : p04RootAngle (1 : ZMod 2) = Real.pi := by
      simp [p04RootAngle, ZMod.val_one'' (by norm_num : (2 : ℕ) ≠ 1)]
    change ZMod.stdAddChar (1 : ZMod 2) =
      if (1 : ZMod 2) = 0 then 1 else -1
    rw [p04_stdAddChar_eq_root, hangle]
    simp
    apply Complex.ext <;> simp

private theorem p04_roundedComplexSum_two (model : P04WilkinsonModel)
    (term : ZMod 2 → ℂ) :
    p04RoundedComplexSum model term =
      p04RoundedComplexAdd model (term 0) (term 1) := by
  apply Complex.ext <;>
    simp [p04RoundedComplexSum, p04RoundedComplexAdd, recursiveSum]

private theorem p04_sum_zmod_two (term : ZMod 2 → ℂ) :
    (∑ j : ZMod 2, term j) = term 0 + term 1 := by
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp term]
  simp

private theorem p04_radixTwo_coeff_exact (j : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  by_cases hj : j = 0
  · simp [p04RadixTwoCoefficientApply, hj, p04_stdAddChar_zmod2]
  · simp [p04RadixTwoCoefficientApply, hj, p04_stdAddChar_zmod2]

private theorem p04_radixTwo_coeff_norm (j : ZMod 2) (x : ℂ) :
    ‖p04RadixTwoCoefficientApply j x‖ = ‖x‖ := by
  rw [p04_radixTwo_coeff_exact, norm_mul, p04_stdAddChar_norm_one]
  ring

private theorem p04_radixTwoBlock_error (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  let term : ZMod 2 → ℂ := fun j => p04RadixTwoCoefficientApply (j * k) (x j)
  have hsum : (∑ j : ZMod 2, term j) =
      ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    exact p04_radixTwo_coeff_exact (j * k) (x j)
  have hnorm : (∑ j : ZMod 2, ‖term j‖) =
      ∑ j : ZMod 2, ‖x j‖ := by
    apply Finset.sum_congr rfl
    intro j _
    exact p04_radixTwo_coeff_norm (j * k) (x j)
  have hsumNorm : (∑ j : ZMod 2, ‖x j‖) = ‖x 0‖ + ‖x 1‖ := by
    rw [← (ZMod.finEquiv 2).toEquiv.sum_comp (fun j => ‖x j‖)]
    simp
  rw [← hsum, p04_sum_zmod_two term, p04RoundedRadixTwoBlock,
    p04_roundedComplexSum_two]
  simpa [term, hsumNorm, p04_radixTwo_coeff_norm] using
    p04_roundedComplexAdd_error model (term 0) (term 1)

private theorem p04_roundedAddTreeFour_error (model : P04WilkinsonModel)
    (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) - (a + b + c + d)‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hu := p04_roundedComplexAdd_error model a b
  have hv := p04_roundedComplexAdd_error model c d
  have htop := p04_roundedComplexAdd_error model u v
  have hunorm : ‖u‖ ≤ (1 + model.epsilon) * (‖a‖ + ‖b‖) := by
    calc
      ‖u‖ = ‖(u - (a + b)) + (a + b)‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - (a + b)‖ + ‖a + b‖ := norm_add_le _ _
      _ ≤ model.epsilon * (‖a‖ + ‖b‖) + (‖a‖ + ‖b‖) :=
        add_le_add hu (norm_add_le a b)
      _ = (1 + model.epsilon) * (‖a‖ + ‖b‖) := by ring
  have hvnorm : ‖v‖ ≤ (1 + model.epsilon) * (‖c‖ + ‖d‖) := by
    calc
      ‖v‖ = ‖(v - (c + d)) + (c + d)‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - (c + d)‖ + ‖c + d‖ := norm_add_le _ _
      _ ≤ model.epsilon * (‖c‖ + ‖d‖) + (‖c‖ + ‖d‖) :=
        add_le_add hv (norm_add_le c d)
      _ = (1 + model.epsilon) * (‖c‖ + ‖d‖) := by ring
  have hdecomp : p04RoundedComplexAdd model u v - (a + b + c + d) =
      (p04RoundedComplexAdd model u v - (u + v)) +
      (u - (a + b)) + (v - (c + d)) := by abel
  change ‖p04RoundedComplexAdd model u v - (a + b + c + d)‖ ≤ _
  rw [hdecomp]
  calc
    ‖(p04RoundedComplexAdd model u v - (u + v)) +
        (u - (a + b)) + (v - (c + d))‖
        ≤ ‖p04RoundedComplexAdd model u v - (u + v)‖ +
            ‖u - (a + b)‖ + ‖v - (c + d)‖ := by
              exact le_trans (norm_add_le _ _)
                (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by gcongr
    _ ≤ model.epsilon *
          ((1 + model.epsilon) * (‖a‖ + ‖b‖) +
            (1 + model.epsilon) * (‖c‖ + ‖d‖)) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by gcongr
    _ = (2 * model.epsilon + model.epsilon ^ 2) *
          (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by ring

private theorem p04_stdAddChar_zmod4_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [p04_stdAddChar_eq_root]
  have hangle : p04RootAngle (1 : ZMod 4) = Real.pi / 2 := by
    rw [p04RootAngle, ZMod.val_one'' (by norm_num : (4 : ℕ) ≠ 1)]
    norm_num
    ring
  rw [hangle]
  apply Complex.ext <;> simp

private theorem p04_stdAddChar_zmod4_two :
    ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  have h : (2 : ZMod 4) = 1 + 1 := by decide
  rw [h, AddChar.map_add_eq_mul, p04_stdAddChar_zmod4_one]
  norm_num

private theorem p04_stdAddChar_zmod4_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have h : (3 : ZMod 4) = 1 + 2 := by decide
  rw [h, AddChar.map_add_eq_mul, p04_stdAddChar_zmod4_one,
    p04_stdAddChar_zmod4_two]
  ring

private theorem p04_radixFour_coeff_exact (j : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change p04RadixFourCoefficientApply (0 : ZMod 4) x =
      ZMod.stdAddChar (0 : ZMod 4) * x
    simp [p04RadixFourCoefficientApply]
  · change p04RadixFourCoefficientApply (1 : ZMod 4) x =
      ZMod.stdAddChar (1 : ZMod 4) * x
    rw [p04_stdAddChar_zmod4_one]
    simp [p04RadixFourCoefficientApply, show (1 : ZMod 4) ≠ 0 by decide]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change p04RadixFourCoefficientApply (2 : ZMod 4) x =
      ZMod.stdAddChar (2 : ZMod 4) * x
    rw [p04_stdAddChar_zmod4_two]
    simp [p04RadixFourCoefficientApply, show (2 : ZMod 4) ≠ 0 by decide,
      show (2 : ZMod 4) ≠ 1 by decide]
  · change p04RadixFourCoefficientApply (3 : ZMod 4) x =
      ZMod.stdAddChar (3 : ZMod 4) * x
    rw [p04_stdAddChar_zmod4_three]
    simp [p04RadixFourCoefficientApply, show (3 : ZMod 4) ≠ 0 by decide,
      show (3 : ZMod 4) ≠ 1 by decide,
      show (3 : ZMod 4) ≠ 2 by decide]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p04_radixFour_coeff_norm (j : ZMod 4) (x : ℂ) :
    ‖p04RadixFourCoefficientApply j x‖ = ‖x‖ := by
  rw [p04_radixFour_coeff_exact, norm_mul, p04_stdAddChar_norm_one]
  ring

private theorem p04_sum_zmod_four (term : ZMod 4 → ℂ) :
    (∑ j : ZMod 4, term j) = term 0 + term 1 + term 2 + term 3 := by
  have h2 : (ZMod.finEquiv 4) (2 : Fin 4) = (2 : ZMod 4) := by decide
  have h3 : (ZMod.finEquiv 4) (3 : Fin 4) = (3 : ZMod 4) := by decide
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp term]
  simp [Fin.sum_univ_succ, h2, h3]
  ring

private theorem p04_sum_zmod_four_real (term : ZMod 4 → ℝ) :
    (∑ j : ZMod 4, term j) = term 0 + term 1 + term 2 + term 3 := by
  have h2 : (ZMod.finEquiv 4) (2 : Fin 4) = (2 : ZMod 4) := by decide
  have h3 : (ZMod.finEquiv 4) (3 : Fin 4) = (3 : ZMod 4) := by decide
  rw [← (ZMod.finEquiv 4).toEquiv.sum_comp term]
  simp [Fin.sum_univ_succ, h2, h3]
  ring

private theorem p04_radixFourBlock_error (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        ∑ j : ZMod 4, ‖x j‖ := by
  let e : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let t : Fin 4 → ℂ := fun i =>
    p04RadixFourCoefficientApply (e i * k) (x (e i))
  have hsum : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      t 0 + t 1 + t 2 + t 3 := by
    rw [← e.sum_comp (fun j => ZMod.stdAddChar (j * k) * x j)]
    simp [Fin.sum_univ_succ, t, p04_radixFour_coeff_exact]
    ring
  have hnorm : (∑ j : ZMod 4, ‖x j‖) =
      ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖ := by
    rw [← e.sum_comp (fun j => ‖x j‖)]
    simp [Fin.sum_univ_succ, t, p04_radixFour_coeff_norm]
    ring
  rw [hsum, hnorm]
  change ‖p04RoundedComplexAdd model
      (p04RoundedComplexAdd model (t 0) (t 1))
      (p04RoundedComplexAdd model (t 2) (t 3)) -
      (t 0 + t 1 + t 2 + t 3)‖ ≤
    (2 * model.epsilon + model.epsilon ^ 2) *
      (‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖)
  exact p04_roundedAddTreeFour_error model (t 0) (t 1) (t 2) (t 3)

private theorem p04_block_l2_bound {β : Type*} [Fintype β]
    {q : ℕ} [NeZero q] (x E : β × ZMod q → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ b : β, ∀ k : ZMod q,
      ‖E (b, k)‖ ≤ c * ∑ j : ZMod q, ‖x (b, j)‖) :
    Real.sqrt (∑ p : β × ZMod q, ‖E p‖ ^ 2) ≤
      (q : ℝ) * c * Real.sqrt (∑ p : β × ZMod q, ‖x p‖ ^ 2) := by
  classical
  let U : ℝ := ∑ p : β × ZMod q, ‖E p‖ ^ 2
  let V : ℝ := ∑ p : β × ZMod q, ‖x p‖ ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hUeq : U = ∑ b : β, ∑ k : ZMod q, ‖E (b, k)‖ ^ 2 := by
    simp [U, Fintype.sum_prod_type]
  have hVeq : V = ∑ b : β, ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
    simp [V, Fintype.sum_prod_type]
  have hUbound : U ≤ ((q : ℝ) * c) ^ 2 * V := by
    rw [hUeq, hVeq]
    have hinner : ∀ b : β,
        (∑ k : ZMod q, ‖E (b, k)‖ ^ 2) ≤
          ((q : ℝ) * c) ^ 2 * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
      intro b
      have hcs : (∑ j : ZMod q, ‖x (b, j)‖) ^ 2 ≤
          (q : ℝ) * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
        simpa using (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ) (f := fun j : ZMod q => ‖x (b, j)‖))
      have hsqpoint : ∀ k : ZMod q,
          ‖E (b, k)‖ ^ 2 ≤
            c ^ 2 * ((q : ℝ) * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2) := by
        intro k
        have hsum : 0 ≤ ∑ j : ZMod q, ‖x (b, j)‖ :=
          Finset.sum_nonneg (fun j _ => norm_nonneg _)
        have hsq := (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hc hsum)).mpr (hpoint b k)
        calc
          _ ≤ c ^ 2 * (∑ j : ZMod q, ‖x (b, j)‖) ^ 2 := by
            simpa [mul_pow] using hsq
          _ ≤ c ^ 2 * ((q : ℝ) * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
      calc
        _ ≤ ∑ k : ZMod q,
            c ^ 2 * ((q : ℝ) * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          exact hsqpoint k
        _ = ((q : ℝ) * c) ^ 2 * ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
          simp [mul_pow]
          ring
    calc
      _ ≤ ∑ b : β, ((q : ℝ) * c) ^ 2 *
            ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro b _
        exact hinner b
      _ = ((q : ℝ) * c) ^ 2 *
          ∑ b : β, ∑ j : ZMod q, ‖x (b, j)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hsq :
      (Real.sqrt U) ^ 2 ≤
        ((q : ℝ) * c * Real.sqrt V) ^ 2 := by
    rw [Real.sq_sqrt hU, mul_pow, Real.sq_sqrt hV]
    exact hUbound
  change Real.sqrt U ≤ (q : ℝ) * c * Real.sqrt V
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (mul_nonneg hq hc) (Real.sqrt_nonneg _))).mp hsq

private theorem p04_l2_pointwise_bound {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] (x E : ι → V) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i, ‖E i‖ ≤ c * ‖x i‖) :
    Real.sqrt (∑ i, ‖E i‖ ^ 2) ≤
      c * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  have hE : 0 ≤ ∑ i, ‖E i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hX : 0 ≤ ∑ i, ‖x i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq : (∑ i, ‖E i‖ ^ 2) ≤ c ^ 2 * ∑ i, ‖x i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mpr
      (hpoint i)
    simpa [mul_pow] using h
  have hsqrt :
      (Real.sqrt (∑ i, ‖E i‖ ^ 2)) ^ 2 ≤
        (c * Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hE, mul_pow, Real.sq_sqrt hX]
    exact hsq
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _))).mp hsqrt

private theorem p04_complexNorm2_sq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 x ^ 2 = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

private theorem p04_complexNorm2_sub_triangle {n : ℕ} [NeZero n]
    (x y z : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i => x i - z i) ≤
      p04ComplexNorm2 (fun i => x i - y i) +
      p04ComplexNorm2 (fun i => y i - z i) := by
  let X : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 y
  let Z : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 z
  have h : ‖X - Z‖ ≤ ‖X - Y‖ + ‖Y - Z‖ := by
    calc
      ‖X - Z‖ = ‖(X - Y) + (Y - Z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq,
    EuclideanSpace.norm_eq, X, Y, Z] using h

private noncomputable def p04_blockA (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 1 else if q = 4 then 2 else 2 * ((q : ℝ) + γ)

private noncomputable def p04_blockB (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 0 else if q = 4 then 1 else p04_genericSecondCoeff q γ

private theorem p04_blockA_nonneg (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_blockA q γ := by
  unfold p04_blockA
  split_ifs <;> positivity

private theorem p04_blockB_nonneg (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_blockB q γ := by
  unfold p04_blockB
  split_ifs
  · norm_num
  · norm_num
  · unfold p04_genericSecondCoeff
    have hC := p04_powSecondCoeff_nonneg q
    positivity

private theorem p04_mixedBlock_pointwise {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (i : ZMod n) (hε : model.epsilon ≤ 1) :
    ‖p04RoundedMixedRadixBlockApply model stage x i -
        p04MixedRadixBlockApply stage x i‖ ≤
      (p04_blockA stage.radix model.gamma * model.epsilon +
          p04_blockB stage.radix model.gamma * model.epsilon ^ 2) *
        ∑ j : ZMod stage.radix,
          ‖x (stage.permutation
            (stage.reindex ((stage.reindex.symm i).1, j)))‖ := by
  cases stage with
  | mk q qtwo qzero b bzero horder reindex permutation useTwiddle twiddleExponent =>
    letI : NeZero q := ⟨qzero⟩
    let bi := reindex.symm i
    by_cases h2 : q = 2
    · subst q
      simpa [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
        p04_blockA, p04_blockB, bi] using
        p04_radixTwoBlock_error model
          (fun j : ZMod 2 => x (permutation (reindex (bi.1, j)))) bi.2
    · by_cases h4 : q = 4
      · subst q
        simpa [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
          p04_blockA, p04_blockB, bi, h2] using
          p04_radixFourBlock_error model
            (fun j : ZMod 4 => x (permutation (reindex (bi.1, j)))) bi.2
      · have hq : 3 ≤ q := by omega
        simpa [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
          p04_blockA, p04_blockB, bi, h2, h4] using
          p04_genericRadixBlock_error model hq
            (fun j : ZMod q => x (permutation (reindex (bi.1, j)))) bi.2 hε

private theorem p04_mixedBlock_norm_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i) ≤
      (stage.radix : ℝ) *
        (p04_blockA stage.radix model.gamma * model.epsilon +
          p04_blockB stage.radix model.gamma * model.epsilon ^ 2) *
        p04ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let r := stage.reindex
  let X : Fin stage.blockCount × ZMod stage.radix → ℂ :=
    fun p => x (stage.permutation (r p))
  let E : Fin stage.blockCount × ZMod stage.radix → ℂ :=
    fun p => p04RoundedMixedRadixBlockApply model stage x (r p) -
      p04MixedRadixBlockApply stage x (r p)
  let c := p04_blockA stage.radix model.gamma * model.epsilon +
    p04_blockB stage.radix model.gamma * model.epsilon ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    have hγ := model.gamma_nonneg
    have hu := le_of_lt model.epsilon_pos
    have ha := p04_blockA_nonneg stage.radix model.gamma hγ
    have hb := p04_blockB_nonneg stage.radix model.gamma hγ
    positivity
  have hpoint : ∀ b : Fin stage.blockCount, ∀ k : ZMod stage.radix,
      ‖E (b, k)‖ ≤ c * ∑ j : ZMod stage.radix, ‖X (b, j)‖ := by
    intro b k
    have h := p04_mixedBlock_pointwise model stage x (r (b, k)) hε
    simpa [E, X, c, r] using h
  have h := p04_block_l2_bound X E c hc hpoint
  have hleft : (∑ p : Fin stage.blockCount × ZMod stage.radix, ‖E p‖ ^ 2) =
      ∑ i : ZMod n,
        ‖p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i‖ ^ 2 := by
    simpa [E, r] using (stage.reindex.sum_comp
      (fun i : ZMod n =>
        ‖p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i‖ ^ 2))
  have hright : (∑ p : Fin stage.blockCount × ZMod stage.radix, ‖X p‖ ^ 2) =
      ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    let e : Fin stage.blockCount × ZMod stage.radix ≃ ZMod n :=
      stage.reindex.trans stage.permutation
    simpa [X, r, e] using (e.sum_comp (fun i : ZMod n => ‖x i‖ ^ 2))
  rw [hleft, hright] at h
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq, c] using h

private theorem p04_exactTwiddle_norm {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) =
      p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, norm_mul, p04_stdAddChar_norm_one]
  · simp [p04MixedRadixTwiddleApply, h]

private theorem p04_exactTwiddle_sub_norm {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
      p04MixedRadixTwiddleApply stage x i -
        p04MixedRadixTwiddleApply stage y i) =
      p04ComplexNorm2 (fun i => x i - y i) := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, ← mul_sub,
      norm_mul, p04_stdAddChar_norm_one]
  · simp [p04MixedRadixTwiddleApply, h]

private theorem p04_complexNorm2_le_add_error {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p04ComplexNorm2 x ≤ p04ComplexNorm2 y +
      p04ComplexNorm2 (fun i => x i - y i) := by
  let X : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 y
  have h : ‖X‖ ≤ ‖Y‖ + ‖X - Y‖ := by
    calc
      ‖X‖ = ‖Y + (X - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq,
    EuclideanSpace.norm_eq, X, Y] using h

private theorem p04_roundedTwiddle_norm_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i =>
      p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) ≤
      (if stage.useTwiddle then
          Real.sqrt 2 * (2 + model.gamma) * model.epsilon +
            (Real.sqrt 2 + 6 * model.gamma) * model.epsilon ^ 2
        else 0) * p04ComplexNorm2 x := by
  by_cases h : stage.useTwiddle
  · let c := Real.sqrt 2 * (2 + model.gamma) * model.epsilon +
        (Real.sqrt 2 + 6 * model.gamma) * model.epsilon ^ 2
    have hc : 0 ≤ c := by
      dsimp [c]
      have hγ := model.gamma_nonneg
      have hu := le_of_lt model.epsilon_pos
      positivity
    have hpoint : ∀ i : ZMod n,
        ‖p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i‖ ≤ c * ‖x i‖ := by
      intro i
      simpa [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, h, c] using
        p04_roundedRootMul_error model (stage.twiddleExponent i) (x i) hε
    have hb := p04_l2_pointwise_bound x
      (fun i => p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) c hc hpoint
    simpa [p04ComplexNorm2, p04ComplexNorm2Sq, h, c] using hb
  · simp [p04RoundedMixedRadixTwiddleApply,
      p04MixedRadixTwiddleApply, h, p04ComplexNorm2, p04ComplexNorm2Sq]

private noncomputable def p04_stageBlockA (q : ℕ) (γ : ℝ) : ℝ :=
  Real.sqrt q * p04_blockA q γ

private noncomputable def p04_stageBlockB (q : ℕ) (γ : ℝ) : ℝ :=
  Real.sqrt q * p04_blockB q γ

private noncomputable def p04_stageTwiddleA {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then Real.sqrt 2 * (2 + γ) else 0

private noncomputable def p04_stageTwiddleB {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then Real.sqrt 2 + 6 * γ else 0

private noncomputable def p04_stageSecondCoeff {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  let a := p04_stageBlockA stage.radix γ
  let b := p04_stageBlockB stage.radix γ
  let c := p04_stageTwiddleA stage γ
  let d := p04_stageTwiddleB stage γ
  b + d + (a + b) * (c + d)

private theorem p04_stageBlockA_le_alpha (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    p04_stageBlockA q γ ≤ p04Alpha q γ := by
  unfold p04_stageBlockA p04_blockA p04Alpha
  by_cases h2 : q = 2
  · simp [h2]
  · by_cases h4 : q = 4
    · simp [h2, h4]
      norm_num
    · simp [h2, h4]
      exact le_of_eq (by ring)

private theorem p04_stageTwiddleA_le (n : ℕ) [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    p04_stageTwiddleA stage γ ≤
      if stage.useTwiddle then 3 + 2 * γ else 0 := by
  unfold p04_stageTwiddleA
  split_ifs with h
  · have hs : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
      have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have hsg := mul_le_mul_of_nonneg_right hs hγ
    nlinarith
  · exact le_rfl

private theorem p04_mixedStage_norm_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (hscale : ∀ z : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage z) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 z)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i =>
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
      Real.sqrt (stage.radix : ℝ) *
        ((p04Alpha stage.radix model.gamma +
            (if stage.useTwiddle then 3 + 2 * model.gamma else 0)) *
            model.epsilon +
          p04_stageSecondCoeff stage model.gamma * model.epsilon ^ 2) *
        p04ComplexNorm2 x := by
  let u := model.epsilon
  let g := model.gamma
  let r := Real.sqrt (stage.radix : ℝ)
  let rb := p04RoundedMixedRadixBlockApply model stage x
  let eb := p04MixedRadixBlockApply stage x
  let a := p04_stageBlockA stage.radix g
  let b := p04_stageBlockB stage.radix g
  let c := p04_stageTwiddleA stage g
  let d := p04_stageTwiddleB stage g
  let be := a * u + b * u ^ 2
  let te := c * u + d * u ^ 2
  let K := p04Alpha stage.radix g +
    (if stage.useTwiddle then 3 + 2 * g else 0)
  let C := p04_stageSecondCoeff stage g
  have hu : 0 ≤ u := le_of_lt model.epsilon_pos
  have hg : 0 ≤ g := model.gamma_nonneg
  have hq : 0 ≤ (stage.radix : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (stage.radix : ℝ) := Real.sq_sqrt hq
  have ha : 0 ≤ a := by
    dsimp [a, p04_stageBlockA]
    exact mul_nonneg hr (p04_blockA_nonneg stage.radix g hg)
  have hb : 0 ≤ b := by
    dsimp [b, p04_stageBlockB]
    exact mul_nonneg hr (p04_blockB_nonneg stage.radix g hg)
  have hc : 0 ≤ c := by
    dsimp [c, p04_stageTwiddleA]
    split_ifs <;> positivity
  have hd : 0 ≤ d := by
    dsimp [d, p04_stageTwiddleB]
    split_ifs <;> positivity
  have hbe : 0 ≤ be := by dsimp [be]; positivity
  have hte : 0 ≤ te := by dsimp [te]; positivity
  have hC : 0 ≤ C := by
    change 0 ≤ b + d + (a + b) * (c + d)
    positivity
  have hblock := p04_mixedBlock_norm_error model stage x hε
  have hblock' :
      p04ComplexNorm2 (fun i => rb i - eb i) ≤ r * be * p04ComplexNorm2 x := by
    have heq : (stage.radix : ℝ) *
        (p04_blockA stage.radix g * u +
          p04_blockB stage.radix g * u ^ 2) = r * be := by
      calc
        _ = r ^ 2 * (p04_blockA stage.radix g * u +
            p04_blockB stage.radix g * u ^ 2) := by rw [hr2]
        _ = r * be := by
          dsimp [be, a, b, p04_stageBlockA, p04_stageBlockB]
          ring
    simpa [rb, eb, u, g, heq] using hblock
  have heb : p04ComplexNorm2 eb = r * p04ComplexNorm2 x := by
    have h := hscale x
    simpa [p04MixedRadixStageApply, p04_exactTwiddle_norm,
      eb, r] using h
  have hrb : p04ComplexNorm2 rb ≤ (1 + be) * r * p04ComplexNorm2 x := by
    calc
      p04ComplexNorm2 rb ≤ p04ComplexNorm2 eb +
          p04ComplexNorm2 (fun i => rb i - eb i) :=
        p04_complexNorm2_le_add_error rb eb
      _ ≤ r * p04ComplexNorm2 x + r * be * p04ComplexNorm2 x := by
        exact add_le_add (le_of_eq heb) hblock'
      _ = (1 + be) * r * p04ComplexNorm2 x := by ring
  have htwiddle := p04_roundedTwiddle_norm_error model stage rb hε
  have htwiddle' :
      p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixTwiddleApply model stage rb i -
          p04MixedRadixTwiddleApply stage rb i) ≤ te * p04ComplexNorm2 rb := by
    by_cases h : stage.useTwiddle
    · simpa [te, c, d, u, g, p04_stageTwiddleA,
        p04_stageTwiddleB, h] using htwiddle
    · simpa [te, c, d, u, g, p04_stageTwiddleA,
        p04_stageTwiddleB, h] using htwiddle
  have hstage :
      p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixStageApply model stage x i -
          p04MixedRadixStageApply stage x i) ≤
        (te * (1 + be) + be) * r * p04ComplexNorm2 x := by
    have htri := p04_complexNorm2_sub_triangle
      (p04RoundedMixedRadixTwiddleApply model stage rb)
      (p04MixedRadixTwiddleApply stage rb)
      (p04MixedRadixTwiddleApply stage eb)
    have hiso := p04_exactTwiddle_sub_norm stage rb eb
    calc
      _ ≤ p04ComplexNorm2 (fun i =>
            p04RoundedMixedRadixTwiddleApply model stage rb i -
              p04MixedRadixTwiddleApply stage rb i) +
          p04ComplexNorm2 (fun i =>
            p04MixedRadixTwiddleApply stage rb i -
              p04MixedRadixTwiddleApply stage eb i) := by
        simpa [p04RoundedMixedRadixStageApply, p04MixedRadixStageApply,
          rb, eb] using htri
      _ ≤ te * p04ComplexNorm2 rb + r * be * p04ComplexNorm2 x := by
        rw [hiso]
        exact add_le_add htwiddle' hblock'
      _ ≤ te * ((1 + be) * r * p04ComplexNorm2 x) +
          r * be * p04ComplexNorm2 x := by
        exact add_le_add (mul_le_mul_of_nonneg_left hrb hte) le_rfl
      _ = (te * (1 + be) + be) * r * p04ComplexNorm2 x := by ring
  have hprod : (1 + be) * (1 + te) - 1 ≤ (a + c) * u + C * u ^ 2 := by
    have h := p04_errorProduct_bound u a b c d hu hε ha hb hc hd
      (1 + be) (by dsimp [be]; exact le_of_eq (by ring))
    convert h using 1 <;> dsimp [be, te, C, p04_stageSecondCoeff,
      a, b, c, d] <;> ring
  have hK : a + c ≤ K := by
    exact add_le_add
      (p04_stageBlockA_le_alpha stage.radix g hg)
      (p04_stageTwiddleA_le n stage g hg)
  have hcoef : te * (1 + be) + be ≤ K * u + C * u ^ 2 := by
    have heq : te * (1 + be) + be = (1 + be) * (1 + te) - 1 := by ring
    rw [heq]
    exact le_trans hprod (add_le_add
      (mul_le_mul_of_nonneg_right hK hu) le_rfl)
  change p04ComplexNorm2 (fun i =>
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
    r * (K * u + C * u ^ 2) * p04ComplexNorm2 x
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcoef hr)
    (by unfold p04ComplexNorm2; positivity : 0 ≤ p04ComplexNorm2 x)
  calc
    _ ≤ (te * (1 + be) + be) * r * p04ComplexNorm2 x := hstage
    _ = r * (te * (1 + be) + be) * p04ComplexNorm2 x := by ring
    _ ≤ r * (K * u + C * u ^ 2) * p04ComplexNorm2 x := hfinal

private theorem p04_mixedStage_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixStageApply stage (fun i => x i - y i) =
      fun i => p04MixedRadixStageApply stage x i -
        p04MixedRadixStageApply stage y i := by
  funext i
  unfold p04MixedRadixStageApply p04MixedRadixTwiddleApply
  by_cases h : stage.useTwiddle
  · simp only [h, ↓reduceIte, ← mul_sub]
    unfold p04MixedRadixBlockApply
    simp [mul_sub, Finset.sum_sub_distrib]
  · simp only [h, ↓reduceIte]
    unfold p04MixedRadixBlockApply
    simp [mul_sub, Finset.sum_sub_distrib]

private noncomputable def p04_stageK {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  p04Alpha stage.radix γ +
    if stage.useTwiddle then 3 + 2 * γ else 0

private noncomputable def p04_listK {n : ℕ} [NeZero n]
    (γ : ℝ) : List (P04MixedRadixStage n) → ℝ
  | [] => 0
  | stage :: rest => p04_stageK stage γ + p04_listK γ rest

private noncomputable def p04_listC {n : ℕ} [NeZero n]
    (γ : ℝ) : List (P04MixedRadixStage n) → ℝ
  | [] => 0
  | stage :: rest =>
      p04_stageSecondCoeff stage γ + p04_listC γ rest +
        (p04_stageK stage γ + p04_stageSecondCoeff stage γ) *
          (p04_listK γ rest + p04_listC γ rest)

private noncomputable def p04_listScale {n : ℕ} [NeZero n] :
    List (P04MixedRadixStage n) → ℝ
  | [] => 1
  | stage :: rest => Real.sqrt (stage.radix : ℝ) * p04_listScale rest

private noncomputable def p04_listExact {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun z stage => p04MixedRadixStageApply stage z) x

private noncomputable def p04_listRounded {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stages : List (P04MixedRadixStage n))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  stages.foldl (fun z stage => p04RoundedMixedRadixStageApply model stage z) x

private theorem p04_listScale_nonneg {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n)) : 0 ≤ p04_listScale stages := by
  induction stages with
  | nil => simp [p04_listScale]
  | cons stage rest ih =>
      simp only [p04_listScale]
      exact mul_nonneg (Real.sqrt_nonneg _) ih

private theorem p04_listExact_scale {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n))
    (hscale : ∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04_listExact stages x) =
      p04_listScale stages * p04ComplexNorm2 x := by
  induction stages generalizing x with
  | nil => simp [p04_listExact, p04_listScale]
  | cons stage rest ih =>
      have hs : ∀ z : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply stage z) =
            Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 z :=
        hscale stage (by simp)
      have ht : ∀ s ∈ rest, ∀ z : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply s z) =
            Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 z := by
        intro s hs z
        exact hscale s (by simp [hs]) z
      calc
        p04ComplexNorm2 (p04_listExact (stage :: rest) x) =
            p04ComplexNorm2 (p04_listExact rest
              (p04MixedRadixStageApply stage x)) := by rfl
        _ = p04_listScale rest *
              p04ComplexNorm2 (p04MixedRadixStageApply stage x) :=
          ih ht _
        _ = p04_listScale (stage :: rest) * p04ComplexNorm2 x := by
          rw [hs]
          simp only [p04_listScale]
          ring

private theorem p04_listExact_sub {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n)) (x y : ZMod n → ℂ) :
    p04_listExact stages (fun i => x i - y i) =
      fun i => p04_listExact stages x i - p04_listExact stages y i := by
  induction stages generalizing x y with
  | nil => rfl
  | cons stage rest ih =>
      change p04_listExact rest
          (p04MixedRadixStageApply stage (fun i => x i - y i)) =
        fun i => p04_listExact rest (p04MixedRadixStageApply stage x) i -
          p04_listExact rest (p04MixedRadixStageApply stage y) i
      rw [p04_mixedStage_sub]
      exact ih _ _

private theorem p04_stageK_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_stageK stage γ := by
  have hα : 0 ≤ p04Alpha stage.radix γ := by
    unfold p04Alpha
    split_ifs <;> positivity
  unfold p04_stageK
  split_ifs <;> positivity

private theorem p04_stageC_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_stageSecondCoeff stage γ := by
  let a := p04_stageBlockA stage.radix γ
  let b := p04_stageBlockB stage.radix γ
  let c := p04_stageTwiddleA stage γ
  let d := p04_stageTwiddleB stage γ
  have ha : 0 ≤ a :=
    mul_nonneg (Real.sqrt_nonneg _) (p04_blockA_nonneg _ _ hγ)
  have hb : 0 ≤ b :=
    mul_nonneg (Real.sqrt_nonneg _) (p04_blockB_nonneg _ _ hγ)
  have hc : 0 ≤ c := by
    dsimp [c, p04_stageTwiddleA]
    split_ifs <;> positivity
  have hd : 0 ≤ d := by
    dsimp [d, p04_stageTwiddleB]
    split_ifs <;> positivity
  change 0 ≤ b + d + (a + b) * (c + d)
  positivity

private theorem p04_listK_nonneg {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_listK γ stages := by
  induction stages with
  | nil => simp [p04_listK]
  | cons stage rest ih =>
      simp only [p04_listK]
      exact add_nonneg (p04_stageK_nonneg stage γ hγ) ih

private theorem p04_listC_nonneg {n : ℕ} [NeZero n]
    (stages : List (P04MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_listC γ stages := by
  induction stages with
  | nil => simp [p04_listC]
  | cons stage rest ih =>
      simp only [p04_listC]
      have hsK := p04_stageK_nonneg stage γ hγ
      have hsC := p04_stageC_nonneg stage γ hγ
      have htK := p04_listK_nonneg rest γ hγ
      positivity

private theorem p04_listRounded_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (hε : model.epsilon ≤ 1) :
    ∀ stages : List (P04MixedRadixStage n),
      (∀ stage ∈ stages, ∀ x : ZMod n → ℂ,
        p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
          Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x) →
      ∀ x : ZMod n → ℂ,
        p04ComplexNorm2 (fun i =>
          p04_listRounded model stages x i - p04_listExact stages x i) ≤
        (p04_listK model.gamma stages * model.epsilon +
          p04_listC model.gamma stages * model.epsilon ^ 2) *
          p04ComplexNorm2 (p04_listExact stages x) := by
  intro stages
  induction stages with
  | nil =>
      intro hscale x
      simp [p04_listRounded, p04_listExact, p04_listK,
        p04_listC, p04ComplexNorm2, p04ComplexNorm2Sq]
  | cons stage rest ih =>
      intro hscale x
      let rs := p04RoundedMixedRadixStageApply model stage x
      let es := p04MixedRadixStageApply stage x
      let u := model.epsilon
      let a := p04_stageK stage model.gamma
      let b := p04_stageSecondCoeff stage model.gamma
      let c := p04_listK model.gamma rest
      let d := p04_listC model.gamma rest
      let ds := a * u + b * u ^ 2
      let dt := c * u + d * u ^ 2
      let R := p04_listRounded model rest rs
      let Y := p04_listExact rest rs
      let T := p04_listExact rest es
      let scale := p04_listScale rest
      have hu : 0 ≤ u := le_of_lt model.epsilon_pos
      have ha : 0 ≤ a := p04_stageK_nonneg stage model.gamma model.gamma_nonneg
      have hb : 0 ≤ b := p04_stageC_nonneg stage model.gamma model.gamma_nonneg
      have hc : 0 ≤ c := p04_listK_nonneg rest model.gamma model.gamma_nonneg
      have hd : 0 ≤ d := p04_listC_nonneg rest model.gamma model.gamma_nonneg
      have hds : 0 ≤ ds := by dsimp [ds]; positivity
      have hdt : 0 ≤ dt := by dsimp [dt]; positivity
      have hscaleS : ∀ z : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply stage z) =
            Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 z :=
        hscale stage (by simp)
      have hscaleT : ∀ s ∈ rest, ∀ z : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply s z) =
            Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 z := by
        intro s hs z
        exact hscale s (by simp [hs]) z
      have htail := ih hscaleT rs
      have hstep := p04_mixedStage_norm_error model stage hscaleS x hε
      have hstep' : p04ComplexNorm2 (fun i => rs i - es i) ≤
          ds * p04ComplexNorm2 es := by
        rw [hscaleS]
        convert hstep using 1 <;>
          dsimp [rs, es, ds, a, b, u, p04_stageK] <;> ring
      have hrs : p04ComplexNorm2 rs ≤ (1 + ds) * p04ComplexNorm2 es := by
        calc
          p04ComplexNorm2 rs ≤ p04ComplexNorm2 es +
              p04ComplexNorm2 (fun i => rs i - es i) :=
            p04_complexNorm2_le_add_error rs es
          _ ≤ p04ComplexNorm2 es + ds * p04ComplexNorm2 es := by
            exact add_le_add le_rfl hstep'
          _ = (1 + ds) * p04ComplexNorm2 es := by ring
      have hY : p04ComplexNorm2 Y = scale * p04ComplexNorm2 rs :=
        p04_listExact_scale rest hscaleT rs
      have hT : p04ComplexNorm2 T = scale * p04ComplexNorm2 es :=
        p04_listExact_scale rest hscaleT es
      have hdiff : p04ComplexNorm2 (fun i => Y i - T i) =
          scale * p04ComplexNorm2 (fun i => rs i - es i) := by
        rw [← p04_listExact_sub]
        exact p04_listExact_scale rest hscaleT _
      have htri := p04_complexNorm2_sub_triangle R Y T
      have hmain : p04ComplexNorm2 (fun i => R i - T i) ≤
          (dt * (1 + ds) + ds) * p04ComplexNorm2 T := by
        calc
          p04ComplexNorm2 (fun i => R i - T i) ≤
              p04ComplexNorm2 (fun i => R i - Y i) +
              p04ComplexNorm2 (fun i => Y i - T i) := htri
          _ ≤ dt * p04ComplexNorm2 Y +
              scale * p04ComplexNorm2 (fun i => rs i - es i) := by
            exact add_le_add htail (le_of_eq hdiff)
          _ ≤ dt * (scale * p04ComplexNorm2 rs) +
              scale * (ds * p04ComplexNorm2 es) := by
            rw [hY]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left hstep' (p04_listScale_nonneg rest))
          _ ≤ dt * (scale * ((1 + ds) * p04ComplexNorm2 es)) +
              scale * (ds * p04ComplexNorm2 es) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hrs (p04_listScale_nonneg rest)) hdt)
              le_rfl
          _ = (dt * (1 + ds) + ds) * p04ComplexNorm2 T := by
            rw [hT]
            ring
      have hprod : (1 + ds) * (1 + dt) - 1 ≤
          (a + c) * u + p04_listC model.gamma (stage :: rest) * u ^ 2 := by
        have h := p04_errorProduct_bound u a b c d hu hε ha hb hc hd
          (1 + ds) (by dsimp [ds]; exact le_of_eq (by ring))
        convert h using 1 <;> dsimp [ds, dt, p04_listC, a, b, c, d] <;> ring
      have hcoef : dt * (1 + ds) + ds ≤
          p04_listK model.gamma (stage :: rest) * u +
            p04_listC model.gamma (stage :: rest) * u ^ 2 := by
        have heq : dt * (1 + ds) + ds = (1 + ds) * (1 + dt) - 1 := by ring
        rw [heq]
        simpa [p04_listK, a, c] using hprod
      have hTpos : 0 ≤ p04ComplexNorm2 T := by
        unfold p04ComplexNorm2
        positivity
      have hfinal := mul_le_mul_of_nonneg_right hcoef hTpos
      change p04ComplexNorm2 (fun i => R i - T i) ≤
        (p04_listK model.gamma (stage :: rest) * u +
          p04_listC model.gamma (stage :: rest) * u ^ 2) * p04ComplexNorm2 T
      exact le_trans hmain hfinal

private theorem p04_listK_ofFn {n : ℕ} [NeZero n] (γ : ℝ) :
    ∀ (m : ℕ) (f : Fin m → P04MixedRadixStage n),
      p04_listK γ (List.ofFn f) = ∑ i : Fin m, p04_stageK (f i) γ := by
  intro m
  induction m with
  | zero => intro f; simp [p04_listK]
  | succ m ih =>
      intro f
      rw [List.ofFn_succ, p04_listK, Fin.sum_univ_succ]
      rw [ih]

private theorem p04_twiddle_fin_sum (m : ℕ) (hm : 0 < m) (c : ℝ) :
    (∑ i : Fin m, if i.val + 1 < m then c else 0) =
      ((m : ℝ) - 1) * c := by
  cases m with
  | zero => omega
  | succ k =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have h : ∀ i : Fin k, i.val + 1 < k + 1 := by
        intro i
        omega
      simp [h]

private theorem p04_listK_plan {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    p04_listK γ (List.ofFn plan.stage) = p04K plan γ := by
  rw [p04_listK_ofFn]
  unfold p04K
  simp_rw [p04_stageK]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ i : Fin plan.stageCount,
        if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
      ∑ i : Fin plan.stageCount,
        if i.val + 1 < plan.stageCount then 3 + 2 * γ else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [plan.twiddle_pattern i]
          simp
    _ = ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) :=
      p04_twiddle_fin_sum plan.stageCount plan.stageCount_pos (3 + 2 * γ)

private theorem p04_perm_norm {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04Permute permutation x) = p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq p04Permute
  congr 1
  exact permutation.sum_comp (fun i : ZMod n => ‖x i‖ ^ 2)

private theorem p04_perm_sub_norm {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
      p04Permute permutation x i - p04Permute permutation y i) =
      p04ComplexNorm2 (fun i => x i - y i) := by
  have h : (fun i => p04Permute permutation x i -
      p04Permute permutation y i) =
      p04Permute permutation (fun i => x i - y i) := by rfl
  rw [h, p04_perm_norm]

private theorem p04_fft_norm_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i =>
      p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
      (p04K plan model.gamma * model.epsilon +
        p04_listC model.gamma (List.ofFn plan.stage) * model.epsilon ^ 2) *
          p04ComplexNorm2 (p04FourierTransform x) := by
  have hscale : ∀ stage ∈ List.ofFn plan.stage, ∀ z : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage z) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 z := by
    intro stage hs z
    obtain ⟨i, rfl⟩ := (List.mem_ofFn).mp hs
    exact plan.stage_norm_scaling i z
  have h := p04_listRounded_error model hε (List.ofFn plan.stage) hscale x
  have hperm := p04_perm_sub_norm plan.finalPermutation
    (p04_listRounded model (List.ofFn plan.stage) x)
    (p04_listExact (List.ofFn plan.stage) x)
  have hexact := plan.exact_factorization x
  rw [← hexact]
  change p04ComplexNorm2 (fun i =>
      p04Permute plan.finalPermutation
        (p04_listRounded model (List.ofFn plan.stage) x) i -
      p04Permute plan.finalPermutation
        (p04_listExact (List.ofFn plan.stage) x) i) ≤
      (p04K plan model.gamma * model.epsilon +
        p04_listC model.gamma (List.ofFn plan.stage) * model.epsilon ^ 2) *
        p04ComplexNorm2 (p04Permute plan.finalPermutation
          (p04_listExact (List.ofFn plan.stage) x))
  rw [hperm, p04_perm_norm]
  simpa [p04_listK_plan plan model.gamma] using h

private noncomputable def p04_fiberEquiv {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    {base : P04MultiIndex axis // base i = 0} × ZMod (axis i).order ≃
      P04MultiIndex axis where
  toFun p := Function.update p.1.1 i p.2
  invFun index := (⟨Function.update index i 0, by simp⟩, index i)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases h : j = i
      · subst j
        simp [p.1.2]
      · simp [h]
    · simp
  right_inv index := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]

private theorem p04_multiNorm2_eq_sqrt {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x = Real.sqrt (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
  unfold p04MultiNorm2
  simp [EuclideanSpace.norm_eq]

private theorem p04_multiNorm2_sub_triangle {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y z : P04MultiArray axis) :
    p04MultiNorm2 (fun i => x i - z i) ≤
      p04MultiNorm2 (fun i => x i - y i) +
      p04MultiNorm2 (fun i => y i - z i) := by
  let X : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 y
  let Z : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 z
  have h : ‖X - Z‖ ≤ ‖X - Y‖ + ‖Y - Z‖ := by
    calc
      ‖X - Z‖ = ‖(X - Y) + (Y - Z)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa [p04MultiNorm2, X, Y, Z] using h

private theorem p04_multiNorm2_le_add_error {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 x ≤ p04MultiNorm2 y +
      p04MultiNorm2 (fun i => x i - y i) := by
  let X : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 y
  have h : ‖X‖ ≤ ‖Y‖ + ‖X - Y‖ := by
    calc
      ‖X‖ = ‖Y + (X - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa [p04MultiNorm2, X, Y] using h

private theorem p04_multiFiber_bound {m : ℕ}
    {axis : Fin m → P04FftAxis} (i : Fin m)
    (x y : P04MultiArray axis) (c : ℝ) (hc : 0 ≤ c)
    (hfiber : ∀ base : {b : P04MultiIndex axis // b i = 0},
      p04ComplexNorm2 (fun k : ZMod (axis i).order =>
        x (p04_fiberEquiv axis i (base, k))) ≤
        c * p04ComplexNorm2 (fun k : ZMod (axis i).order =>
          y (p04_fiberEquiv axis i (base, k)))) :
    p04MultiNorm2 x ≤ c * p04MultiNorm2 y := by
  let e := p04_fiberEquiv axis i
  let X (base : {b : P04MultiIndex axis // b i = 0}) :=
    p04ComplexNorm2 (fun k : ZMod (axis i).order => x (e (base, k)))
  let Y (base : {b : P04MultiIndex axis // b i = 0}) :=
    p04ComplexNorm2 (fun k : ZMod (axis i).order => y (e (base, k)))
  have hX : (∑ base, X base ^ 2) =
      ∑ index : P04MultiIndex axis, ‖x index‖ ^ 2 := by
    simp_rw [X, p04_complexNorm2_sq]
    simpa only [Fintype.sum_prod_type] using
      (e.sum_comp (fun index => ‖x index‖ ^ 2))
  have hY : (∑ base, Y base ^ 2) =
      ∑ index : P04MultiIndex axis, ‖y index‖ ^ 2 := by
    simp_rw [Y, p04_complexNorm2_sq]
    simpa only [Fintype.sum_prod_type] using
      (e.sum_comp (fun index => ‖y index‖ ^ 2))
  have hsumX : 0 ≤ ∑ base, X base ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsumY : 0 ≤ ∑ base, Y base ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : (∑ base, X base ^ 2) ≤ c ^ 2 * ∑ base, Y base ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro base _
    have hnonneg (z : ZMod (axis i).order → ℂ) :
        0 ≤ p04ComplexNorm2 z := by
      unfold p04ComplexNorm2
      exact Real.sqrt_nonneg _
    have h := (sq_le_sq₀ (hnonneg _)
      (mul_nonneg hc (hnonneg _))).mpr (hfiber base)
    simpa [X, Y, mul_pow] using h
  rw [p04_multiNorm2_eq_sqrt, p04_multiNorm2_eq_sqrt, ← hX, ← hY]
  have hs : (Real.sqrt (∑ base, X base ^ 2)) ^ 2 ≤
      (c * Real.sqrt (∑ base, Y base ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hsumX, mul_pow, Real.sq_sqrt hsumY]
    exact hsq
  exact (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hc (Real.sqrt_nonneg _))).mp hs

private theorem p04_coordinate_fiber_exact {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis)
    (base : {b : P04MultiIndex axis // b i = 0})
    (k : ZMod (axis i).order) :
    p04CoordinateTransform axis i x (p04_fiberEquiv axis i (base, k)) =
      p04FourierTransform
        (fun j => x (p04_fiberEquiv axis i (base, j))) k := by
  simp [p04CoordinateTransform, p04FourierTransform, p04_fiberEquiv,
    Function.update_idem]

private theorem p04_coordinate_fiber_rounded {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis)
    (base : {b : P04MultiIndex axis // b i = 0})
    (k : ZMod (axis i).order) :
    p04RoundedCoordinateTransform axis i model x
        (p04_fiberEquiv axis i (base, k)) =
      p04RoundedFftApply (axis i).plan model
        (fun j => x (p04_fiberEquiv axis i (base, j))) k := by
  simp [p04RoundedCoordinateTransform, p04_fiberEquiv,
    Function.update_idem]

private theorem p04_axis_fourier_norm_scale
    (axis : P04FftAxis) (x : ZMod axis.order → ℂ) :
    p04ComplexNorm2 (p04FourierTransform x) =
      Real.sqrt (axis.order : ℝ) * p04ComplexNorm2 x := by
  have hs : Real.sqrt (axis.order : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast axis.order_pos))
  have h := axis.plan.fourier_rms_scaling x
  change p04ComplexNorm2 (p04FourierTransform x) /
      Real.sqrt (axis.order : ℝ) =
    Real.sqrt (axis.order : ℝ) *
      (p04ComplexNorm2 x / Real.sqrt (axis.order : ℝ)) at h
  field_simp [hs] at h
  nlinarith

private theorem p04_coordinate_norm_scale {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04MultiNorm2 (p04CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p04MultiNorm2 x := by
  let s := Real.sqrt ((axis i).order : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (axis i).order_pos)
  have hfiber (base : {b : P04MultiIndex axis // b i = 0}) :
      p04ComplexNorm2 (fun k : ZMod (axis i).order =>
        p04CoordinateTransform axis i x (p04_fiberEquiv axis i (base, k))) =
      s * p04ComplexNorm2 (fun k : ZMod (axis i).order =>
        x (p04_fiberEquiv axis i (base, k))) := by
    simp_rw [p04_coordinate_fiber_exact]
    exact p04_axis_fourier_norm_scale (axis i) _
  have hforward := p04_multiFiber_bound i
    (p04CoordinateTransform axis i x) x s hs.le (fun base => le_of_eq (hfiber base))
  have hback := p04_multiFiber_bound i x
    (p04CoordinateTransform axis i x) (s⁻¹) (inv_nonneg.mpr hs.le)
    (fun base => by rw [hfiber base]; field_simp [ne_of_gt hs]; exact le_refl _)
  have hnorm : 0 ≤ p04MultiNorm2 x := by
    unfold p04MultiNorm2
    exact norm_nonneg _
  have hnorm' : 0 ≤ p04MultiNorm2 (p04CoordinateTransform axis i x) := by
    unfold p04MultiNorm2
    exact norm_nonneg _
  change p04MultiNorm2 (p04CoordinateTransform axis i x) = s * p04MultiNorm2 x
  have hprod := mul_le_mul_of_nonneg_left hback hs.le
  field_simp [ne_of_gt hs] at hprod
  exact le_antisymm hforward hprod

private theorem p04_coordinate_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) :
    p04CoordinateTransform axis i (fun index => x index - y index) =
      (fun index => p04CoordinateTransform axis i x index -
        p04CoordinateTransform axis i y index) := by
  funext index
  simp [p04CoordinateTransform, mul_sub, Finset.sum_sub_distrib]

private theorem p04_coordinate_local_bound {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis)
    (hε : model.epsilon ≤ 1) :
    p04MultiNorm2 (fun index =>
      p04RoundedCoordinateTransform axis i model x index -
      p04CoordinateTransform axis i x index) ≤
      (p04AxisK (axis i) model.gamma * model.epsilon +
        p04_listC model.gamma (List.ofFn (axis i).plan.stage) *
          model.epsilon ^ 2) *
        p04MultiNorm2 (p04CoordinateTransform axis i x) := by
  have hc : 0 ≤ p04AxisK (axis i) model.gamma * model.epsilon +
      p04_listC model.gamma (List.ofFn (axis i).plan.stage) *
        model.epsilon ^ 2 := by
    have hk : 0 ≤ p04AxisK (axis i) model.gamma := by
      simpa [p04AxisK, p04_listK_plan] using
        (p04_listK_nonneg (List.ofFn (axis i).plan.stage)
          model.gamma model.gamma_nonneg)
    have hC := p04_listC_nonneg (List.ofFn (axis i).plan.stage)
      model.gamma model.gamma_nonneg
    have hε0 := model.epsilon_pos.le
    positivity
  apply p04_multiFiber_bound i _ _ _ hc
  intro base
  simpa only [p04_coordinate_fiber_exact, p04_coordinate_fiber_rounded,
    p04AxisK] using
    (p04_fft_norm_error (axis i).plan model
      (fun j => x (p04_fiberEquiv axis i (base, j))) hε)

private theorem p04_coordinateNat_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ)
    (x y : P04MultiArray axis) :
    p04CoordinateTransformNat axis k (fun index => x index - y index) =
      (fun index => p04CoordinateTransformNat axis k x index -
        p04CoordinateTransformNat axis k y index) := by
  unfold p04CoordinateTransformNat
  split_ifs with hk
  · exact p04_coordinate_sub axis ⟨k, hk⟩ x y
  · rfl

private theorem p04_prefix_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ)
    (x y : P04MultiArray axis) :
    p04ApplyCoordinatePrefix axis k (fun index => x index - y index) =
      (fun index => p04ApplyCoordinatePrefix axis k x index -
        p04ApplyCoordinatePrefix axis k y index) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      change p04ApplyCoordinatePrefix axis k
          (p04CoordinateTransformNat axis k (fun index => x index - y index)) =
        (fun index =>
          p04ApplyCoordinatePrefix axis k (p04CoordinateTransformNat axis k x) index -
          p04ApplyCoordinatePrefix axis k (p04CoordinateTransformNat axis k y) index)
      rw [p04_coordinateNat_sub]
      exact ih _ _

private theorem p04_multiCard_sqrt_pos {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    0 < Real.sqrt (p04MultiCardinality axis : ℝ) := by
  apply Real.sqrt_pos.2
  change 0 < ((∏ i : Fin m, (axis i).order : ℕ) : ℝ)
  exact_mod_cast (Finset.prod_pos (fun i _ => (axis i).order_pos) :
    0 < ∏ i : Fin m, (axis i).order)

private theorem p04_prefix_norm_scale {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (k : ℕ) (hk : k ≤ m)
    (x : P04MultiArray plan.axis) :
    p04MultiNorm2 (p04ApplyCoordinatePrefix plan.axis k x) =
      Real.sqrt (p04PrefixOrderProduct plan.axis k hk : ℝ) * p04MultiNorm2 x := by
  have hs := p04_multiCard_sqrt_pos plan.axis
  have h := plan.prefix_rms_scaling k hk x
  change p04MultiNorm2 (p04ApplyCoordinatePrefix plan.axis k x) /
      Real.sqrt (p04MultiCardinality plan.axis : ℝ) =
    Real.sqrt (p04PrefixOrderProduct plan.axis k hk : ℝ) *
      (p04MultiNorm2 x / Real.sqrt (p04MultiCardinality plan.axis : ℝ)) at h
  field_simp [ne_of_gt hs] at h
  nlinarith

private noncomputable def p04_runPartialOutput {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) (k : Fin (m + 1)) :
    P04MultiArray plan.axis :=
  p04ApplyCoordinatePrefix plan.axis k.val (run.computedState k)

private theorem p04_run_step_relative {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model)
    (hε : model.epsilon ≤ 1) (i : Fin m) :
    p04MultiNorm2 (fun index =>
      p04_runPartialOutput run i.castSucc index -
      p04_runPartialOutput run i.succ index) ≤
      (p04AxisK (plan.axis i) model.gamma * model.epsilon +
        p04_listC model.gamma (List.ofFn (plan.axis i).plan.stage) *
          model.epsilon ^ 2) *
        p04MultiNorm2 (p04_runPartialOutput run i.succ) := by
  let x := run.computedState i.succ
  let r := p04RoundedCoordinateTransform plan.axis i model x
  let e := p04CoordinateTransform plan.axis i x
  have hfirst : p04_runPartialOutput run i.castSucc =
      p04ApplyCoordinatePrefix plan.axis i.val r := by
    unfold p04_runPartialOutput
    simpa [r, x] using congrArg
      (p04ApplyCoordinatePrefix plan.axis i.val) (run.stage_step i)
  have hnext : p04_runPartialOutput run i.succ =
      p04ApplyCoordinatePrefix plan.axis i.val e := by
    change p04ApplyCoordinatePrefix plan.axis (i.val + 1) x =
      p04ApplyCoordinatePrefix plan.axis i.val e
    simp [p04ApplyCoordinatePrefix, p04CoordinateTransformNat, e, x, i.isLt]
  rw [hfirst, hnext, ← p04_prefix_sub]
  rw [p04_prefix_norm_scale plan i.val i.isLt.le,
    p04_prefix_norm_scale plan i.val i.isLt.le]
  simpa only [r, e, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left
      (p04_coordinate_local_bound plan.axis i model x hε)
      (Real.sqrt_nonneg _))

private def p04_chainA (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, a i

private def p04_chainC (a b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => p04_chainC a b n + b n +
      (p04_chainA a n + p04_chainC a b n) * (a n + b n)

private theorem p04_chain_bound {m : ℕ} {axis : Fin m → P04FftAxis}
    (x : ℕ → P04MultiArray axis) (a b : ℕ → ℝ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ha : ∀ i < m, 0 ≤ a i) (hb : ∀ i < m, 0 ≤ b i)
    (hstep : ∀ i < m,
      p04MultiNorm2 (fun index => x i index - x (i + 1) index) ≤
        (a i * u + b i * u ^ 2) * p04MultiNorm2 (x (i + 1))) :
    p04MultiNorm2 (fun index => x 0 index - x m index) ≤
      (p04_chainA a m * u + p04_chainC a b m * u ^ 2) *
        p04MultiNorm2 (x m) := by
  have hmain : ∀ n ≤ m,
      0 ≤ p04_chainA a n ∧ 0 ≤ p04_chainC a b n ∧
      p04MultiNorm2 (fun index => x 0 index - x n index) ≤
        (p04_chainA a n * u + p04_chainC a b n * u ^ 2) *
          p04MultiNorm2 (x n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [p04_chainA, p04_chainC, p04MultiNorm2] <;>
          (funext index; rfl)
    | succ n ih =>
        intro hn
        have hnlt : n < m := by omega
        obtain ⟨hA, hC, hprev⟩ := ih (by omega)
        have han := ha n hnlt
        have hbn := hb n hnlt
        have hAn : p04_chainA a (n + 1) = p04_chainA a n + a n := by
          simp [p04_chainA, Finset.sum_range_succ]
        have hCn : p04_chainC a b (n + 1) =
            p04_chainC a b n + b n +
              (p04_chainA a n + p04_chainC a b n) * (a n + b n) := rfl
        have hAnew : 0 ≤ p04_chainA a (n + 1) := by rw [hAn]; positivity
        have hCnew : 0 ≤ p04_chainC a b (n + 1) := by rw [hCn]; positivity
        refine ⟨hAnew, hCnew, ?_⟩
        let p := p04_chainA a n * u + p04_chainC a b n * u ^ 2
        let d := a n * u + b n * u ^ 2
        have hp : 0 ≤ p := by dsimp [p]; positivity
        have hd : 0 ≤ d := by dsimp [d]; positivity
        have hnorm : p04MultiNorm2 (x n) ≤
            (1 + d) * p04MultiNorm2 (x (n + 1)) := by
          have h := p04_multiNorm2_le_add_error (x n) (x (n + 1))
          have hs := hstep n hnlt
          dsimp [d]
          nlinarith
        have hscaled := mul_le_mul_of_nonneg_left hnorm hp
        have htri := p04_multiNorm2_sub_triangle (x 0) (x n) (x (n + 1))
        have hs := hstep n hnlt
        have hcoeff : p * (1 + d) + d ≤
            p04_chainA a (n + 1) * u +
              p04_chainC a b (n + 1) * u ^ 2 := by
          have h := p04_errorProduct_bound u
            (p04_chainA a n) (p04_chainC a b n) (a n) (b n)
            hu0 hu1 hA hC han hbn
            (1 + p) (by dsimp [p]; nlinarith)
          rw [hAn, hCn]
          dsimp [p, d] at *
          nlinarith
        have hnorm0 : 0 ≤ p04MultiNorm2 (x (n + 1)) := by
          unfold p04MultiNorm2
          exact norm_nonneg _
        have hscaledCoeff := mul_le_mul_of_nonneg_right hcoeff hnorm0
        dsimp [p, d] at *
        nlinarith
  exact (hmain m le_rfl).2.2

private theorem p04_chainC_nonneg (a b : ℕ → ℝ) (m : ℕ)
    (ha : ∀ i < m, 0 ≤ a i) (hb : ∀ i < m, 0 ≤ b i) :
    0 ≤ p04_chainC a b m := by
  have haux : ∀ n ≤ m,
      0 ≤ p04_chainA a n ∧ 0 ≤ p04_chainC a b n := by
    intro n
    induction n with
    | zero => intro _; simp [p04_chainA, p04_chainC]
    | succ n ih =>
        intro hn
        obtain ⟨hA, hC⟩ := ih (by omega)
        have hnlt : n < m := by omega
        have hAn : p04_chainA a (n + 1) = p04_chainA a n + a n := by
          simp [p04_chainA, Finset.sum_range_succ]
        constructor
        · rw [hAn]; exact add_nonneg hA (ha n hnlt)
        · simp only [p04_chainC]
          have han := ha n hnlt
          have hbn := hb n hnlt
          positivity
  exact (haux m le_rfl).2

theorem p04_c1_multidimensional_rms_error_bound
    {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (hexactOutput : 0 < p04MultiRms (p04FamilyMultiExactOutput family)) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ ε : P04PositiveEpsilon, ε.1 ≤ radius →
          p04MultiRms (p04FamilyMultiFftRoundoffError family ε) /
              p04MultiRms (p04FamilyMultiExactOutput family) ≤
            ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
              secondOrderCoeff * ε.1 ^ 2 := by
  -- PROOF_START P04-C1-H001
  let a (k : ℕ) : ℝ :=
    if hk : k < m then p04AxisK (plan.axis ⟨k, hk⟩) γ else 0
  let b (k : ℕ) : ℝ :=
    if hk : k < m then
      p04_listC γ (List.ofFn (plan.axis ⟨k, hk⟩).plan.stage) else 0
  have ha : ∀ i < m, 0 ≤ a i := by
    intro i hi
    simp only [a, dif_pos hi]
    simpa [p04AxisK, p04_listK_plan] using
      (p04_listK_nonneg (List.ofFn (plan.axis ⟨i, hi⟩).plan.stage)
        γ family.gamma_nonneg)
  have hb : ∀ i < m, 0 ≤ b i := by
    intro i hi
    simp only [b, dif_pos hi]
    exact p04_listC_nonneg _ γ family.gamma_nonneg
  have hA : p04_chainA a m = ∑ i : Fin m, p04AxisK (plan.axis i) γ := by
    calc
      p04_chainA a m = ∑ i ∈ Finset.range m, a i := rfl
      _ = ∑ i : Fin m, a i.val :=
        (Fin.sum_univ_eq_sum_range a m).symm
      _ = ∑ i : Fin m, p04AxisK (plan.axis i) γ := by
        apply Finset.sum_congr rfl
        intro i _
        simp [a, i.isLt]
  refine ⟨p04_chainC a b m, p04_chainC_nonneg a b m ha hb,
    1, by norm_num, ?_⟩
  intro ε hε
  let run := family.run ε
  let states (k : ℕ) : P04MultiArray plan.axis :=
    if hk : k ≤ m then
      p04_runPartialOutput run ⟨k, Nat.lt_succ_of_le hk⟩
    else 0
  have hstates (k : ℕ) (hk : k ≤ m) :
      states k = p04_runPartialOutput run ⟨k, Nat.lt_succ_of_le hk⟩ := by
    exact dif_pos hk
  have hmodelε : (family.model ε).epsilon = ε.1 := family.model_epsilon ε
  have hmodelγ : (family.model ε).gamma = γ := family.model_gamma ε
  have hstep : ∀ i < m,
      p04MultiNorm2 (fun index => states i index - states (i + 1) index) ≤
        (a i * ε.1 + b i * ε.1 ^ 2) * p04MultiNorm2 (states (i + 1)) := by
    intro i hi
    rw [hstates i (by omega), hstates (i + 1) (by omega)]
    have h := p04_run_step_relative run (by simpa [hmodelε] using hε) ⟨i, hi⟩
    simpa [a, b, hi, hmodelε, hmodelγ] using h
  have hnorm := p04_chain_bound states a b ε.1 ε.2.le hε ha hb hstep
  rw [hA] at hnorm
  have hstart : states 0 = p04MultiComputedOutput run := by
    rw [hstates 0 (by omega)]
    rfl
  have hend : states m = p04FamilyMultiExactOutput family := by
    rw [hstates m le_rfl]
    change p04ApplyCoordinatePrefix plan.axis m
      (run.computedState (Fin.last m)) =
      p04ApplyCoordinatePrefix plan.axis m family.input
    rw [run.computed_input, family.run_input]
  rw [hstart, hend] at hnorm
  have hnorm' :
      p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) ≤
        ((∑ i : Fin m, p04AxisK (plan.axis i) γ) * ε.1 +
          p04_chainC a b m * ε.1 ^ 2) *
          p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
    simpa [p04FamilyMultiFftRoundoffError, p04MultiComputedOutput,
      p04FamilyMultiExactOutput, run] using hnorm
  have hs := p04_multiCard_sqrt_pos plan.axis
  have hrms :
      p04MultiRms (p04FamilyMultiFftRoundoffError family ε) ≤
        ((∑ i : Fin m, p04AxisK (plan.axis i) γ) * ε.1 +
          p04_chainC a b m * ε.1 ^ 2) *
          p04MultiRms (p04FamilyMultiExactOutput family) := by
    unfold p04MultiRms
    simpa only [mul_div_assoc] using
      ((div_le_div_iff_of_pos_right hs).2 hnorm')
  have hquot := (div_le_iff₀ hexactOutput).2 hrms
  simpa [mul_comm] using hquot

end VSCLReuse

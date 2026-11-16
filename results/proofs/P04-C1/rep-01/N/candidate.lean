import VSCLReuse.P04.Definitions

namespace VSCLReuse



private theorem p04_coord_scale_norm_le (z : ℂ) (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(⟨a * z.re, b * z.im⟩ : ℂ)‖ ≤ ‖z‖ := by
  have ha2 : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 1 + |a| by positivity), sq_abs a]
  have hb2 : b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 1 + |b| by positivity), sq_abs b]
  have hre : (a * z.re) ^ 2 ≤ z.re ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2) (sq_nonneg z.re)]
  have him : (b * z.im) ^ 2 ≤ z.im ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb2) (sq_nonneg z.im)]
  have hsq : ‖(⟨a * z.re, b * z.im⟩ : ℂ)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply]
    nlinarith
  nlinarith [norm_nonneg (⟨a * z.re, b * z.im⟩ : ℂ), norm_nonneg z]

private theorem p04_rounded_complex_add_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  obtain ⟨ar, br, har, hbr, hre⟩ := model.add_model x.re y.re
  obtain ⟨ai, bi, hai, hbi, him⟩ := model.add_model x.im y.im
  let ex : ℂ := ⟨ar * x.re, ai * x.im⟩
  let ey : ℂ := ⟨br * y.re, bi * y.im⟩
  have heq : p04RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * (ex + ey) := by
    apply Complex.ext <;> simp [p04RoundedComplexAdd, ex, ey, hre, him] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  have hx := p04_coord_scale_norm_le x ar ai har hai
  have hy := p04_coord_scale_norm_le y br bi hbr hbi
  calc
    model.epsilon * ‖ex + ey‖ ≤
        model.epsilon * (‖ex‖ + ‖ey‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le ex ey) model.epsilon_pos.le
    _ ≤ model.epsilon * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hx hy) model.epsilon_pos.le

private theorem p04_complex_norm2_eq {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  simp [p04ComplexNorm2, p04ComplexNorm2Sq, EuclideanSpace.norm_eq]

private theorem p04_multi_norm2_eq {m : ℕ} {axis : Fin m → P04FftAxis}
    (x : P04MultiArray axis) :
    p04MultiNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))‖ := rfl

private theorem p04_stdAddChar_eq_trig {n : ℕ} [NeZero n]
    (j : ZMod n) :
    ZMod.stdAddChar j =
      ⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ := by
  rw [p04StdAddChar_positive_exp]
  have harg : (2 * Real.pi * Complex.I * (j.val : ℂ) / (n : ℂ)) =
      (p04RootAngle j : ℂ) * Complex.I := by
    simp only [p04RootAngle]
    push_cast
    ring
  rw [harg]
  apply Complex.ext
  · exact Complex.exp_ofReal_mul_I_re _
  · exact Complex.exp_ofReal_mul_I_im _

private theorem p04_complex_norm_mk_le (a b : ℝ) :
    ‖(⟨a, b⟩ : ℂ)‖ ≤ |a| + |b| := by
  have h : (⟨a, b⟩ : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h]
  calc
    ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ ‖(a : ℂ)‖ + ‖(b : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = |a| + |b| := by simp [Complex.norm_real, Real.norm_eq_abs]

private theorem p04_rounded_root_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  obtain ⟨tc, htc, hc⟩ := model.cos_model (p04RootAngle j)
  obtain ⟨ts, hts, hs⟩ := model.sin_model (p04RootAngle j)
  have heq : p04RoundedRoot model j - ZMod.stdAddChar j =
      (model.gamma * model.epsilon : ℂ) * (⟨tc, ts⟩ : ℂ) := by
    rw [p04_stdAddChar_eq_trig]
    apply Complex.ext <;> simp [p04RoundedRoot, hc, hs] <;> ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg model.gamma_nonneg,
    abs_of_pos model.epsilon_pos]
  have hnorm : ‖(⟨tc, ts⟩ : ℂ)‖ ≤ 2 := by
    calc
      ‖(⟨tc, ts⟩ : ℂ)‖ ≤ |tc| + |ts| := p04_complex_norm_mk_le tc ts
      _ ≤ 2 := by linarith
  nlinarith [mul_nonneg (mul_nonneg model.gamma_nonneg model.epsilon_pos.le)
    (sub_nonneg.mpr hnorm)]

private theorem p04_rounded_real_mul_pair_error (model : P04WilkinsonModel)
    (a : ℝ) (y : ℂ) :
    ‖(⟨model.flMul a y.re - a * y.re,
        model.flMul a y.im - a * y.im⟩ : ℂ)‖ ≤
      model.epsilon * |a| * ‖y‖ := by
  obtain ⟨tr, htr, hr⟩ := model.mul_model a y.re
  obtain ⟨ti, hti, hi⟩ := model.mul_model a y.im
  have heq : (⟨model.flMul a y.re - a * y.re,
        model.flMul a y.im - a * y.im⟩ : ℂ) =
      (model.epsilon : ℂ) * (a : ℂ) * (⟨tr * y.re, ti * y.im⟩ : ℂ) := by
    apply Complex.ext <;> simp [hr, hi] <;> ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos model.epsilon_pos]
  have h := p04_coord_scale_norm_le y tr ti htr hti
  nlinarith [mul_nonneg (mul_nonneg model.epsilon_pos.le (abs_nonneg a))
    (sub_nonneg.mpr h)]

private theorem p04_abs_re_add_abs_im_le (x : ℂ) :
    |x.re| + |x.im| ≤ Real.sqrt 2 * ‖x‖ := by
  have hsq : (|x.re| + |x.im|) ^ 2 ≤
      (Real.sqrt 2 * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg (|x.re| - |x.im|), sq_abs x.re, sq_abs x.im]
  have hnonneg : 0 ≤ Real.sqrt 2 * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [abs_nonneg x.re, abs_nonneg x.im]

private theorem p04_rounded_complex_mul_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (|x.re| + |x.im|) * ‖y‖ := by
  let uR : ℂ := ⟨model.flMul x.re y.re, model.flMul x.re y.im⟩
  let vR : ℂ := ⟨-model.flMul x.im y.im, model.flMul x.im y.re⟩
  let u : ℂ := ⟨x.re * y.re, x.re * y.im⟩
  let v : ℂ := ⟨-x.im * y.im, x.im * y.re⟩
  have hround : p04RoundedComplexMul model x y =
      p04RoundedComplexAdd model uR vR := rfl
  have hexact : x * y = u + v := by
    apply Complex.ext <;> simp [u, v, Complex.mul_re, Complex.mul_im] <;> ring
  have hu : ‖u‖ = |x.re| * ‖y‖ := by
    have heq : u = (x.re : ℂ) * y := by
      apply Complex.ext <;> simp [u, Complex.mul_re, Complex.mul_im]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hv : ‖v‖ = |x.im| * ‖y‖ := by
    have heq : v = (x.im : ℂ) * Complex.I * y := by
      apply Complex.ext <;> simp [v, Complex.mul_re, Complex.mul_im] <;> ring
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp
  have huerr : ‖uR - u‖ ≤ model.epsilon * |x.re| * ‖y‖ :=
    p04_rounded_real_mul_pair_error model x.re y
  have hverr : ‖vR - v‖ ≤ model.epsilon * |x.im| * ‖y‖ := by
    have heq : vR - v = Complex.I *
        (⟨model.flMul x.im y.re - x.im * y.re,
          model.flMul x.im y.im - x.im * y.im⟩ : ℂ) := by
      apply Complex.ext <;>
        simp [vR, v, Complex.mul_re, Complex.mul_im] <;> ring
    rw [heq, norm_mul]
    simpa using p04_rounded_real_mul_pair_error model x.im y
  have huR : ‖uR‖ ≤ (1 + model.epsilon) * |x.re| * ‖y‖ := by
    have h := norm_add_le (uR - u) u
    have heq : uR - u + u = uR := by abel
    rw [heq, hu] at h
    nlinarith
  have hvR : ‖vR‖ ≤ (1 + model.epsilon) * |x.im| * ‖y‖ := by
    have h := norm_add_le (vR - v) v
    have heq : vR - v + v = vR := by abel
    rw [heq, hv] at h
    nlinarith
  have h1 := p04_rounded_complex_add_error model uR vR
  have htri : ‖p04RoundedComplexMul model x y - x * y‖ ≤
      ‖p04RoundedComplexAdd model uR vR - (uR + vR)‖ +
        ‖uR - u‖ + ‖vR - v‖ := by
    rw [hround, hexact]
    have heq : p04RoundedComplexAdd model uR vR - (u + v) =
        (p04RoundedComplexAdd model uR vR - (uR + vR)) +
          ((uR - u) + (vR - v)) := by abel
    rw [heq]
    have hfirst := norm_add_le
      (p04RoundedComplexAdd model uR vR - (uR + vR))
      ((uR - u) + (vR - v))
    have hsecond := norm_add_le (uR - u) (vR - v)
    linarith
  have hnonneg : 0 ≤ model.epsilon := model.epsilon_pos.le
  have hsum : ‖uR‖ + ‖vR‖ ≤
      (1 + model.epsilon) * (|x.re| + |x.im|) * ‖y‖ := by
    nlinarith
  have hE : ‖uR - u‖ + ‖vR - v‖ ≤
      model.epsilon * (|x.re| + |x.im|) * ‖y‖ := by
    nlinarith
  calc
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
        model.epsilon * (‖uR‖ + ‖vR‖) +
          (‖uR - u‖ + ‖vR - v‖) := by linarith
    _ ≤ model.epsilon *
          ((1 + model.epsilon) * (|x.re| + |x.im|) * ‖y‖) +
          model.epsilon * (|x.re| + |x.im|) * ‖y‖ := by
            gcongr
    _ = model.epsilon * (2 + model.epsilon) *
          (|x.re| + |x.im|) * ‖y‖ := by ring

private theorem p04_rounded_complex_mul_error_sharp (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (3 + 2 * model.epsilon) * ‖x‖ * ‖y‖ := by
  have hroot : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg (2 : ℝ)]
  have hfactor : 0 ≤ model.epsilon * (2 + model.epsilon) :=
    mul_nonneg model.epsilon_pos.le (by linarith [model.epsilon_pos])
  have hcoef : (2 + model.epsilon) * Real.sqrt 2 ≤
      3 + 2 * model.epsilon := by
    nlinarith [mul_nonneg (show 0 ≤ 2 + model.epsilon by linarith [model.epsilon_pos])
      (sub_nonneg.mpr hroot), model.epsilon_pos.le]
  calc
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
        model.epsilon * (2 + model.epsilon) *
          (|x.re| + |x.im|) * ‖y‖ :=
      p04_rounded_complex_mul_error model x y
    _ ≤ model.epsilon * (2 + model.epsilon) *
          (Real.sqrt 2 * ‖x‖) * ‖y‖ := by
      gcongr
      exact p04_abs_re_add_abs_im_le x
    _ ≤ model.epsilon * (3 + 2 * model.epsilon) * ‖x‖ * ‖y‖ := by
      have h := mul_le_mul_of_nonneg_left hcoef model.epsilon_pos.le
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg (norm_nonneg x) (norm_nonneg y))
      nlinarith

private theorem p04_stdAddChar_norm_eq_one {q : ℕ} [NeZero q]
    (j : ZMod q) : ‖ZMod.stdAddChar j‖ = 1 := by
  rw [p04_stdAddChar_eq_trig]
  have hsq : ‖(⟨Real.cos (p04RootAngle j),
      Real.sin (p04RootAngle j)⟩ : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [pow_two, add_comm] using Real.sin_sq_add_cos_sq (p04RootAngle j)
  nlinarith [norm_nonneg (⟨Real.cos (p04RootAngle j),
    Real.sin (p04RootAngle j)⟩ : ℂ)]

private theorem p04_rounded_root_norm_le {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  have h := norm_add_le
    (p04RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
  have heq : p04RoundedRoot model j - ZMod.stdAddChar j +
      ZMod.stdAddChar j = p04RoundedRoot model j := by abel
  rw [heq, p04_stdAddChar_norm_eq_one] at h
  linarith [p04_rounded_root_error model j]

private theorem p04_rounded_root_mul_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      model.epsilon * (3 + 2 * model.gamma +
        (2 + 10 * model.gamma) * model.epsilon) * ‖x‖ := by
  have h1 := p04_rounded_complex_mul_error_sharp model
    (p04RoundedRoot model j) x
  have h2 := p04_rounded_root_error model j
  have h3 := p04_rounded_root_norm_le model j
  have htri : ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        p04RoundedRoot model j * x‖ +
        ‖(p04RoundedRoot model j - ZMod.stdAddChar j) * x‖ := by
    have heq : p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x =
        (p04RoundedComplexMul model (p04RoundedRoot model j) x -
          p04RoundedRoot model j * x) +
          (p04RoundedRoot model j - ZMod.stdAddChar j) * x := by ring
    rw [heq]
    exact norm_add_le _ _
  rw [norm_mul] at htri
  have hcoeff : 0 ≤ model.epsilon * (3 + 2 * model.epsilon) := by
    apply mul_nonneg model.epsilon_pos.le
    linarith [model.epsilon_pos]
  have hmul := mul_le_mul_of_nonneg_right h3 hcoeff
  have hmul2 := mul_le_mul_of_nonneg_right hmul (norm_nonneg x)
  have hmul' := mul_le_mul_of_nonneg_right h2 (norm_nonneg x)
  have hmono : model.epsilon * (3 + 2 * model.epsilon) *
      (1 + 2 * model.gamma * model.epsilon) +
      2 * model.gamma * model.epsilon ≤
      model.epsilon * (3 + 2 * model.gamma +
        (2 + 10 * model.gamma) * model.epsilon) := by
    have he : 0 ≤ model.epsilon := model.epsilon_pos.le
    have hg : 0 ≤ model.gamma := model.gamma_nonneg
    have hε2 := mul_nonneg (mul_nonneg hg he) (sub_nonneg.mpr hε)
    nlinarith
  have hmono' := mul_le_mul_of_nonneg_right hmono (norm_nonneg x)
  nlinarith [h1, hmul2, hmul']

private noncomputable def p04RecursiveComplexSum (model : P04WilkinsonModel)
    (n : ℕ) (v : Fin n → ℂ) : ℂ :=
  ⟨recursiveSum model.flAdd n (fun i ↦ (v i).re),
    recursiveSum model.flAdd n (fun i ↦ (v i).im)⟩

private theorem p04RecursiveComplexSum_zero (model : P04WilkinsonModel)
    (v : Fin 0 → ℂ) : p04RecursiveComplexSum model 0 v = 0 := by
  apply Complex.ext <;> simp [p04RecursiveComplexSum, recursiveSum]

private theorem p04RecursiveComplexSum_one (model : P04WilkinsonModel)
    (v : Fin 1 → ℂ) : p04RecursiveComplexSum model 1 v = v 0 := by
  apply Complex.ext <;> simp [p04RecursiveComplexSum, recursiveSum]

private theorem p04RecursiveComplexSum_succ (model : P04WilkinsonModel)
    (n : ℕ) (hn : 0 < n) (v : Fin (n + 1) → ℂ) :
    p04RecursiveComplexSum model (n + 1) v =
      p04RoundedComplexAdd model
        (p04RecursiveComplexSum model n (fun i ↦ v i.castSucc))
        (v (Fin.last n)) := by
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  apply Complex.ext <;> simp [p04RecursiveComplexSum, recursiveSum, hne,
    p04RoundedComplexAdd]

private theorem p04RoundedComplexSum_eq_recursive {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    p04RoundedComplexSum model term =
      p04RecursiveComplexSum model q
        (fun i ↦ term ((ZMod.finEquiv q).toEquiv i)) := rfl

private theorem p04_recursive_complex_sum_error (model : P04WilkinsonModel)
    (n : ℕ) (v : Fin (n + 1) → ℂ) :
    ‖p04RecursiveComplexSum model (n + 1) v - ∑ i, v i‖ ≤
      ((1 + model.epsilon) ^ n - 1) * (∑ i, ‖v i‖) := by
  induction n with
  | zero =>
      simp [p04RecursiveComplexSum_one]
  | succ n ih =>
      let w : Fin (n + 1) → ℂ := fun i ↦ v i.castSucc
      let z : ℂ := v (Fin.last (n + 1))
      have hrec : p04RecursiveComplexSum model (n + 2) v =
          p04RoundedComplexAdd model (p04RecursiveComplexSum model (n + 1) w) z := by
        simpa [w, z] using p04RecursiveComplexSum_succ model (n + 1)
          (Nat.zero_lt_succ n) v
      have hsum : (∑ i : Fin (n + 2), v i) =
          (∑ i : Fin (n + 1), w i) + z := by
        simpa [w, z] using (Fin.sum_univ_castSucc v)
      have hnormsum : ‖∑ i : Fin (n + 1), w i‖ ≤
          ∑ i : Fin (n + 1), ‖w i‖ := norm_sum_le _ _
      have hnormprev : ‖p04RecursiveComplexSum model (n + 1) w‖ ≤
          ‖p04RecursiveComplexSum model (n + 1) w -
            ∑ i : Fin (n + 1), w i‖ +
              ∑ i : Fin (n + 1), ‖w i‖ := by
        have h := norm_add_le
          (p04RecursiveComplexSum model (n + 1) w - ∑ i, w i)
          (∑ i, w i)
        have heq : p04RecursiveComplexSum model (n + 1) w - ∑ i, w i +
            ∑ i, w i = p04RecursiveComplexSum model (n + 1) w := by abel
        rw [heq] at h
        linarith
      have hlocal := p04_rounded_complex_add_error model
        (p04RecursiveComplexSum model (n + 1) w) z
      have htri : ‖p04RecursiveComplexSum model (n + 2) v -
          ∑ i : Fin (n + 2), v i‖ ≤
          ‖p04RoundedComplexAdd model
              (p04RecursiveComplexSum model (n + 1) w) z -
              (p04RecursiveComplexSum model (n + 1) w + z)‖ +
            ‖p04RecursiveComplexSum model (n + 1) w -
              ∑ i : Fin (n + 1), w i‖ := by
        rw [hrec, hsum]
        have heq : p04RoundedComplexAdd model
            (p04RecursiveComplexSum model (n + 1) w) z -
            ((∑ i, w i) + z) =
            (p04RoundedComplexAdd model
              (p04RecursiveComplexSum model (n + 1) w) z -
              (p04RecursiveComplexSum model (n + 1) w + z)) +
              (p04RecursiveComplexSum model (n + 1) w -
                ∑ i, w i) := by abel
        rw [heq]
        exact norm_add_le _ _
      have hc : 0 ≤ (1 + model.epsilon) ^ n - 1 := by
        have hbase : 1 ≤ 1 + model.epsilon := by linarith [model.epsilon_pos]
        have hp : (1 : ℝ) ^ n ≤ (1 + model.epsilon) ^ n :=
          pow_le_pow_left₀ (by norm_num) hbase _
        simpa using sub_nonneg.mpr hp
      have hprev := ih w
      have hS : 0 ≤ ∑ i : Fin (n + 1), ‖w i‖ :=
        Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
      have hA : ‖p04RoundedComplexAdd model
          (p04RecursiveComplexSum model (n + 1) w) z -
          (p04RecursiveComplexSum model (n + 1) w + z)‖ ≤
          model.epsilon *
            (((1 + model.epsilon) ^ n - 1) *
              (∑ i : Fin (n + 1), ‖w i‖) +
              (∑ i : Fin (n + 1), ‖w i‖) + ‖z‖) := by
        have hm := mul_le_mul_of_nonneg_left
          (add_le_add_right hnormprev ‖z‖) model.epsilon_pos.le
        have hprev_mul := mul_le_mul_of_nonneg_left hprev model.epsilon_pos.le
        nlinarith [hlocal, hm, hprev_mul]
      have hstep : ‖p04RecursiveComplexSum model (n + 2) v -
          ∑ i : Fin (n + 2), v i‖ ≤
          ((1 + model.epsilon) ^ (n + 1) - 1) *
            ((∑ i : Fin (n + 1), ‖w i‖) + ‖z‖) := by
        have hp : (1 + model.epsilon) ^ (n + 1) - 1 =
            ((1 + model.epsilon) ^ n - 1) * (1 + model.epsilon) +
              model.epsilon := by ring
        have hcoeff : model.epsilon ≤ (1 + model.epsilon) ^ (n + 1) - 1 := by
          rw [hp]
          have he : 0 ≤ 1 + model.epsilon := by linarith [model.epsilon_pos]
          nlinarith [mul_nonneg hc he]
        have hmul := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg z)
        rw [hp] at hmul ⊢
        calc
          ‖p04RecursiveComplexSum model (n + 2) v -
              ∑ i : Fin (n + 2), v i‖ ≤
              model.epsilon *
                (((1 + model.epsilon) ^ n - 1) *
                  (∑ i : Fin (n + 1), ‖w i‖) +
                  (∑ i : Fin (n + 1), ‖w i‖) + ‖z‖) +
                ((1 + model.epsilon) ^ n - 1) *
                  (∑ i : Fin (n + 1), ‖w i‖) := by linarith
          _ = (((1 + model.epsilon) ^ n - 1) *
                (1 + model.epsilon) + model.epsilon) *
                (∑ i : Fin (n + 1), ‖w i‖) +
                model.epsilon * ‖z‖ := by ring
          _ ≤ (((1 + model.epsilon) ^ n - 1) *
                (1 + model.epsilon) + model.epsilon) *
                ((∑ i : Fin (n + 1), ‖w i‖) + ‖z‖) := by
              nlinarith [hmul]
      simpa [Fin.sum_univ_castSucc, w, z] using hstep

private theorem p04_pow_one_add_first_order (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        (1 + ε) ^ n - 1 ≤ (n : ℝ) * ε + C * ε ^ 2 := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro ε hε hε1
      simp
  | succ n ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨(n : ℝ) + 2 * C, by positivity, ?_⟩
      intro ε hε hε1
      have h := hbound ε hε hε1
      have hm := mul_le_mul_of_nonneg_right h (by linarith : 0 ≤ 1 + ε)
      have hcube : C * ε ^ 3 ≤ C * ε ^ 2 := by
        have hpow : ε ^ 3 ≤ ε ^ 2 := by
          nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε1)]
        exact mul_le_mul_of_nonneg_left hpow hC
      calc
        (1 + ε) ^ (n + 1) - 1 =
            ((1 + ε) ^ n - 1) * (1 + ε) + ε := by ring
        _ ≤ ((n : ℝ) * ε + C * ε ^ 2) * (1 + ε) + ε := by
            linarith [hm]
        _ ≤ ((n + 1 : ℕ) : ℝ) * ε +
              ((n : ℝ) + 2 * C) * ε ^ 2 := by
            push_cast
            nlinarith [hcube]

private theorem p04_rounded_complex_sum_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j, term j‖ ≤
      ((1 + model.epsilon) ^ (q - 1) - 1) * (∑ j, ‖term j‖) := by
  cases q with
  | zero => exact (NeZero.ne (0 : ℕ)) rfl |>.elim
  | succ n =>
      have h := p04_recursive_complex_sum_error model n
        (fun i : Fin (n + 1) ↦ term ((ZMod.finEquiv (n + 1)).toEquiv i))
      simpa only [p04RoundedComplexSum_eq_recursive, Nat.succ_eq_add_one,
        Nat.add_sub_cancel_left, Equiv.sum_comp] using h

private theorem p04_radix_two_coefficient_exact (j : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · have hchar0 : ZMod.stdAddChar (0 : ZMod 2) = 1 := by
      rw [p04StdAddChar_positive_exp]
      norm_num
    change p04RadixTwoCoefficientApply (0 : ZMod 2) x =
      ZMod.stdAddChar (0 : ZMod 2) * x
    simp [p04RadixTwoCoefficientApply, hchar0]
  · have hangle : p04RootAngle (1 : ZMod 2) = Real.pi := by
      norm_num [p04RootAngle, ZMod.val_one]
    have hchar : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
      rw [p04_stdAddChar_eq_trig, hangle]
      apply Complex.ext <;> simp
    change p04RadixTwoCoefficientApply (1 : ZMod 2) x =
      ZMod.stdAddChar (1 : ZMod 2) * x
    have hne : (1 : ZMod 2) ≠ 0 := by decide
    simp [p04RadixTwoCoefficientApply, hchar, hne]

private theorem p04_radix_four_char_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  have hangle : p04RootAngle (1 : ZMod 4) = Real.pi / 2 := by
    change 2 * Real.pi * (((1 : ZMod 4).val : ℝ)) / 4 = Real.pi / 2
    have hval : (1 : ZMod 4).val = 1 := by decide
    rw [hval]
    ring
  rw [p04_stdAddChar_eq_trig, hangle]
  apply Complex.ext <;> simp

private theorem p04_radix_four_char_two :
    ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  have hangle : p04RootAngle (2 : ZMod 4) = Real.pi := by
    change 2 * Real.pi * (((2 : ZMod 4).val : ℝ)) / 4 = Real.pi
    have hval : (2 : ZMod 4).val = 2 := by decide
    rw [hval]
    ring
  rw [p04_stdAddChar_eq_trig, hangle]
  apply Complex.ext <;> simp

private theorem p04_radix_four_char_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have hangle : p04RootAngle (3 : ZMod 4) = 3 * Real.pi / 2 := by
    change 2 * Real.pi * (((3 : ZMod 4).val : ℝ)) / 4 = 3 * Real.pi / 2
    have hval : (3 : ZMod 4).val = 3 := by decide
    rw [hval]
    ring
  rw [p04_stdAddChar_eq_trig, hangle]
  have hsin : Real.sin (3 * Real.pi / 2) = -1 := by
    have heq : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [heq, Real.sin_add]
    simp
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    have heq : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
    rw [heq, Real.cos_add]
    simp
  apply Complex.ext <;> simp [hsin, hcos]

private theorem p04_radix_four_coefficient_exact (j : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · have hchar0 : ZMod.stdAddChar (0 : ZMod 4) = 1 := by
      rw [p04StdAddChar_positive_exp]
      norm_num
    change p04RadixFourCoefficientApply (0 : ZMod 4) x =
      ZMod.stdAddChar (0 : ZMod 4) * x
    simp [p04RadixFourCoefficientApply, hchar0]
  · change p04RadixFourCoefficientApply (1 : ZMod 4) x =
      ZMod.stdAddChar (1 : ZMod 4) * x
    have hne0 : (1 : ZMod 4) ≠ 0 := by decide
    simp [p04RadixFourCoefficientApply, p04_radix_four_char_one, hne0]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change p04RadixFourCoefficientApply (2 : ZMod 4) x =
      ZMod.stdAddChar (2 : ZMod 4) * x
    have hne0 : (2 : ZMod 4) ≠ 0 := by decide
    have hne1 : (2 : ZMod 4) ≠ 1 := by decide
    simp [p04RadixFourCoefficientApply, p04_radix_four_char_two, hne0, hne1]
  · change p04RadixFourCoefficientApply (3 : ZMod 4) x =
      ZMod.stdAddChar (3 : ZMod 4) * x
    have hne0 : (3 : ZMod 4) ≠ 0 := by decide
    have hne1 : (3 : ZMod 4) ≠ 1 := by decide
    have hne2 : (3 : ZMod 4) ≠ 2 := by decide
    simp [p04RadixFourCoefficientApply, p04_radix_four_char_three,
      hne0, hne1, hne2]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p04_rounded_four_tree_error (model : P04WilkinsonModel)
    (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) - (a + b + c + d)‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  have hu := p04_rounded_complex_add_error model a b
  have hv := p04_rounded_complex_add_error model c d
  have hnu : ‖u‖ ≤ (1 + model.epsilon) * (‖a‖ + ‖b‖) := by
    have h := norm_add_le (u - (a + b)) (a + b)
    have heq : u - (a + b) + (a + b) = u := by abel
    rw [heq] at h
    nlinarith [norm_add_le a b]
  have hnv : ‖v‖ ≤ (1 + model.epsilon) * (‖c‖ + ‖d‖) := by
    have h := norm_add_le (v - (c + d)) (c + d)
    have heq : v - (c + d) + (c + d) = v := by abel
    rw [heq] at h
    nlinarith [norm_add_le c d]
  have hlast := p04_rounded_complex_add_error model u v
  have htri : ‖p04RoundedComplexAdd model u v - (a + b + c + d)‖ ≤
      ‖p04RoundedComplexAdd model u v - (u + v)‖ +
        ‖u - (a + b)‖ + ‖v - (c + d)‖ := by
    have heq : p04RoundedComplexAdd model u v - (a + b + c + d) =
        (p04RoundedComplexAdd model u v - (u + v)) +
          ((u - (a + b)) + (v - (c + d))) := by abel
    rw [heq]
    nlinarith [norm_add_le
      (p04RoundedComplexAdd model u v - (u + v))
      ((u - (a + b)) + (v - (c + d))),
      norm_add_le (u - (a + b)) (v - (c + d))]
  have hlast' := mul_le_mul_of_nonneg_left (add_le_add hnu hnv)
    model.epsilon_pos.le
  nlinarith [htri, hlast, hlast', hu, hv]

private theorem p04_rounded_radix_four_block_error (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (∑ j : ZMod 4, ‖x j‖) := by
  let e : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let t : Fin 4 → ℂ := fun i ↦
    p04RadixFourCoefficientApply (e i * k) (x (e i))
  have ht (i : Fin 4) : t i = ZMod.stdAddChar (e i * k) * x (e i) :=
    p04_radix_four_coefficient_exact _ _
  have hnorm (i : Fin 4) : ‖t i‖ = ‖x (e i)‖ := by
    rw [ht, norm_mul, p04_stdAddChar_norm_eq_one, one_mul]
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      t 0 + t 1 + t 2 + t 3 := by
    calc
      (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
          ∑ i : Fin 4, ZMod.stdAddChar (e i * k) * x (e i) :=
        (Equiv.sum_comp e _).symm
      _ = ∑ i : Fin 4, t i := by simp_rw [ht]
      _ = t 0 + t 1 + t 2 + t 3 := by rw [Fin.sum_univ_four]
  have hsum : (∑ j : ZMod 4, ‖x j‖) =
      ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖ := by
    calc
      (∑ j : ZMod 4, ‖x j‖) = ∑ i : Fin 4, ‖x (e i)‖ :=
        (Equiv.sum_comp e _).symm
      _ = ∑ i : Fin 4, ‖t i‖ := by simp_rw [hnorm]
      _ = ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖ := by rw [Fin.sum_univ_four]
  have h := p04_rounded_four_tree_error model (t 0) (t 1) (t 2) (t 3)
  rw [hexact, hsum]
  exact h

private theorem p04_rounded_radix_two_block_error (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (∑ j : ZMod 2, ‖x j‖) := by
  let term : ZMod 2 → ℂ := fun j ↦
    p04RadixTwoCoefficientApply (j * k) (x j)
  have h := p04_rounded_complex_sum_error model term
  have ht (j : ZMod 2) : term j = ZMod.stdAddChar (j * k) * x j :=
    p04_radix_two_coefficient_exact _ _
  have hn (j : ZMod 2) : ‖term j‖ = ‖x j‖ := by
    rw [ht, norm_mul, p04_stdAddChar_norm_eq_one, one_mul]
  simpa [p04RoundedRadixTwoBlock, term, ht, hn] using h

private theorem p04_complex_norm2_sq {q : ℕ} [NeZero q]
    (x : ZMod q → ℂ) :
    p04ComplexNorm2 x ^ 2 = ∑ j : ZMod q, ‖x j‖ ^ 2 := by
  have hnon : 0 ≤ p04ComplexNorm2Sq x := by
    change 0 ≤ ∑ j : ZMod q, ‖x j‖ ^ 2
    exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (‖x i‖))
  rw [p04ComplexNorm2, Real.sq_sqrt hnon]
  rfl

private theorem p04_sum_norm_le_sqrt_card_norm2 {q : ℕ} [NeZero q]
    (x : ZMod q → ℂ) :
    (∑ j : ZMod q, ‖x j‖) ≤ Real.sqrt (q : ℝ) * p04ComplexNorm2 x := by
  have hsq := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (ZMod q))) (f := fun j ↦ ‖x j‖)
  have hcard : (Finset.univ : Finset (ZMod q)).card = q := by simp
  rw [hcard, ← p04_complex_norm2_sq] at hsq
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hsqrt : (Real.sqrt (q : ℝ) * p04ComplexNorm2 x) ^ 2 =
      (q : ℝ) * p04ComplexNorm2 x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hsum : 0 ≤ ∑ j : ZMod q, ‖x j‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hnorm : 0 ≤ Real.sqrt (q : ℝ) * p04ComplexNorm2 x := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact Real.sqrt_nonneg _
  nlinarith

private theorem p04_complex_norm2_le_card_mul_of_pointwise {q : ℕ} [NeZero q]
    (x e : ZMod q → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hpoint : ∀ k, ‖e k‖ ≤ B * (∑ j : ZMod q, ‖x j‖)) :
    p04ComplexNorm2 e ≤ (q : ℝ) * B * p04ComplexNorm2 x := by
  let S : ℝ := ∑ j : ZMod q, ‖x j‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hBS : 0 ≤ B * S := mul_nonneg hB hS
  have hsq (k : ZMod q) : ‖e k‖ ^ 2 ≤ (B * S) ^ 2 := by
    nlinarith [hpoint k, norm_nonneg (e k)]
  have hsum : (∑ k : ZMod q, ‖e k‖ ^ 2) ≤ (q : ℝ) * (B * S) ^ 2 := by
    calc
      (∑ k : ZMod q, ‖e k‖ ^ 2) ≤ ∑ _k : ZMod q, (B * S) ^ 2 :=
        Finset.sum_le_sum (fun k _ ↦ hsq k)
      _ = (q : ℝ) * (B * S) ^ 2 := by simp
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hbound : p04ComplexNorm2 e ≤ Real.sqrt (q : ℝ) * B * S := by
    have hsqrt : (Real.sqrt (q : ℝ) * B * S) ^ 2 =
        (q : ℝ) * (B * S) ^ 2 := by
      calc
        (Real.sqrt (q : ℝ) * B * S) ^ 2 =
            (Real.sqrt (q : ℝ)) ^ 2 * (B * S) ^ 2 := by ring
        _ = (q : ℝ) * (B * S) ^ 2 := by rw [Real.sq_sqrt hq]
    rw [← p04_complex_norm2_sq] at hsum
    have hnon : 0 ≤ Real.sqrt (q : ℝ) * B * S :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB) hS
    nlinarith [Real.sqrt_nonneg (p04ComplexNorm2Sq e)]
  have hx := p04_sum_norm_le_sqrt_card_norm2 x
  have hmul := mul_le_mul_of_nonneg_left hx
    (mul_nonneg (Real.sqrt_nonneg (q : ℝ)) hB)
  have hroot : Real.sqrt (q : ℝ) * B *
      (Real.sqrt (q : ℝ) * p04ComplexNorm2 x) =
      (q : ℝ) * B * p04ComplexNorm2 x := by
    calc
      Real.sqrt (q : ℝ) * B *
          (Real.sqrt (q : ℝ) * p04ComplexNorm2 x) =
          (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)) *
            B * p04ComplexNorm2 x := by ring
      _ = (q : ℝ) * B * p04ComplexNorm2 x := by
          rw [Real.mul_self_sqrt hq]
  rw [← hroot]
  exact hbound.trans hmul

private theorem p04_rounded_sum_perturbed_terms {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x term exact : ZMod q → ℂ)
    (δ c : ℝ) (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (hterm : ∀ j, ‖term j - exact j‖ ≤ δ * ‖x j‖)
    (hexact : ∀ j, ‖exact j‖ = ‖x j‖)
    (hsum : ‖p04RoundedComplexSum model term - ∑ j, term j‖ ≤
      c * (∑ j, ‖term j‖)) :
    ‖p04RoundedComplexSum model term - ∑ j, exact j‖ ≤
      (c * (1 + δ) + δ) * (∑ j, ‖x j‖) := by
  have hnorm (j : ZMod q) : ‖term j‖ ≤ (1 + δ) * ‖x j‖ := by
    have h := norm_add_le (term j - exact j) (exact j)
    have heq : term j - exact j + exact j = term j := by abel
    rw [heq, hexact] at h
    nlinarith [hterm j]
  have hnormsum : (∑ j, ‖term j‖) ≤
      (1 + δ) * (∑ j, ‖x j‖) := by
    calc
      (∑ j, ‖term j‖) ≤ ∑ j, (1 + δ) * ‖x j‖ :=
        Finset.sum_le_sum (fun j _ ↦ hnorm j)
      _ = (1 + δ) * (∑ j, ‖x j‖) := by rw [Finset.mul_sum]
  have herrsum : ‖(∑ j, term j) - ∑ j, exact j‖ ≤
      δ * (∑ j, ‖x j‖) := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : ZMod q, (term j - exact j)‖ ≤
          ∑ j : ZMod q, ‖term j - exact j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, δ * ‖x j‖ :=
        Finset.sum_le_sum (fun j _ ↦ hterm j)
      _ = δ * (∑ j, ‖x j‖) := by rw [Finset.mul_sum]
  have htri : ‖p04RoundedComplexSum model term - ∑ j, exact j‖ ≤
      ‖p04RoundedComplexSum model term - ∑ j, term j‖ +
        ‖(∑ j, term j) - ∑ j, exact j‖ := by
    have heq : p04RoundedComplexSum model term - ∑ j, exact j =
        (p04RoundedComplexSum model term - ∑ j, term j) +
          ((∑ j, term j) - ∑ j, exact j) := by abel
    rw [heq]
    exact norm_add_le _ _
  have hmul := mul_le_mul_of_nonneg_left hnormsum hc
  nlinarith [htri, hsum, hmul, herrsum]

private theorem p04_rounded_generic_radix_block_error
    (n : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod (n + 1) → ℂ)
        (k : ZMod (n + 1)),
        ‖p04RoundedGenericRadixBlock model x k -
            ∑ j : ZMod (n + 1), ZMod.stdAddChar (j * k) * x j‖ ≤
          (model.epsilon * (((n + 1 : ℕ) : ℝ) + 2 + 2 * γ) +
            C * model.epsilon ^ 2) * (∑ j, ‖x j‖) := by
  obtain ⟨Cpow, hCpow, hpow⟩ := p04_pow_one_add_first_order n
  let A : ℝ := 3 + 2 * γ
  let B : ℝ := 2 + 10 * γ
  let C : ℝ := Cpow + ((n : ℝ) + Cpow) * (A + B) + B
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ hε x k
  let term : ZMod (n + 1) → ℂ := fun j ↦
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let exact : ZMod (n + 1) → ℂ := fun j ↦
    ZMod.stdAddChar (j * k) * x j
  let δ : ℝ := model.epsilon * (A + B * model.epsilon)
  let c : ℝ := (1 + model.epsilon) ^ n - 1
  have hε0 : 0 ≤ model.epsilon := model.epsilon_pos.le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact mul_nonneg hε0 (add_nonneg hA (mul_nonneg hB hε0))
  have hc : 0 ≤ c := by
    dsimp [c]
    have hbase : 1 ≤ 1 + model.epsilon := by linarith
    have hp : (1 : ℝ) ^ n ≤ (1 + model.epsilon) ^ n :=
      pow_le_pow_left₀ (by norm_num) hbase _
    simpa using sub_nonneg.mpr hp
  have hterm (j : ZMod (n + 1)) :
      ‖term j - exact j‖ ≤ δ * ‖x j‖ := by
    dsimp [term, exact, δ, A, B]
    simpa [hmodelγ, add_assoc, mul_assoc] using
      p04_rounded_root_mul_error model (j * k) (x j) hε
  have hexact (j : ZMod (n + 1)) : ‖exact j‖ = ‖x j‖ := by
    dsimp [exact]
    rw [norm_mul, p04_stdAddChar_norm_eq_one, one_mul]
  have hsum : ‖p04RoundedComplexSum model term - ∑ j, term j‖ ≤
      c * (∑ j, ‖term j‖) := by
    simpa [c] using p04_rounded_complex_sum_error model term
  have hmain := p04_rounded_sum_perturbed_terms model x term exact δ c
    hδ hc hterm hexact hsum
  have hpow' : c ≤ (n : ℝ) * model.epsilon + Cpow * model.epsilon ^ 2 :=
    hpow model.epsilon hε0 hε
  have hεsq : model.epsilon ^ 2 ≤ model.epsilon := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hε)]
  have hclinear : c ≤ ((n : ℝ) + Cpow) * model.epsilon := by
    have hh := mul_le_mul_of_nonneg_left hεsq hCpow
    nlinarith [hpow', hh]
  have hδlinear : δ ≤ (A + B) * model.epsilon := by
    have hh := mul_le_mul_of_nonneg_left hεsq hB
    dsimp [δ]
    nlinarith [hh]
  have hprod : c * δ ≤
      ((n : ℝ) + Cpow) * (A + B) * model.epsilon ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_right hclinear hδ
    have hright := mul_le_mul_of_nonneg_left hδlinear
      (mul_nonneg (by positivity : 0 ≤ (n : ℝ) + Cpow) hε0)
    nlinarith [hleft, hright]
  have hcoeff : c * (1 + δ) + δ ≤
      model.epsilon * (((n + 1 : ℕ) : ℝ) + 2 + 2 * γ) +
        C * model.epsilon ^ 2 := by
    dsimp [C, δ, A, B]
    push_cast
    nlinarith [hpow', hprod]
  have hS : 0 ≤ ∑ j : ZMod (n + 1), ‖x j‖ :=
    Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hcoeff hS
  simpa [p04RoundedGenericRadixBlock, term, exact] using hmain.trans hm

private noncomputable def p04BlockBeta (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 1 else if q = 4 then 2 else (q : ℝ) + 2 + 2 * γ

private theorem p04BlockBeta_nonneg (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04BlockBeta q γ := by
  simp only [p04BlockBeta]
  split_ifs <;> positivity

private theorem p04BlockBeta_alpha_bound (q : ℕ) (hq : 2 ≤ q)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (q : ℝ) * p04BlockBeta q γ ≤
      Real.sqrt (q : ℝ) * p04Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    simp [p04BlockBeta, p04Alpha, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases h4 : q = 4
  · subst q
    norm_num [p04BlockBeta, p04Alpha]
  have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  simp only [p04BlockBeta, p04Alpha, if_neg h2, if_neg h4]
  have hroot := Real.mul_self_sqrt hq0
  nlinarith [mul_nonneg (show 0 ≤ (q : ℝ) by positivity)
    (show 0 ≤ (q : ℝ) - 2 by linarith)]

private noncomputable def p04RoundedRadixBlock {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  if h2 : q = 2 then
    p04RoundedRadixTwoBlock model
      (fun j : ZMod 2 ↦ x (h2.symm ▸ j)) (h2 ▸ k)
  else if h4 : q = 4 then
    p04RoundedRadixFourBlock model
      (fun j : ZMod 4 ↦ x (h4.symm ▸ j)) (h4 ▸ k)
  else p04RoundedGenericRadixBlock model x k

private theorem p04RoundedRadixBlock_pointwise {q : ℕ} [NeZero q]
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod q → ℂ) (k : ZMod q),
        ‖p04RoundedRadixBlock model x k -
            ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
          (model.epsilon * p04BlockBeta q γ +
            C * model.epsilon ^ 2) * (∑ j : ZMod q, ‖x j‖) := by
  by_cases h2 : q = 2
  · subst q
    refine ⟨0, le_rfl, ?_⟩
    intro model hmodelγ hε x k
    simpa [p04RoundedRadixBlock, p04BlockBeta] using
      p04_rounded_radix_two_block_error model x k
  by_cases h4 : q = 4
  · subst q
    refine ⟨1, by norm_num, ?_⟩
    intro model hmodelγ hε x k
    simpa [p04RoundedRadixBlock, p04BlockBeta, mul_add, mul_assoc, pow_two] using
      p04_rounded_radix_four_block_error model x k
  cases q with
  | zero => exact (NeZero.ne (0 : ℕ)) rfl |>.elim
  | succ n =>
      obtain ⟨C, hC, h⟩ := p04_rounded_generic_radix_block_error n γ hγ
      refine ⟨C, hC, ?_⟩
      intro model hmodelγ hε x k
      simpa [p04RoundedRadixBlock, p04BlockBeta, h2, h4] using
        h model hmodelγ hε x k

private theorem p04RoundedRadixBlock_norm_error {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod q → ℂ),
        p04ComplexNorm2 (fun k ↦ p04RoundedRadixBlock model x k -
            ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
          (model.epsilon * Real.sqrt (q : ℝ) * p04Alpha q γ +
            C * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  obtain ⟨Cpt, hCpt, hpt⟩ := p04RoundedRadixBlock_pointwise γ hγ (q := q)
  refine ⟨(q : ℝ) * Cpt, mul_nonneg (Nat.cast_nonneg _) hCpt, ?_⟩
  intro model hmodelγ hε x
  let B : ℝ := model.epsilon * p04BlockBeta q γ +
    Cpt * model.epsilon ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg model.epsilon_pos.le (p04BlockBeta_nonneg q γ hγ))
      (mul_nonneg hCpt (sq_nonneg _))
  have hvec := p04_complex_norm2_le_card_mul_of_pointwise x
    (fun k ↦ p04RoundedRadixBlock model x k -
      ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) B hB
    (hpt model hmodelγ hε x)
  have hcoeff : (q : ℝ) * B ≤
      model.epsilon * Real.sqrt (q : ℝ) * p04Alpha q γ +
        ((q : ℝ) * Cpt) * model.epsilon ^ 2 := by
    dsimp [B]
    have hh := mul_le_mul_of_nonneg_left
      (p04BlockBeta_alpha_bound q hq γ hγ) model.epsilon_pos.le
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (Real.sqrt_nonneg (p04ComplexNorm2Sq x))
  exact hvec.trans hm

private theorem p04_sqrt_sum_sq_le_mul {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (h : ∀ i, a i ≤ C * b i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ C * Real.sqrt (∑ i, b i ^ 2) := by
  have hsq (i : ι) : a i ^ 2 ≤ C ^ 2 * b i ^ 2 := by
    have hc : 0 ≤ C * b i := mul_nonneg hC (hb i)
    nlinarith [h i, ha i]
  have hsum : (∑ i, a i ^ 2) ≤ C ^ 2 * (∑ i, b i ^ 2) := by
    calc
      (∑ i, a i ^ 2) ≤ ∑ i, C ^ 2 * b i ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ hsq i)
      _ = C ^ 2 * (∑ i, b i ^ 2) := by rw [Finset.mul_sum]
  have hsumA : 0 ≤ ∑ i, a i ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hsumB : 0 ≤ ∑ i, b i ^ 2 :=
    Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hsqA : (Real.sqrt (∑ i, a i ^ 2)) ^ 2 = ∑ i, a i ^ 2 :=
    Real.sq_sqrt hsumA
  have hsqB : (C * Real.sqrt (∑ i, b i ^ 2)) ^ 2 =
      C ^ 2 * (∑ i, b i ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hsumB]
  have hnonA := Real.sqrt_nonneg (∑ i, a i ^ 2)
  have hnonB : 0 ≤ C * Real.sqrt (∑ i, b i ^ 2) :=
    mul_nonneg hC (Real.sqrt_nonneg _)
  nlinarith

private theorem p04_complex_norm2_rows {n q : ℕ} [NeZero n] [NeZero q]
    {ι : Type*} [Fintype ι]
    (e : ι × ZMod q ≃ ZMod n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 x =
      Real.sqrt (∑ b : ι,
        p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2) := by
  have hsq : p04ComplexNorm2 x ^ 2 =
      ∑ b : ι, p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2 := by
    rw [p04_complex_norm2_sq]
    calc
      (∑ i : ZMod n, ‖x i‖ ^ 2) =
          ∑ ij : ι × ZMod q, ‖x (e ij)‖ ^ 2 :=
        (Equiv.sum_comp e _).symm
      _ = ∑ b : ι, ∑ j : ZMod q, ‖x (e (b, j))‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
      _ = ∑ b : ι,
          p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2 := by
        congr 1
        funext b
        rw [p04_complex_norm2_sq]
  have hrhs : 0 ≤ Real.sqrt (∑ b : ι,
      p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2) :=
    Real.sqrt_nonneg _
  have hnorm : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  have hsqrt : (Real.sqrt (∑ b : ι,
      p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2)) ^ 2 =
      ∑ b : ι,
        p04ComplexNorm2 (fun j : ZMod q ↦ x (e (b, j))) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  nlinarith

private theorem p04_complex_norm2_perm {n : ℕ} [NeZero n]
    (e : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i ↦ x (e i)) = p04ComplexNorm2 x := by
  have hsq : p04ComplexNorm2 (fun i ↦ x (e i)) ^ 2 =
      p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq, p04_complex_norm2_sq]
    exact Equiv.sum_comp e (fun i : ZMod n ↦ ‖x i‖ ^ 2)
  have h1 : 0 ≤ p04ComplexNorm2 (fun i ↦ x (e i)) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith

private theorem p04_rounded_stage_block_norm_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i ↦
            p04RoundedMixedRadixBlockApply model stage x i -
              p04MixedRadixBlockApply stage x i) ≤
          (model.epsilon * Real.sqrt (stage.radix : ℝ) *
              p04Alpha stage.radix γ + C * model.epsilon ^ 2) *
            p04ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  obtain ⟨C, hC, hblock⟩ :=
    p04RoundedRadixBlock_norm_error stage.radix_two_le γ hγ
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ hε x
  let row : Fin stage.blockCount → ZMod stage.radix → ℂ :=
    fun b j ↦ x (stage.permutation (stage.reindex (b, j)))
  let err : ZMod n → ℂ := fun i ↦
    p04RoundedMixedRadixBlockApply model stage x i -
      p04MixedRadixBlockApply stage x i
  have hrow (b : Fin stage.blockCount) (k : ZMod stage.radix) :
      err (stage.reindex (b, k)) =
        p04RoundedRadixBlock model (row b) k -
          ∑ j : ZMod stage.radix,
            ZMod.stdAddChar (j * k) * row b j := by
    simp [err, row, p04RoundedMixedRadixBlockApply,
      p04MixedRadixBlockApply, p04RoundedRadixBlock]
  have hnormrow (b : Fin stage.blockCount) :
      p04ComplexNorm2 (fun k : ZMod stage.radix ↦
        err (stage.reindex (b, k))) ≤
        (model.epsilon * Real.sqrt (stage.radix : ℝ) *
            p04Alpha stage.radix γ + C * model.epsilon ^ 2) *
          p04ComplexNorm2 (row b) := by
    simpa only [hrow] using hblock model hmodelγ hε (row b)
  have hcoef : 0 ≤ model.epsilon * Real.sqrt (stage.radix : ℝ) *
      p04Alpha stage.radix γ + C * model.epsilon ^ 2 := by
    have halpha : 0 ≤ p04Alpha stage.radix γ := by
      simp [p04Alpha]
      split_ifs <;> positivity
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg model.epsilon_pos.le (Real.sqrt_nonneg _)) halpha)
      (mul_nonneg hC (sq_nonneg _))
  have hroot := p04_sqrt_sum_sq_le_mul
    (fun b : Fin stage.blockCount ↦
      p04ComplexNorm2 (fun k : ZMod stage.radix ↦
        err (stage.reindex (b, k))))
    (fun b : Fin stage.blockCount ↦ p04ComplexNorm2 (row b))
    (model.epsilon * Real.sqrt (stage.radix : ℝ) *
      p04Alpha stage.radix γ + C * model.epsilon ^ 2)
    hcoef (fun _ ↦ Real.sqrt_nonneg _) (fun _ ↦ Real.sqrt_nonneg _)
    hnormrow
  have herr := p04_complex_norm2_rows stage.reindex err
  have hinput := p04_complex_norm2_rows stage.reindex
    (fun i ↦ x (stage.permutation i))
  have hperm := p04_complex_norm2_perm stage.permutation x
  change p04ComplexNorm2 err ≤ _
  rw [herr, ← hperm, hinput]
  exact hroot

private theorem p04_complex_norm2_le_mul_of_pointwise {n : ℕ} [NeZero n]
    (x e : ZMod n → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ i, ‖e i‖ ≤ B * ‖x i‖) :
    p04ComplexNorm2 e ≤ B * p04ComplexNorm2 x := by
  have hh := p04_sqrt_sum_sq_le_mul
    (fun i : ZMod n ↦ ‖e i‖) (fun i : ZMod n ↦ ‖x i‖) B hB
    (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _) h
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq] using hh

private theorem p04_stage_twiddle_norm {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) =
      p04ComplexNorm2 x := by
  have hpoint (i : ZMod n) : ‖p04MixedRadixTwiddleApply stage x i‖ = ‖x i‖ := by
    simp only [p04MixedRadixTwiddleApply]
    split_ifs with h
    · rw [norm_mul, p04_stdAddChar_norm_eq_one, one_mul]
    · rfl
  have hsq : p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) ^ 2 =
      p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq, p04_complex_norm2_sq]
    simp_rw [hpoint]
  have h1 : 0 ≤ p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith

private theorem p04_stage_twiddle_add {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixTwiddleApply stage (fun i ↦ x i + y i) =
      fun i ↦ p04MixedRadixTwiddleApply stage x i +
        p04MixedRadixTwiddleApply stage y i := by
  funext i
  simp only [p04MixedRadixTwiddleApply]
  split_ifs <;> ring

private theorem p04_stage_twiddle_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixTwiddleApply stage (fun i ↦ x i - y i) =
      fun i ↦ p04MixedRadixTwiddleApply stage x i -
        p04MixedRadixTwiddleApply stage y i := by
  funext i
  simp only [p04MixedRadixTwiddleApply]
  split_ifs <;> ring

private theorem p04_stage_twiddle_rounded_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ)
    (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
    (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i) ≤
      (model.epsilon * (3 + 2 * γ) +
        (2 + 10 * γ) * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  let B : ℝ := model.epsilon * (3 + 2 * γ) +
    (2 + 10 * γ) * model.epsilon ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg model.epsilon_pos.le (by linarith))
      (mul_nonneg (by linarith) (sq_nonneg _))
  apply p04_complex_norm2_le_mul_of_pointwise x _ B hB
  intro i
  simp only [p04RoundedMixedRadixTwiddleApply,
    p04MixedRadixTwiddleApply]
  split_ifs with hi
  · calc
      ‖p04RoundedComplexMul model
          (p04RoundedRoot model (stage.twiddleExponent i)) (x i) -
          ZMod.stdAddChar (stage.twiddleExponent i) * x i‖ ≤
          model.epsilon * (3 + 2 * model.gamma +
            (2 + 10 * model.gamma) * model.epsilon) * ‖x i‖ :=
        p04_rounded_root_mul_error model _ _ hε
      _ = B * ‖x i‖ := by
        congr 1
        dsimp [B]
        rw [hmodelγ]
        ring
  · simp only [sub_self, norm_zero]
    exact mul_nonneg hB (norm_nonneg _)

private theorem p04_complex_norm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i ↦ x i + y i) ≤
      p04ComplexNorm2 x + p04ComplexNorm2 y := by
  simp only [p04_complex_norm2_eq]
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))
    (WithLp.toLp 2 y : EuclideanSpace ℂ (ZMod n))

private theorem p04_first_order_compose_scalar
    (ε s a b C D : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (ε * b + D * ε ^ 2) * (s + ε * a + C * ε ^ 2) +
        (ε * a + C * ε ^ 2) ≤
      ε * (a + s * b) +
        (s * D + C + (b + D) * (a + C)) * ε ^ 2 := by
  have hεsq : ε ^ 2 ≤ ε := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hε1)]
  have hleft : ε * b + D * ε ^ 2 ≤ ε * (b + D) := by
    nlinarith [mul_le_mul_of_nonneg_left hεsq hD]
  have hright : ε * a + C * ε ^ 2 ≤ ε * (a + C) := by
    nlinarith [mul_le_mul_of_nonneg_left hεsq hC]
  have hleft0 : 0 ≤ ε * b + D * ε ^ 2 := by positivity
  have hright0 : 0 ≤ ε * a + C * ε ^ 2 := by positivity
  have hprod : (ε * b + D * ε ^ 2) *
      (ε * a + C * ε ^ 2) ≤ (b + D) * (a + C) * ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hleft hright0
    have h2 := mul_le_mul_of_nonneg_left hright
      (mul_nonneg hε0 (add_nonneg hb hD))
    nlinarith [h1, h2]
  have hD' := mul_le_mul_of_nonneg_left hεsq hD
  nlinarith [hprod, hD', mul_nonneg hs (sub_nonneg.mpr hD')]

private theorem p04_stage_twiddle_rounded_error_if {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ)
    (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
    (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i) ≤
      (model.epsilon * (if stage.useTwiddle then 3 + 2 * γ else 0) +
        (if stage.useTwiddle then 2 + 10 * γ else 0) *
          model.epsilon ^ 2) * p04ComplexNorm2 x := by
  by_cases h : stage.useTwiddle = true
  · simp only [h, ite_true]
    exact p04_stage_twiddle_rounded_error stage γ hγ model hmodelγ hε x
  · have hfalse : stage.useTwiddle = false := by
      cases hv : stage.useTwiddle <;> simp_all
    simp only [hfalse, Bool.false_eq_true, ite_false, mul_zero, zero_mul,
      add_zero, zero_le']
    have heq : (fun i ↦ p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) = fun _ ↦ 0 := by
      funext i
      simp [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, hfalse]
    rw [heq]
    simp [p04ComplexNorm2, p04ComplexNorm2Sq]

private theorem p04_rounded_stage_norm_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i ↦
            p04RoundedMixedRadixStageApply model stage x i -
              p04MixedRadixStageApply stage x i) ≤
          (model.epsilon * Real.sqrt (stage.radix : ℝ) *
              (p04Alpha stage.radix γ +
                if stage.useTwiddle then 3 + 2 * γ else 0) +
            C * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  obtain ⟨Cblock, hCblock, hblock⟩ :=
    p04_rounded_stage_block_norm_error stage γ hγ
  let s : ℝ := Real.sqrt (stage.radix : ℝ)
  let a : ℝ := s * p04Alpha stage.radix γ
  let b : ℝ := if stage.useTwiddle then 3 + 2 * γ else 0
  let D : ℝ := if stage.useTwiddle then 2 + 10 * γ else 0
  let C : ℝ := s * D + Cblock + (b + D) * (a + Cblock)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have halpha : 0 ≤ p04Alpha stage.radix γ := by
    simp [p04Alpha]
    split_ifs <;> positivity
  have ha : 0 ≤ a := mul_nonneg hs halpha
  have hb : 0 ≤ b := by dsimp [b]; split_ifs <;> linarith
  have hD : 0 ≤ D := by dsimp [D]; split_ifs <;> linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg (mul_nonneg hs hD) hCblock)
      (mul_nonneg (add_nonneg hb hD) (add_nonneg ha hCblock))
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ hε x
  let u : ZMod n → ℂ := p04RoundedMixedRadixBlockApply model stage x
  let v : ZMod n → ℂ := p04MixedRadixBlockApply stage x
  let e : ZMod n → ℂ := fun i ↦ u i - v i
  let T : ℝ := model.epsilon * b + D * model.epsilon ^ 2
  let E : ℝ := model.epsilon * a + Cblock * model.epsilon ^ 2
  have hT : 0 ≤ T :=
    add_nonneg (mul_nonneg model.epsilon_pos.le hb)
      (mul_nonneg hD (sq_nonneg _))
  have hE : 0 ≤ E :=
    add_nonneg (mul_nonneg model.epsilon_pos.le ha)
      (mul_nonneg hCblock (sq_nonneg _))
  have herr : p04ComplexNorm2 e ≤ E * p04ComplexNorm2 x := by
    simpa [e, E, a, s, u, v, mul_assoc] using hblock model hmodelγ hε x
  have hv : p04ComplexNorm2 v = s * p04ComplexNorm2 x := by
    have hh := hscale x
    simpa [p04MixedRadixStageApply, p04_stage_twiddle_norm, v, s] using hh
  have hu : p04ComplexNorm2 u ≤ (s + E) * p04ComplexNorm2 x := by
    have htri := p04_complex_norm2_add_le e v
    have heq : (fun i ↦ e i + v i) = u := by funext i; simp [e]
    rw [heq, hv] at htri
    nlinarith [herr]
  have htw := p04_stage_twiddle_rounded_error_if stage γ hγ
    model hmodelγ hε u
  have htw' : p04ComplexNorm2 (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage u i -
          p04MixedRadixTwiddleApply stage u i) ≤
      T * p04ComplexNorm2 u := by
    simpa [T, b, D] using htw
  have hdecomp : (fun i ↦
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) =
      fun i ↦
        (p04RoundedMixedRadixTwiddleApply model stage u i -
          p04MixedRadixTwiddleApply stage u i) +
        p04MixedRadixTwiddleApply stage e i := by
    funext i
    have hsub := congrFun (p04_stage_twiddle_sub stage u v) i
    simp only [p04RoundedMixedRadixStageApply,
      p04MixedRadixStageApply, u, v, e] at *
    rw [hsub]
    ring
  have htri : p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
      p04ComplexNorm2 (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage u i -
          p04MixedRadixTwiddleApply stage u i) +
        p04ComplexNorm2 e := by
    rw [hdecomp]
    have hh := p04_complex_norm2_add_le
      (fun i ↦ p04RoundedMixedRadixTwiddleApply model stage u i -
        p04MixedRadixTwiddleApply stage u i)
      (p04MixedRadixTwiddleApply stage e)
    rwa [p04_stage_twiddle_norm] at hh
  have hmul := mul_le_mul_of_nonneg_left hu hT
  have hnum : p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
      (T * (s + E) + E) * p04ComplexNorm2 x := by
    nlinarith [htri, htw', hmul, herr]
  have hscalar := p04_first_order_compose_scalar model.epsilon s a b
    Cblock D model.epsilon_pos.le hε hs ha hb hCblock hD
  have htarget : T * (s + E) + E ≤
      model.epsilon * s *
        (p04Alpha stage.radix γ + b) + C * model.epsilon ^ 2 := by
    simpa [T, E, C, a, mul_add, mul_assoc, add_assoc] using hscalar
  have hmul' := mul_le_mul_of_nonneg_right htarget
    (Real.sqrt_nonneg (p04ComplexNorm2Sq x))
  simpa [s, b, C] using hnum.trans hmul'

private theorem p04_stage_block_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixBlockApply stage (fun i ↦ x i - y i) =
      fun i ↦ p04MixedRadixBlockApply stage x i -
        p04MixedRadixBlockApply stage y i := by
  funext i
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  simp only [p04MixedRadixBlockApply]
  rw [← Finset.sum_sub_distrib]
  congr 1
  funext j
  ring

private theorem p04_stage_exact_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixStageApply stage (fun i ↦ x i - y i) =
      fun i ↦ p04MixedRadixStageApply stage x i -
        p04MixedRadixStageApply stage y i := by
  simp only [p04MixedRadixStageApply, p04_stage_block_sub]
  exact p04_stage_twiddle_sub stage
    (p04MixedRadixBlockApply stage x) (p04MixedRadixBlockApply stage y)

private noncomputable def p04StageScale {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) : ℝ := Real.sqrt (stage.radix : ℝ)

private noncomputable def p04StageK {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  p04Alpha stage.radix γ + if stage.useTwiddle then 3 + 2 * γ else 0

private noncomputable def p04ListScale {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) : ℝ :=
  (l.map p04StageScale).prod

private noncomputable def p04ListK {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (γ : ℝ) : ℝ :=
  (l.map (fun stage ↦ p04StageK stage γ)).sum

private noncomputable def p04ExactFold {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state stage ↦ p04MixedRadixStageApply stage state) x

private noncomputable def p04RoundedFold {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel)
    (l : List (P04MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state stage ↦ p04RoundedMixedRadixStageApply model stage state) x

private theorem p04StageScale_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) : 0 ≤ p04StageScale stage :=
  Real.sqrt_nonneg _

private theorem p04StageK_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04StageK stage γ := by
  have ha : 0 ≤ p04Alpha stage.radix γ := by
    simp [p04Alpha]
    split_ifs <;> positivity
  simp only [p04StageK]
  split_ifs <;> linarith

private theorem p04ListScale_nonneg {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) : 0 ≤ p04ListScale l := by
  induction l with
  | nil => simp [p04ListScale]
  | cons s l ih =>
      simpa [p04ListScale] using mul_nonneg (p04StageScale_nonneg s) ih

private theorem p04ListK_nonneg {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04ListK l γ := by
  induction l with
  | nil => simp [p04ListK]
  | cons s l ih =>
      simpa [p04ListK] using add_nonneg (p04StageK_nonneg s γ hγ) ih

private theorem p04ExactFold_sub {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (x y : ZMod n → ℂ) :
    p04ExactFold l (fun i ↦ x i - y i) =
      fun i ↦ p04ExactFold l x i - p04ExactFold l y i := by
  induction l generalizing x y with
  | nil => rfl
  | cons s l ih =>
      simp only [p04ExactFold, List.foldl_cons]
      change p04ExactFold l (p04MixedRadixStageApply s (fun i ↦ x i - y i)) =
        fun i ↦ p04ExactFold l (p04MixedRadixStageApply s x) i -
          p04ExactFold l (p04MixedRadixStageApply s y) i
      rw [p04_stage_exact_sub]
      exact ih _ _

private theorem p04ExactFold_norm {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n))
    (hscale : ∀ s ∈ l, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        p04StageScale s * p04ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04ExactFold l x) =
      p04ListScale l * p04ComplexNorm2 x := by
  induction l generalizing x with
  | nil => simp [p04ExactFold, p04ListScale]
  | cons s l ih =>
      have hscale_tail : ∀ t ∈ l, ∀ x : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply t x) =
            p04StageScale t * p04ComplexNorm2 x := by
        intro t ht x
        exact hscale t (List.mem_cons_of_mem s ht) x
      have hs := hscale s (by simp) x
      change p04ComplexNorm2 (p04ExactFold l (p04MixedRadixStageApply s x)) = _
      rw [ih hscale_tail, hs]
      simp [p04ListScale]
      ring

private theorem p04_chain_compose_scalar
    (ε p s k K C D : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hs : 0 ≤ s) (hk : 0 ≤ k) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    (ε * p * K + D * ε ^ 2) *
        (s + ε * s * k + C * ε ^ 2) +
        p * (ε * s * k + C * ε ^ 2) ≤
      ε * (p * s) * (K + k) +
        (D * s + p * C + (p * K + D) * (s * k + C)) * ε ^ 2 := by
  have hεsq : ε ^ 2 ≤ ε := by
    nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hε1)]
  have hl : ε * p * K + D * ε ^ 2 ≤ ε * (p * K + D) := by
    nlinarith [mul_le_mul_of_nonneg_left hεsq hD]
  have hr : ε * s * k + C * ε ^ 2 ≤ ε * (s * k + C) := by
    nlinarith [mul_le_mul_of_nonneg_left hεsq hC]
  have hl0 : 0 ≤ ε * p * K + D * ε ^ 2 := by positivity
  have hr0 : 0 ≤ ε * s * k + C * ε ^ 2 := by positivity
  have hprod : (ε * p * K + D * ε ^ 2) *
      (ε * s * k + C * ε ^ 2) ≤
      (p * K + D) * (s * k + C) * ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hl hr0
    have h2 := mul_le_mul_of_nonneg_left hr
      (mul_nonneg hε0 (add_nonneg (mul_nonneg hp hK) hD))
    nlinarith [h1, h2]
  nlinarith [hprod]

private theorem p04RoundedFold_error {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ)
    (hscale : ∀ s ∈ l, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        p04StageScale s * p04ComplexNorm2 x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i ↦
            p04RoundedFold model l x i - p04ExactFold l x i) ≤
          (model.epsilon * p04ListScale l * p04ListK l γ +
            C * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  induction l with
  | nil =>
      refine ⟨0, le_rfl, ?_⟩
      intro model hmodelγ hε x
      simp [p04RoundedFold, p04ExactFold, p04ListScale,
        p04ListK, p04ComplexNorm2, p04ComplexNorm2Sq]
  | cons s l ih =>
      have htail : ∀ t ∈ l, ∀ x : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply t x) =
            p04StageScale t * p04ComplexNorm2 x := by
        intro t ht x
        exact hscale t (List.mem_cons_of_mem s ht) x
      obtain ⟨D, hD, htailerr⟩ := ih htail
      have hs_scale := hscale s (by simp)
      obtain ⟨C, hC, hheaderr⟩ :=
        p04_rounded_stage_norm_error s hs_scale γ hγ
      let p : ℝ := p04ListScale l
      let ss : ℝ := p04StageScale s
      let k : ℝ := p04StageK s γ
      let K : ℝ := p04ListK l γ
      let E : ℝ := D * ss + p * C + (p * K + D) * (ss * k + C)
      have hp : 0 ≤ p := p04ListScale_nonneg l
      have hss : 0 ≤ ss := p04StageScale_nonneg s
      have hk : 0 ≤ k := p04StageK_nonneg s γ hγ
      have hK : 0 ≤ K := p04ListK_nonneg l γ hγ
      have hE : 0 ≤ E := by
        dsimp [E]
        exact add_nonneg
          (add_nonneg (mul_nonneg hD hss) (mul_nonneg hp hC))
          (mul_nonneg (add_nonneg (mul_nonneg hp hK) hD)
            (add_nonneg (mul_nonneg hss hk) hC))
      refine ⟨E, hE, ?_⟩
      intro model hmodelγ hε x
      let u : ZMod n → ℂ := p04RoundedMixedRadixStageApply model s x
      let v : ZMod n → ℂ := p04MixedRadixStageApply s x
      let e : ZMod n → ℂ := fun i ↦ u i - v i
      let L : ℝ := model.epsilon * ss * k + C * model.epsilon ^ 2
      let T : ℝ := model.epsilon * p * K + D * model.epsilon ^ 2
      have hL : 0 ≤ L := by
        dsimp [L]
        exact add_nonneg
          (mul_nonneg (mul_nonneg model.epsilon_pos.le hss) hk)
          (mul_nonneg hC (sq_nonneg _))
      have hT : 0 ≤ T := by
        dsimp [T]
        exact add_nonneg
          (mul_nonneg (mul_nonneg model.epsilon_pos.le hp) hK)
          (mul_nonneg hD (sq_nonneg _))
      have he : p04ComplexNorm2 e ≤ L * p04ComplexNorm2 x := by
        simpa [e, u, v, L, ss, k, p04StageScale, p04StageK,
          mul_assoc] using hheaderr model hmodelγ hε x
      have hv : p04ComplexNorm2 v = ss * p04ComplexNorm2 x :=
        hs_scale x
      have hu : p04ComplexNorm2 u ≤ (ss + L) * p04ComplexNorm2 x := by
        have htri := p04_complex_norm2_add_le e v
        have heq : (fun i ↦ e i + v i) = u := by funext i; simp [e]
        rw [heq, hv] at htri
        nlinarith [he]
      have htailu : p04ComplexNorm2 (fun i ↦
          p04RoundedFold model l u i - p04ExactFold l u i) ≤
          T * p04ComplexNorm2 u := by
        simpa [T, p, K] using htailerr model hmodelγ hε u
      have htailprop : p04ComplexNorm2 (fun i ↦
          p04ExactFold l u i - p04ExactFold l v i) =
          p * p04ComplexNorm2 e := by
        rw [← p04ExactFold_sub l u v]
        exact p04ExactFold_norm l htail e
      have hdecomp : (fun i ↦
          p04RoundedFold model (s :: l) x i -
            p04ExactFold (s :: l) x i) =
          fun i ↦ (p04RoundedFold model l u i - p04ExactFold l u i) +
            (p04ExactFold l u i - p04ExactFold l v i) := by
        funext i
        simp only [p04RoundedFold, p04ExactFold, List.foldl_cons]
        change p04RoundedFold model l u i - p04ExactFold l v i =
          (p04RoundedFold model l u i - p04ExactFold l u i) +
            (p04ExactFold l u i - p04ExactFold l v i)
        ring
      have htri : p04ComplexNorm2 (fun i ↦
          p04RoundedFold model (s :: l) x i -
            p04ExactFold (s :: l) x i) ≤
          p04ComplexNorm2 (fun i ↦
            p04RoundedFold model l u i - p04ExactFold l u i) +
          p04ComplexNorm2 (fun i ↦
            p04ExactFold l u i - p04ExactFold l v i) := by
        rw [hdecomp]
        exact p04_complex_norm2_add_le _ _
      have hmul := mul_le_mul_of_nonneg_left hu hT
      have hmul' := mul_le_mul_of_nonneg_left he hp
      have hnum : p04ComplexNorm2 (fun i ↦
          p04RoundedFold model (s :: l) x i -
            p04ExactFold (s :: l) x i) ≤
          (T * (ss + L) + p * L) * p04ComplexNorm2 x := by
        nlinarith [htri, htailu, htailprop, hmul, hmul']
      have hscalar := p04_chain_compose_scalar model.epsilon p ss k K C D
        model.epsilon_pos.le hε hp hss hk hK hC hD
      have hcoeff : T * (ss + L) + p * L ≤
          model.epsilon * p04ListScale (s :: l) * p04ListK (s :: l) γ +
            E * model.epsilon ^ 2 := by
        have hcoeff0 : T * (ss + L) + p * L ≤
            model.epsilon * (p * ss) * (K + k) + E * model.epsilon ^ 2 := by
          simpa [T, L, E, add_assoc] using hscalar
        have hprod : p04ListScale (s :: l) = p * ss := by
          simp [p04ListScale, p, ss, mul_comm]
        have hsum : p04ListK (s :: l) γ = K + k := by
          simp [p04ListK, K, k, add_comm]
        rw [hprod, hsum]
        exact hcoeff0
      have hmul'' := mul_le_mul_of_nonneg_right hcoeff
        (Real.sqrt_nonneg (p04ComplexNorm2Sq x))
      exact hnum.trans hmul''

private theorem p04_prod_ofFn (r : ℕ) (f : Fin r → ℝ) :
    (List.ofFn f).prod = ∏ i : Fin r, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      congr 1
      exact ih (fun i ↦ f i.succ)

private theorem p04_sum_ofFn (r : ℕ) (f : Fin r → ℝ) :
    (List.ofFn f).sum = ∑ i : Fin r, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      congr 1
      exact ih (fun i ↦ f i.succ)

private theorem p04_twiddle_sum (r : ℕ) (hr : 0 < r)
    (b : ℝ) :
    (∑ i : Fin r, if decide (i.val + 1 < r) then b else 0) =
      ((r : ℝ) - 1) * b := by
  cases r with
  | zero => omega
  | succ k =>
      rw [Fin.sum_univ_castSucc]
      have htail (i : Fin k) : i.castSucc.val + 1 < k + 1 := by
        exact Nat.succ_lt_succ i.isLt
      simp only [Fin.val_last, lt_irrefl, decide_false, Bool.false_eq_true,
        ite_false]
      simp_rw [show ∀ i : Fin k,
          (if decide (i.castSucc.val + 1 < k + 1) then b else 0) = b from by
            intro i; simp [htail i]]
      simp

private theorem p04_plan_list_scale {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) :
    p04ListScale (List.ofFn plan.stage) = Real.sqrt (n : ℝ) := by
  have hnon (i : Fin plan.stageCount) :
      0 ≤ ((plan.stage i).radix : ℝ) := Nat.cast_nonneg _
  calc
    p04ListScale (List.ofFn plan.stage) =
        ∏ i : Fin plan.stageCount,
          Real.sqrt ((plan.stage i).radix : ℝ) := by
      change (List.map p04StageScale (List.ofFn plan.stage)).prod = _
      rw [← List.ofFn_comp' plan.stage p04StageScale]
      rw [p04_prod_ofFn]
      rfl
    _ = Real.sqrt (∏ i : Fin plan.stageCount,
          ((plan.stage i).radix : ℝ)) := by
      rw [Real.sqrt_prod Finset.univ (fun i _ ↦ hnon i)]
    _ = Real.sqrt (n : ℝ) := by
      rw [← Nat.cast_prod, plan.order_factorization]

private theorem p04_plan_list_K {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    p04ListK (List.ofFn plan.stage) γ = p04K plan γ := by
  have htw : (∑ i : Fin plan.stageCount,
      if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
      ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) := by
    simpa only [plan.twiddle_pattern] using
      p04_twiddle_sum plan.stageCount plan.stageCount_pos (3 + 2 * γ)
  calc
    p04ListK (List.ofFn plan.stage) γ =
        ∑ i : Fin plan.stageCount, p04StageK (plan.stage i) γ := by
      change (List.map (fun stage ↦ p04StageK stage γ)
        (List.ofFn plan.stage)).sum = _
      rw [← List.ofFn_comp' plan.stage (fun stage ↦ p04StageK stage γ)]
      rw [p04_sum_ofFn]
    _ = (∑ i : Fin plan.stageCount,
          p04Alpha (plan.stage i).radix γ) +
        ∑ i : Fin plan.stageCount,
          (if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) := by
      simp [p04StageK, Finset.sum_add_distrib]
    _ = p04K plan γ := by rw [htw]; rfl

set_option maxHeartbeats 500000 in
private theorem p04_rounded_fft_norm_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i ↦
            p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
          (model.epsilon * Real.sqrt (n : ℝ) * p04K plan γ +
            C * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  have hscale : ∀ s ∈ List.ofFn plan.stage, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        p04StageScale s * p04ComplexNorm2 x := by
    intro s hs x
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' plan.stage s).mp hs
    exact plan.stage_norm_scaling i x
  obtain ⟨C, hC, h⟩ := p04RoundedFold_error
    (List.ofFn plan.stage) γ hγ hscale
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ hε x
  have hh := h model hmodelγ hε x
  have heq : (fun i ↦
      p04RoundedFftApply plan model x i - p04FourierTransform x i) =
      fun i ↦ p04RoundedFold model (List.ofFn plan.stage) x
          (plan.finalPermutation i) -
        p04ExactFold (List.ofFn plan.stage) x (plan.finalPermutation i) := by
    funext i
    have hf := congrFun (plan.exact_factorization x) i
    change p04ExactFold (List.ofFn plan.stage) x
      (plan.finalPermutation i) = p04FourierTransform x i at hf
    change p04RoundedFold model (List.ofFn plan.stage) x
      (plan.finalPermutation i) - p04FourierTransform x i = _
    rw [← hf]
  have hperm : p04ComplexNorm2 (fun i ↦
      p04RoundedFold model (List.ofFn plan.stage) x
          (plan.finalPermutation i) -
        p04ExactFold (List.ofFn plan.stage) x (plan.finalPermutation i)) =
      p04ComplexNorm2 (fun i ↦
        p04RoundedFold model (List.ofFn plan.stage) x i -
          p04ExactFold (List.ofFn plan.stage) x i) :=
    p04_complex_norm2_perm plan.finalPermutation
      (fun j ↦ p04RoundedFold model (List.ofFn plan.stage) x j -
        p04ExactFold (List.ofFn plan.stage) x j)
  rw [heq, hperm]
  simpa [p04_plan_list_scale plan, p04_plan_list_K plan] using hh

private theorem p04_fourier_norm_scale {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04FourierTransform x) =
      Real.sqrt (n : ℝ) * p04ComplexNorm2 x := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
  have h := plan.fourier_rms_scaling x
  dsimp [p04ComplexRms] at h
  field_simp at h ⊢
  nlinarith [h]

private theorem p04_rounded_fft_relative_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i ↦
            p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
          (model.epsilon * p04K plan γ + C * model.epsilon ^ 2) *
            p04ComplexNorm2 (p04FourierTransform x) := by
  obtain ⟨Cabs, hCabs, h⟩ := p04_rounded_fft_norm_error plan γ hγ
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (NeZero.pos n))
  refine ⟨Cabs / s, div_nonneg hCabs hs.le, ?_⟩
  intro model hmodelγ hε x
  have hh := h model hmodelγ hε x
  rw [p04_fourier_norm_scale plan x]
  have heq : (model.epsilon * p04K plan γ +
      Cabs / s * model.epsilon ^ 2) *
      (s * p04ComplexNorm2 x) =
      (model.epsilon * s * p04K plan γ +
        Cabs * model.epsilon ^ 2) * p04ComplexNorm2 x := by
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp [hs0]
  rw [heq]
  exact hh

private abbrev P04OtherIndex {m : ℕ} (axis : Fin m → P04FftAxis)
    (i : Fin m) :=
  (j : {j : Fin m // j ≠ i}) → ZMod (axis j).order

private noncomputable instance p04OtherIndexFintype {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    Fintype (P04OtherIndex axis i) := by
  letI (j : {j : Fin m // j ≠ i}) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  infer_instance

private noncomputable def p04MultiSplitEquiv {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    P04OtherIndex axis i × ZMod (axis i).order ≃ P04MultiIndex axis :=
  (Equiv.prodComm _ _).trans
    (Equiv.piSplitAt i (fun j ↦ ZMod (axis j).order)).symm

private theorem p04MultiSplitEquiv_at {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : P04OtherIndex axis i) (k : ZMod (axis i).order) :
    p04MultiSplitEquiv axis i (r, k) i = k := by
  simp [p04MultiSplitEquiv, Equiv.piSplitAt]

private theorem p04MultiSplitEquiv_update {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : P04OtherIndex axis i) (k j : ZMod (axis i).order) :
    Function.update (p04MultiSplitEquiv axis i (r, k)) i j =
      p04MultiSplitEquiv axis i (r, j) := by
  funext a
  by_cases ha : a = i
  · subst a
    simp [p04MultiSplitEquiv_at]
  · simp [Function.update, ha, p04MultiSplitEquiv,
      Equiv.piSplitAt]

private theorem p04_multi_norm2_sqrt_sum {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x =
      Real.sqrt (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
  simp [p04MultiNorm2, EuclideanSpace.norm_eq]

private theorem p04_multi_norm2_rows {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04MultiNorm2 x =
      Real.sqrt (∑ r : P04OtherIndex axis i,
        p04ComplexNorm2 (fun k : ZMod (axis i).order ↦
          x (p04MultiSplitEquiv axis i (r, k))) ^ 2) := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  rw [p04_multi_norm2_sqrt_sum]
  congr 1
  calc
    (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) =
        ∑ rk : P04OtherIndex axis i × ZMod (axis i).order,
          ‖x (p04MultiSplitEquiv axis i rk)‖ ^ 2 :=
      (Equiv.sum_comp (p04MultiSplitEquiv axis i) _).symm
    _ = ∑ r : P04OtherIndex axis i,
          ∑ k : ZMod (axis i).order,
            ‖x (p04MultiSplitEquiv axis i (r, k))‖ ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ r : P04OtherIndex axis i,
        p04ComplexNorm2 (fun k : ZMod (axis i).order ↦
          x (p04MultiSplitEquiv axis i (r, k))) ^ 2 := by
      congr 1
      funext r
      rw [p04_complex_norm2_sq]

private theorem p04AxisK_nonneg (axis : P04FftAxis)
    (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ p04AxisK axis γ := by
  letI : NeZero axis.order := ⟨Nat.ne_of_gt axis.order_pos⟩
  rw [p04AxisK, ← p04_plan_list_K]
  exact p04ListK_nonneg _ γ hγ

private theorem p04_coordinate_relative_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (model : P04WilkinsonModel) (hmodelγ : model.gamma = γ)
        (hε : model.epsilon ≤ 1) (x : P04MultiArray axis),
        p04MultiNorm2 (fun index ↦
            p04RoundedCoordinateTransform axis i model x index -
              p04CoordinateTransform axis i x index) ≤
          (model.epsilon * p04AxisK (axis i) γ +
            C * model.epsilon ^ 2) *
              p04MultiNorm2 (p04CoordinateTransform axis i x) := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  obtain ⟨C, hC, h⟩ :=
    p04_rounded_fft_relative_error (axis i).plan γ hγ
  refine ⟨C, hC, ?_⟩
  intro model hmodelγ hε x
  let row : P04OtherIndex axis i → ZMod (axis i).order → ℂ :=
    fun r j ↦ x (p04MultiSplitEquiv axis i (r, j))
  let err : P04MultiArray axis := fun index ↦
    p04RoundedCoordinateTransform axis i model x index -
      p04CoordinateTransform axis i x index
  let exact : P04MultiArray axis := p04CoordinateTransform axis i x
  have hrowerr (r : P04OtherIndex axis i) (k : ZMod (axis i).order) :
      err (p04MultiSplitEquiv axis i (r, k)) =
        p04RoundedFftApply (axis i).plan model (row r) k -
          p04FourierTransform (row r) k := by
    simp [err, row, p04RoundedCoordinateTransform,
      p04CoordinateTransform, p04FourierTransform,
      p04MultiSplitEquiv_at, p04MultiSplitEquiv_update]
  have hrowexact (r : P04OtherIndex axis i) (k : ZMod (axis i).order) :
      exact (p04MultiSplitEquiv axis i (r, k)) =
        p04FourierTransform (row r) k := by
    simp [exact, row, p04CoordinateTransform, p04FourierTransform,
      p04MultiSplitEquiv_at, p04MultiSplitEquiv_update]
  let B : ℝ := model.epsilon * p04AxisK (axis i) γ +
    C * model.epsilon ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    exact add_nonneg
      (mul_nonneg model.epsilon_pos.le
        (p04AxisK_nonneg (axis i) γ hγ))
      (mul_nonneg hC (sq_nonneg _))
  have hrow (r : P04OtherIndex axis i) :
      p04ComplexNorm2 (fun k ↦
          err (p04MultiSplitEquiv axis i (r, k))) ≤
        B * p04ComplexNorm2 (fun k ↦
          exact (p04MultiSplitEquiv axis i (r, k))) := by
    simpa [hrowerr, hrowexact, B, p04AxisK] using
      h model hmodelγ hε (row r)
  have hroot := p04_sqrt_sum_sq_le_mul
    (fun r : P04OtherIndex axis i ↦
      p04ComplexNorm2 (fun k ↦
        err (p04MultiSplitEquiv axis i (r, k))))
    (fun r : P04OtherIndex axis i ↦
      p04ComplexNorm2 (fun k ↦
        exact (p04MultiSplitEquiv axis i (r, k))))
    B hB (fun _ ↦ Real.sqrt_nonneg _) (fun _ ↦ Real.sqrt_nonneg _) hrow
  rw [← p04_multi_norm2_rows axis i err,
    ← p04_multi_norm2_rows axis i exact] at hroot
  exact hroot

private theorem p04_multi_norm2_add_le {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 (fun index ↦ x index + y index) ≤
      p04MultiNorm2 x + p04MultiNorm2 y := by
  simp only [p04_multi_norm2_eq]
  exact norm_add_le
    (WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))
    (WithLp.toLp 2 y : EuclideanSpace ℂ (P04MultiIndex axis))

private theorem p04_multi_norm2_nonneg {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    0 ≤ p04MultiNorm2 x := norm_nonneg _

private theorem p04_multi_norm2_sub_triangle {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y z : P04MultiArray axis) :
    p04MultiNorm2 (fun index ↦ x index - z index) ≤
      p04MultiNorm2 (fun index ↦ x index - y index) +
        p04MultiNorm2 (fun index ↦ y index - z index) := by
  have hh := p04_multi_norm2_add_le
    (fun index ↦ x index - y index)
    (fun index ↦ y index - z index)
  have heq : (fun index ↦ (x index - y index) + (y index - z index)) =
      fun index ↦ x index - z index := by funext index; ring
  rwa [heq] at hh

private theorem p04_multi_norm2_le_add_sub {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 x ≤ p04MultiNorm2 y +
      p04MultiNorm2 (fun index ↦ x index - y index) := by
  have hh := p04_multi_norm2_add_le y (fun index ↦ x index - y index)
  have heq : (fun index ↦ y index + (x index - y index)) = x := by
    funext index; ring
  rw [heq] at hh
  linarith

private theorem p04_multi_chain_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (n : ℕ)
    (k c : Fin n → ℝ)
    (hk : ∀ i, 0 ≤ k i) (hc : ∀ i, 0 ≤ c i) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
        (z : Fin (n + 1) → P04MultiArray axis),
        (∀ i : Fin n,
          p04MultiNorm2 (fun index ↦ z i.castSucc index - z i.succ index) ≤
            (ε * k i + c i * ε ^ 2) * p04MultiNorm2 (z i.succ)) →
        p04MultiNorm2 (fun index ↦ z 0 index - z (Fin.last n) index) ≤
          (ε * (∑ i : Fin n, k i) + D * ε ^ 2) *
            p04MultiNorm2 (z (Fin.last n)) := by
  induction n with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro ε hε0 hε1 z hstep
      have heq : (fun index ↦ z 0 index - z (Fin.last 0) index) =
          (fun _ ↦ (0 : ℂ)) := by funext index; simp
      rw [heq]
      simp [p04_multi_norm2_sqrt_sum]
  | succ n ih =>
      let kt : Fin n → ℝ := fun i ↦ k i.succ
      let ct : Fin n → ℝ := fun i ↦ c i.succ
      have hkt : ∀ i, 0 ≤ kt i := fun i ↦ hk i.succ
      have hct : ∀ i, 0 ≤ ct i := fun i ↦ hc i.succ
      obtain ⟨Dt, hDt, ht⟩ := ih kt ct hkt hct
      let S : ℝ := ∑ i : Fin n, kt i
      let D : ℝ := Dt + c 0 + (S + Dt) * (k 0 + c 0)
      have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ ↦ hkt i)
      have hD : 0 ≤ D := by
        dsimp [D]
        exact add_nonneg (add_nonneg hDt (hc 0))
          (mul_nonneg (add_nonneg hS hDt)
            (add_nonneg (hk 0) (hc 0)))
      refine ⟨D, hD, ?_⟩
      intro ε hε0 hε1 z hstep
      let zt : Fin (n + 1) → P04MultiArray axis := fun i ↦ z i.succ
      have hstep_t : ∀ i : Fin n,
          p04MultiNorm2 (fun index ↦
              zt i.castSucc index - zt i.succ index) ≤
            (ε * kt i + ct i * ε ^ 2) *
              p04MultiNorm2 (zt i.succ) := by
        intro i
        simpa only [zt, kt, ct] using
          hstep i.succ
      have htail := ht ε hε0 hε1 zt hstep_t
      have htail' : p04MultiNorm2 (fun index ↦
          z 1 index - z (Fin.last (n + 1)) index) ≤
          (ε * S + Dt * ε ^ 2) *
            p04MultiNorm2 (z (Fin.last (n + 1))) := by
        simpa [zt, S, kt] using htail
      have hhead := hstep (0 : Fin (n + 1))
      have hhead' : p04MultiNorm2 (fun index ↦
          z 0 index - z 1 index) ≤
          (ε * k 0 + c 0 * ε ^ 2) * p04MultiNorm2 (z 1) := by
        simpa using hhead
      have hnorm : p04MultiNorm2 (z 1) ≤
          (1 + ε * S + Dt * ε ^ 2) *
            p04MultiNorm2 (z (Fin.last (n + 1))) := by
        have hh := p04_multi_norm2_le_add_sub (z 1)
          (z (Fin.last (n + 1)))
        nlinarith [htail']
      have hcoeff0 : 0 ≤ ε * k 0 + c 0 * ε ^ 2 := by
        exact add_nonneg (mul_nonneg hε0 (hk 0))
          (mul_nonneg (hc 0) (sq_nonneg _))
      have hmul := mul_le_mul_of_nonneg_left hnorm hcoeff0
      have htri := p04_multi_norm2_sub_triangle (z 0) (z 1)
        (z (Fin.last (n + 1)))
      have hbound : p04MultiNorm2 (fun index ↦
          z 0 index - z (Fin.last (n + 1)) index) ≤
          ((ε * k 0 + c 0 * ε ^ 2) *
              (1 + ε * S + Dt * ε ^ 2) +
            (ε * S + Dt * ε ^ 2)) *
              p04MultiNorm2 (z (Fin.last (n + 1))) := by
        nlinarith [htri, hhead', htail', hmul]
      have hscalar := p04_chain_compose_scalar ε 1 1 (k 0) S
        (c 0) Dt hε0 hε1 (by norm_num) (by norm_num)
        (hk 0) hS (hc 0) hDt
      have hcoeff : (ε * k 0 + c 0 * ε ^ 2) *
          (1 + ε * S + Dt * ε ^ 2) + (ε * S + Dt * ε ^ 2) ≤
          ε * (∑ i : Fin (n + 1), k i) + D * ε ^ 2 := by
        have hsum : (∑ i : Fin (n + 1), k i) = k 0 + S := by
          simpa [S, kt] using (Fin.sum_univ_succ k)
        rw [hsum]
        dsimp [D]
        nlinarith [hscalar]
      have hm := mul_le_mul_of_nonneg_right hcoeff
        (p04_multi_norm2_nonneg (z (Fin.last (n + 1))))
      exact hbound.trans hm

private theorem p04CoordinateTransform_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) :
    p04CoordinateTransform axis i (fun index ↦ x index - y index) =
      fun index ↦ p04CoordinateTransform axis i x index -
        p04CoordinateTransform axis i y index := by
  funext index
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp only [p04CoordinateTransform]
  rw [← Finset.sum_sub_distrib]
  congr 1
  funext j
  ring

private theorem p04CoordinateTransformNat_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : ℕ)
    (x y : P04MultiArray axis) :
    p04CoordinateTransformNat axis i (fun index ↦ x index - y index) =
      fun index ↦ p04CoordinateTransformNat axis i x index -
        p04CoordinateTransformNat axis i y index := by
  by_cases hi : i < m
  · simp [p04CoordinateTransformNat, hi, p04CoordinateTransform_sub]
  · simp [p04CoordinateTransformNat, hi]

private theorem p04Prefix_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ)
    (x y : P04MultiArray axis) :
    p04ApplyCoordinatePrefix axis k (fun index ↦ x index - y index) =
      fun index ↦ p04ApplyCoordinatePrefix axis k x index -
        p04ApplyCoordinatePrefix axis k y index := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      simp only [p04ApplyCoordinatePrefix]
      rw [p04CoordinateTransformNat_sub]
      exact ih _ _

private theorem p04MultiCardinality_pos {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    0 < p04MultiCardinality axis := by
  unfold p04MultiCardinality
  exact Finset.prod_pos (fun i _ ↦ (axis i).order_pos)

private theorem p04Prefix_norm_scaling {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (k : ℕ) (hk : k ≤ m) (x : P04MultiArray plan.axis) :
    p04MultiNorm2 (p04ApplyCoordinatePrefix plan.axis k x) =
      Real.sqrt (p04PrefixOrderProduct plan.axis k hk : ℝ) *
        p04MultiNorm2 x := by
  have hcard : 0 < (p04MultiCardinality plan.axis : ℝ) := by
    exact_mod_cast p04MultiCardinality_pos plan.axis
  have hden : Real.sqrt (p04MultiCardinality plan.axis : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  have h := plan.prefix_rms_scaling k hk x
  dsimp [p04MultiRms] at h
  field_simp [hden] at h
  nlinarith [h]

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
  classical
  let coeffProof (i : Fin m) :=
    p04_coordinate_relative_error plan.axis i γ family.gamma_nonneg
  let coeff : Fin m → ℝ := fun i ↦ Classical.choose (coeffProof i)
  have hcoeff_nonneg (i : Fin m) : 0 ≤ coeff i :=
    (Classical.choose_spec (coeffProof i)).1
  have hlocal (i : Fin m) (model : P04WilkinsonModel)
      (hmodelγ : model.gamma = γ) (hε : model.epsilon ≤ 1)
      (x : P04MultiArray plan.axis) :
      p04MultiNorm2 (fun index ↦
          p04RoundedCoordinateTransform plan.axis i model x index -
            p04CoordinateTransform plan.axis i x index) ≤
        (model.epsilon * p04AxisK (plan.axis i) γ +
          coeff i * model.epsilon ^ 2) *
            p04MultiNorm2 (p04CoordinateTransform plan.axis i x) :=
    (Classical.choose_spec (coeffProof i)).2 model hmodelγ hε x
  obtain ⟨D, hD, hchain⟩ := p04_multi_chain_error plan.axis m
    (fun i ↦ p04AxisK (plan.axis i) γ) coeff
    (fun i ↦ p04AxisK_nonneg (plan.axis i) γ family.gamma_nonneg)
    hcoeff_nonneg
  refine ⟨D, hD, 1, by norm_num, ?_⟩
  intro ε hεle
  let run := family.run ε
  let z : Fin (m + 1) → P04MultiArray plan.axis :=
    fun j ↦ p04ApplyCoordinatePrefix plan.axis j.val
      (run.computedState j)
  have hstep (i : Fin m) :
      p04MultiNorm2 (fun index ↦
          z i.castSucc index - z i.succ index) ≤
        (ε.1 * p04AxisK (plan.axis i) γ +
          coeff i * ε.1 ^ 2) * p04MultiNorm2 (z i.succ) := by
    let x : P04MultiArray plan.axis := run.computedState i.succ
    let e : P04MultiArray plan.axis := fun index ↦
      p04RoundedCoordinateTransform plan.axis i (family.model ε) x index -
        p04CoordinateTransform plan.axis i x index
    let y : P04MultiArray plan.axis :=
      p04CoordinateTransform plan.axis i x
    have hstepvec : (fun index ↦ z i.castSucc index - z i.succ index) =
        p04ApplyCoordinatePrefix plan.axis i.val e := by
      have hs := run.stage_step i
      change run.computedState i.castSucc =
        p04RoundedCoordinateTransform plan.axis i (family.model ε) x at hs
      have hnat : p04CoordinateTransformNat plan.axis i.val x = y := by
        simp [p04CoordinateTransformNat, i.isLt, y]
      have hpref := p04Prefix_sub plan.axis i.val
        (p04RoundedCoordinateTransform plan.axis i (family.model ε) x) y
      change p04ApplyCoordinatePrefix plan.axis i.val e = _ at hpref
      rw [hpref]
      funext index
      simp only [z, Fin.val_castSucc, Fin.val_succ,
        p04ApplyCoordinatePrefix]
      rw [hs, hnat]
    have hsucc : z i.succ = p04ApplyCoordinatePrefix plan.axis i.val y := by
      change p04ApplyCoordinatePrefix plan.axis (i.val + 1) x = _
      simp [p04ApplyCoordinatePrefix,
        p04CoordinateTransformNat, i.isLt, y]
    have hloc := hlocal i (family.model ε) (family.model_gamma ε)
      (by simpa [family.model_epsilon ε] using hεle) x
    have heps : (family.model ε).epsilon = ε.1 := family.model_epsilon ε
    rw [heps] at hloc
    have hprefe := p04Prefix_norm_scaling plan i.val i.isLt.le e
    have hprefy := p04Prefix_norm_scaling plan i.val i.isLt.le y
    have hsqrt : 0 ≤ Real.sqrt
        (p04PrefixOrderProduct plan.axis i.val i.isLt.le : ℝ) :=
      Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hloc hsqrt
    rw [hstepvec, hsucc, hprefe, hprefy]
    nlinarith [hmul]
  have hnorm := hchain ε.1 ε.2.le hεle z hstep
  have hz0 : z 0 = p04MultiComputedOutput run := by
    rfl
  have hzm : z (Fin.last m) = p04FamilyMultiExactOutput family := by
    change p04ApplyCoordinatePrefix plan.axis m
      (run.computedState (Fin.last m)) =
        p04ApplyCoordinatePrefix plan.axis m family.input
    rw [run.computed_input, family.run_input ε]
  have hErr : (fun index ↦ z 0 index - z (Fin.last m) index) =
      p04FamilyMultiFftRoundoffError family ε := by
    funext index
    simp [run, hz0, hzm, p04FamilyMultiFftRoundoffError,
      p04MultiVecSub]
  rw [hErr, hzm] at hnorm
  have hcard : 0 < Real.sqrt (p04MultiCardinality plan.axis : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast p04MultiCardinality_pos plan.axis
  have hrms : p04MultiRms (p04FamilyMultiFftRoundoffError family ε) ≤
      (ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
        D * ε.1 ^ 2) *
        p04MultiRms (p04FamilyMultiExactOutput family) := by
    unfold p04MultiRms
    calc
      p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) /
          Real.sqrt (p04MultiCardinality plan.axis : ℝ) ≤
          ((ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
            D * ε.1 ^ 2) *
            p04MultiNorm2 (p04FamilyMultiExactOutput family)) /
              Real.sqrt (p04MultiCardinality plan.axis : ℝ) :=
        div_le_div_of_nonneg_right hnorm hcard.le
      _ = (ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
            D * ε.1 ^ 2) *
          (p04MultiNorm2 (p04FamilyMultiExactOutput family) /
            Real.sqrt (p04MultiCardinality plan.axis : ℝ)) := by ring
  exact (div_le_iff₀ hexactOutput).2 hrms

end VSCLReuse

import VSCLReuse.P04.Definitions

namespace VSCLReuse

private theorem p04_complex_diag_norm_le
    (z : ℂ) (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(⟨a * z.re, b * z.im⟩ : ℂ)‖ ≤ ‖z‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  have ha' : a ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (by simpa using ha : |a| ≤ |(1 : ℝ)|))
  have hb' : b ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (by simpa using hb : |b| ≤ |(1 : ℝ)|))
  have hre : 0 ≤ z.re ^ 2 := sq_nonneg _
  have him : 0 ≤ z.im ^ 2 := sq_nonneg _
  have h1 : (a * z.re) ^ 2 ≤ z.re ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right ha' hre]
  have h2 : (b * z.im) ^ 2 ≤ z.im ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hb' him]
  simpa only [Complex.normSq_mk, Complex.normSq_apply, ← sq] using add_le_add h1 h2

private theorem p04_rounded_complex_add_error_bound
    (model : P04WilkinsonModel) (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  rcases model.add_model x.re y.re with ⟨ar, br, har, hbr, hre⟩
  rcases model.add_model x.im y.im with ⟨ai, bi, hai, hbi, him⟩
  let dx : ℂ := ⟨ar * x.re, ai * x.im⟩
  let dy : ℂ := ⟨br * y.re, bi * y.im⟩
  have herror : p04RoundedComplexAdd model x y - (x + y) =
      (model.epsilon : ℂ) * (dx + dy) := by
    apply Complex.ext <;> simp [p04RoundedComplexAdd, dx, dy, hre, him] <;> ring
  rw [herror, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  exact mul_le_mul_of_nonneg_left
    ((norm_add_le dx dy).trans (add_le_add
      (p04_complex_diag_norm_le x ar ai har hai)
      (p04_complex_diag_norm_le y br bi hbr hbi)))
    model.epsilon_pos.le

private theorem p04_complex_l1_le_three_halves_norm (z : ℂ) :
    |z.re| + |z.im| ≤ (3 / 2 : ℝ) * ‖z‖ := by
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  have hr : 0 ≤ |z.re| := abs_nonneg _
  have hi : 0 ≤ |z.im| := abs_nonneg _
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply, sq] using Complex.sq_norm z
  have hrr : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
  have hii : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
  nlinarith [sq_nonneg (|z.re| - |z.im|)]

private noncomputable def p04_rounded_real_complex_scale
    (model : P04WilkinsonModel) (a : ℝ) (z : ℂ) : ℂ :=
  ⟨model.flMul a z.re, model.flMul a z.im⟩

private theorem p04_rounded_real_complex_scale_error_bound
    (model : P04WilkinsonModel) (a : ℝ) (z : ℂ) :
    ‖p04_rounded_real_complex_scale model a z - (a : ℂ) * z‖ ≤
      model.epsilon * |a| * ‖z‖ := by
  rcases model.mul_model a z.re with ⟨tr, htr, hr⟩
  rcases model.mul_model a z.im with ⟨ti, hti, hi⟩
  have heq : p04_rounded_real_complex_scale model a z - (a : ℂ) * z =
      (model.epsilon : ℂ) * (a : ℂ) * (⟨tr * z.re, ti * z.im⟩ : ℂ) := by
    apply Complex.ext <;>
      simp [p04_rounded_real_complex_scale, hr, hi, Complex.mul_re, Complex.mul_im] <;>
      ring
  rw [heq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos model.epsilon_pos]
  exact mul_le_mul_of_nonneg_left
    (p04_complex_diag_norm_le z tr ti htr hti)
    (mul_nonneg model.epsilon_pos.le (abs_nonneg a))

private theorem p04_rounded_real_complex_scale_norm_bound
    (model : P04WilkinsonModel) (a : ℝ) (z : ℂ) :
    ‖p04_rounded_real_complex_scale model a z‖ ≤
      (1 + model.epsilon) * |a| * ‖z‖ := by
  calc
    ‖p04_rounded_real_complex_scale model a z‖ =
        ‖(p04_rounded_real_complex_scale model a z - (a : ℂ) * z) +
          (a : ℂ) * z‖ := by rw [sub_add_cancel]
    _ ≤ ‖p04_rounded_real_complex_scale model a z - (a : ℂ) * z‖ +
        ‖(a : ℂ) * z‖ := norm_add_le _ _
    _ ≤ model.epsilon * |a| * ‖z‖ + |a| * ‖z‖ := by
      gcongr
      · exact p04_rounded_real_complex_scale_error_bound model a z
      · simp
    _ = (1 + model.epsilon) * |a| * ‖z‖ := by ring

private theorem p04_rounded_complex_mul_error_bound
    (model : P04WilkinsonModel) (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (|x.re| + |x.im|) * ‖y‖ := by
  let u := p04_rounded_real_complex_scale model x.re y
  let v := Complex.I * p04_rounded_real_complex_scale model x.im y
  have hrounded : p04RoundedComplexMul model x y =
      p04RoundedComplexAdd model u v := by
    apply Complex.ext <;>
      simp [p04RoundedComplexMul, p04RoundedComplexAdd, u, v,
        p04_rounded_real_complex_scale, Complex.mul_re, Complex.mul_im]
  have hexact : x * y = (x.re : ℂ) * y + Complex.I * (x.im : ℂ) * y := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hvnorm : ‖v‖ = ‖p04_rounded_real_complex_scale model x.im y‖ := by
    simp [v]
  have hinput : ‖u‖ + ‖v‖ ≤
      (1 + model.epsilon) * (|x.re| + |x.im|) * ‖y‖ := by
    rw [hvnorm]
    have h1 := p04_rounded_real_complex_scale_norm_bound model x.re y
    have h2 := p04_rounded_real_complex_scale_norm_bound model x.im y
    dsimp [u]
    linarith [h1, h2]
  have hpre : ‖u + v - x * y‖ ≤
      model.epsilon * (|x.re| + |x.im|) * ‖y‖ := by
    rw [hexact]
    have heq : u + v - ((x.re : ℂ) * y + Complex.I * (x.im : ℂ) * y) =
        (u - (x.re : ℂ) * y) +
          Complex.I * (p04_rounded_real_complex_scale model x.im y - (x.im : ℂ) * y) := by
      dsimp [v]
      ring
    rw [heq]
    calc
      _ ≤ ‖u - (x.re : ℂ) * y‖ +
          ‖Complex.I * (p04_rounded_real_complex_scale model x.im y -
            (x.im : ℂ) * y)‖ := norm_add_le _ _
      _ ≤ model.epsilon * |x.re| * ‖y‖ +
          model.epsilon * |x.im| * ‖y‖ := by
        simp only [norm_mul, Complex.norm_I, one_mul]
        exact add_le_add
          (p04_rounded_real_complex_scale_error_bound model x.re y)
          (p04_rounded_real_complex_scale_error_bound model x.im y)
      _ = _ := by ring
  have hcalc : p04RoundedComplexMul model x y - x * y =
      (p04RoundedComplexAdd model u v - (u + v)) + (u + v - x * y) := by
    rw [hrounded]
    ring
  rw [hcalc]
  calc
    _ ≤ ‖p04RoundedComplexAdd model u v - (u + v)‖ +
        ‖u + v - x * y‖ := norm_add_le _ _
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
        model.epsilon * (|x.re| + |x.im|) * ‖y‖ := by
      exact add_le_add (p04_rounded_complex_add_error_bound model u v) hpre
    _ ≤ model.epsilon * ((1 + model.epsilon) *
        (|x.re| + |x.im|) * ‖y‖) +
        model.epsilon * (|x.re| + |x.im|) * ‖y‖ := by
      gcongr
      exact model.epsilon_pos.le
    _ = _ := by ring

private theorem p04_rounded_complex_mul_error_bound_alt
    (model : P04WilkinsonModel) (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (3 + (3 / 2 : ℝ) * model.epsilon) * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ model.epsilon * (2 + model.epsilon) *
        (|x.re| + |x.im|) * ‖y‖ :=
      p04_rounded_complex_mul_error_bound model x y
    _ ≤ model.epsilon * (2 + model.epsilon) *
        ((3 / 2 : ℝ) * ‖x‖) * ‖y‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (p04_complex_l1_le_three_halves_norm x)
          (by have hε := model.epsilon_pos.le; positivity)) (norm_nonneg y)
    _ = _ := by ring

private theorem p04_root_exact_formula {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.stdAddChar j =
      (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ) := by
  have he : ZMod.stdAddChar j =
      Complex.exp ((p04RootAngle j : ℂ) * Complex.I) := by
    rw [p04StdAddChar_positive_exp]
    congr 1
    simp only [p04RootAngle, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    norm_num
    ring
  rw [he]
  apply Complex.ext
  · exact Complex.exp_ofReal_mul_I_re _
  · exact Complex.exp_ofReal_mul_I_im _

private theorem p04_root_exact_norm {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  have he : ZMod.stdAddChar j =
      Complex.exp ((p04RootAngle j : ℂ) * Complex.I) := by
    rw [p04StdAddChar_positive_exp]
    congr 1
    simp only [p04RootAngle, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    norm_num
    ring
  rw [he]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem p04_rounded_root_error_bound {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  let angle := p04RootAngle j
  rcases model.cos_model angle with ⟨tc, htc, hc⟩
  rcases model.sin_model angle with ⟨ts, hts, hs⟩
  have htc2 : tc ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (by simpa using htc : |tc| ≤ |(1 : ℝ)|))
  have hts2 : ts ^ 2 ≤ 1 := by
    simpa using (sq_le_sq.mpr (by simpa using hts : |ts| ≤ |(1 : ℝ)|))
  have htheta : ‖(⟨tc, ts⟩ : ℂ)‖ ≤ 2 := by
    have hn := norm_nonneg (⟨tc, ts⟩ : ℂ)
    have hsq : ‖(⟨tc, ts⟩ : ℂ)‖ ^ 2 = tc ^ 2 + ts ^ 2 := by
      simpa [Complex.normSq_mk, sq] using Complex.sq_norm (⟨tc, ts⟩ : ℂ)
    nlinarith
  have heq : p04RoundedRoot model j - ZMod.stdAddChar j =
      ((model.gamma * model.epsilon : ℝ) : ℂ) * (⟨tc, ts⟩ : ℂ) := by
    rw [p04_root_exact_formula]
    apply Complex.ext <;> simp [p04RoundedRoot, angle, hc, hs, Complex.mul_re,
      Complex.mul_im] <;> ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg model.gamma_nonneg model.epsilon_pos.le)]
  nlinarith [mul_le_mul_of_nonneg_left htheta
    (mul_nonneg model.gamma_nonneg model.epsilon_pos.le)]

private theorem p04_rounded_root_norm_bound {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  calc
    ‖p04RoundedRoot model j‖ =
        ‖(p04RoundedRoot model j - ZMod.stdAddChar j) +
          ZMod.stdAddChar j‖ := by rw [sub_add_cancel]
    _ ≤ ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ +
        ‖ZMod.stdAddChar j‖ := norm_add_le _ _
    _ ≤ 2 * model.gamma * model.epsilon + 1 := by
      rw [p04_root_exact_norm]
      linarith [p04_rounded_root_error_bound model j]
    _ = _ := by ring

private theorem p04_rounded_twiddle_error_bound {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      (model.epsilon * (3 + 2 * model.gamma) +
        model.epsilon ^ 2 * (2 + 9 * model.gamma)) * ‖x‖ := by
  let r := p04RoundedRoot model j
  let e := ZMod.stdAddChar j
  have hsplit : p04RoundedComplexMul model r x - e * x =
      (p04RoundedComplexMul model r x - r * x) + (r - e) * x := by ring
  rw [hsplit]
  have hmul := p04_rounded_complex_mul_error_bound_alt model r x
  have hroot := p04_rounded_root_error_bound model j
  have hrnorm := p04_rounded_root_norm_bound model j
  calc
    _ ≤ ‖p04RoundedComplexMul model r x - r * x‖ + ‖(r - e) * x‖ :=
      norm_add_le _ _
    _ ≤ model.epsilon * (3 + (3 / 2 : ℝ) * model.epsilon) * ‖r‖ * ‖x‖ +
        (2 * model.gamma * model.epsilon) * ‖x‖ := by
      rw [norm_mul]
      exact add_le_add hmul
        (mul_le_mul_of_nonneg_right hroot (norm_nonneg x))
    _ ≤ (model.epsilon * (3 + (3 / 2 : ℝ) * model.epsilon) *
          (1 + 2 * model.gamma * model.epsilon) +
          2 * model.gamma * model.epsilon) * ‖x‖ := by
      have hc : 0 ≤ model.epsilon * (3 + (3 / 2 : ℝ) * model.epsilon) := by
        have hp := model.epsilon_pos.le
        positivity
      nlinarith [mul_le_mul_of_nonneg_left hrnorm hc, norm_nonneg x]
    _ ≤ (model.epsilon * (3 + 2 * model.gamma) +
          model.epsilon ^ 2 * (2 + 9 * model.gamma)) * ‖x‖ := by
      have hc : 0 ≤ model.epsilon ^ 2 * model.gamma :=
        mul_nonneg (sq_nonneg _) model.gamma_nonneg
      have hε0 := model.epsilon_pos.le
      have hγ := model.gamma_nonneg
      have hcoeff : model.epsilon * (3 + (3 / 2 : ℝ) * model.epsilon) *
          (1 + 2 * model.gamma * model.epsilon) +
          2 * model.gamma * model.epsilon ≤
          model.epsilon * (3 + 2 * model.gamma) +
          model.epsilon ^ 2 * (2 + 9 * model.gamma) := by
        nlinarith [mul_le_mul_of_nonneg_left hε hc]
      exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)

private noncomputable def p04_recursive_complex_sum
    (model : P04WilkinsonModel) : (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then v ⟨0, by omega⟩
      else p04RoundedComplexAdd model
        (p04_recursive_complex_sum model n (fun i => v i.castSucc))
        (v (Fin.last n))

private theorem p04_recursive_complex_sum_eq_components
    (model : P04WilkinsonModel) (n : ℕ) (v : Fin n → ℂ) :
    p04_recursive_complex_sum model n v =
      (⟨recursiveSum model.flAdd n (fun i => (v i).re),
        recursiveSum model.flAdd n (fun i => (v i).im)⟩ : ℂ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        rfl
      · simp only [p04_recursive_complex_sum, recursiveSum, dif_neg h]
        rw [ih]
        rfl

private theorem p04_rounded_complex_sum_eq_recursive {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    p04RoundedComplexSum model term =
      p04_recursive_complex_sum model q
        (fun i => term ((ZMod.finEquiv q).toEquiv i)) := by
  rw [p04_recursive_complex_sum_eq_components]
  rfl

private theorem p04_rounded_complex_add_norm_bound
    (model : P04WilkinsonModel) (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y‖ ≤
      (1 + model.epsilon) * (‖x‖ + ‖y‖) := by
  calc
    ‖p04RoundedComplexAdd model x y‖ =
        ‖(p04RoundedComplexAdd model x y - (x + y)) + (x + y)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖p04RoundedComplexAdd model x y - (x + y)‖ + ‖x + y‖ :=
      norm_add_le _ _
    _ ≤ model.epsilon * (‖x‖ + ‖y‖) + (‖x‖ + ‖y‖) := by
      exact add_le_add (p04_rounded_complex_add_error_bound model x y)
        (norm_add_le x y)
    _ = _ := by ring

private theorem p04_recursive_complex_sum_norm_bound
    (model : P04WilkinsonModel) (n : ℕ) (v : Fin n → ℂ) :
    ‖p04_recursive_complex_sum model n v‖ ≤
      (1 + model.epsilon) ^ n * ∑ i : Fin n, ‖v i‖ := by
  induction n with
  | zero => simp [p04_recursive_complex_sum]
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        simp [p04_recursive_complex_sum, Fin.sum_univ_one]
        nlinarith [model.epsilon_pos, norm_nonneg (v 0)]
      · let u : Fin n → ℂ := fun i => v i.castSucc
        let s : ℝ := ∑ i : Fin n, ‖u i‖
        let l : ℝ := ‖v (Fin.last n)‖
        have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have hl : 0 ≤ l := norm_nonneg _
        have he : 0 ≤ model.epsilon := model.epsilon_pos.le
        have hp : 1 ≤ (1 + model.epsilon) ^ n := by
          exact one_le_pow₀ (by linarith) 
        have hu := ih u
        have hround := p04_rounded_complex_add_norm_bound model
          (p04_recursive_complex_sum model n u) (v (Fin.last n))
        have hpow : 0 ≤ 1 + model.epsilon := by linarith
        simpa only [p04_recursive_complex_sum, dif_neg h,
          Fin.sum_univ_castSucc, pow_succ] using
          (calc
            ‖p04RoundedComplexAdd model (p04_recursive_complex_sum model n u)
                (v (Fin.last n))‖ ≤
                (1 + model.epsilon) *
                  (‖p04_recursive_complex_sum model n u‖ + l) := hround
            _ ≤ (1 + model.epsilon) * ((1 + model.epsilon) ^ n * s + l) := by
              exact mul_le_mul_of_nonneg_left (by dsimp [s]; linarith [hu]) hpow
            _ ≤ (1 + model.epsilon) ^ (n + 1) * (s + l) := by
              rw [pow_succ]
              have : l ≤ (1 + model.epsilon) ^ n * l := by nlinarith
              nlinarith)

private theorem p04_recursive_complex_sum_error_bound
    (model : P04WilkinsonModel) (n : ℕ) (v : Fin n → ℂ) :
    ‖p04_recursive_complex_sum model n v - ∑ i : Fin n, v i‖ ≤
      model.epsilon * (n : ℝ) * (1 + model.epsilon) ^ n *
        ∑ i : Fin n, ‖v i‖ := by
  induction n with
  | zero => simp [p04_recursive_complex_sum]
  | succ n ih =>
      by_cases h : n = 0
      · subst n
        simp [p04_recursive_complex_sum]
        have he : 0 ≤ model.epsilon := model.epsilon_pos.le
        positivity
      · let u : Fin n → ℂ := fun i => v i.castSucc
        let s : ℝ := ∑ i : Fin n, ‖u i‖
        let l : ℝ := ‖v (Fin.last n)‖
        let r := p04_recursive_complex_sum model n u
        have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have hl : 0 ≤ l := norm_nonneg _
        have he : 0 ≤ model.epsilon := model.epsilon_pos.le
        have hp : 1 ≤ (1 + model.epsilon) ^ n :=
          one_le_pow₀ (by linarith)
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        have hu := ih u
        have hr := p04_recursive_complex_sum_norm_bound model n u
        have hadd := p04_rounded_complex_add_error_bound model r (v (Fin.last n))
        have hsplit : p04RoundedComplexAdd model r (v (Fin.last n)) -
            ((∑ i : Fin n, u i) + v (Fin.last n)) =
            (p04RoundedComplexAdd model r (v (Fin.last n)) -
              (r + v (Fin.last n))) + (r - ∑ i : Fin n, u i) := by ring
        have hpow : (1 + model.epsilon) ^ n ≤
            (1 + model.epsilon) ^ (n + 1) := by
          rw [pow_succ]
          nlinarith [pow_nonneg (by linarith : 0 ≤ 1 + model.epsilon) n]
        simpa only [p04_recursive_complex_sum, dif_neg h,
          Fin.sum_univ_castSucc, Nat.cast_add, Nat.cast_one] using
          (calc
            ‖p04RoundedComplexAdd model r (v (Fin.last n)) -
                ((∑ i : Fin n, u i) + v (Fin.last n))‖ ≤
                ‖p04RoundedComplexAdd model r (v (Fin.last n)) -
                    (r + v (Fin.last n))‖ +
                  ‖r - ∑ i : Fin n, u i‖ := by
              rw [hsplit]
              exact norm_add_le _ _
            _ ≤ model.epsilon * (‖r‖ + l) +
                model.epsilon * (n : ℝ) * (1 + model.epsilon) ^ n * s := by
              exact add_le_add hadd hu
            _ ≤ model.epsilon * ((1 + model.epsilon) ^ n * s + l) +
                model.epsilon * (n : ℝ) * (1 + model.epsilon) ^ n * s := by
              nlinarith [mul_le_mul_of_nonneg_left hr he]
            _ ≤ model.epsilon * ((n : ℝ) + 1) *
                (1 + model.epsilon) ^ n * (s + l) := by
              have hh : l ≤ ((n : ℝ) + 1) * (1 + model.epsilon) ^ n * l := by
                nlinarith [mul_nonneg hn (sub_nonneg.mpr hp)]
              nlinarith [mul_le_mul_of_nonneg_left hh he]
            _ ≤ model.epsilon * ((n : ℝ) + 1) *
                (1 + model.epsilon) ^ (n + 1) * (s + l) := by
              have hc : 0 ≤ model.epsilon * ((n : ℝ) + 1) := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hpow hc,
                mul_nonneg hs hl])

private theorem p04_pow_one_add_linear_bound (n : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 + t) ^ n ≤ 1 + c * t := by
  induction n with
  | zero =>
      exact ⟨0, le_rfl, by intro t ht ht1; simp⟩
  | succ n ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      refine ⟨2 * c + 1, by positivity, ?_⟩
      intro t ht ht1
      have hp := hbound t ht ht1
      have hpos : 0 ≤ 1 + t := by linarith
      calc
        (1 + t) ^ (n + 1) = (1 + t) ^ n * (1 + t) := pow_succ _ _
        _ ≤ (1 + c * t) * (1 + t) :=
          mul_le_mul_of_nonneg_right hp hpos
        _ ≤ 1 + (2 * c + 1) * t := by
          have hct : 0 ≤ c * t := mul_nonneg hc ht
          nlinarith [mul_nonneg hct (sub_nonneg.mpr ht1)]

private theorem p04_rounded_complex_sum_error_bound {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q *
        ∑ j : ZMod q, ‖term j‖ := by
  rw [p04_rounded_complex_sum_eq_recursive]
  let e : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  simpa only [e, Equiv.sum_comp e term,
    Equiv.sum_comp e (fun j => ‖term j‖)] using
    p04_recursive_complex_sum_error_bound model q (fun i => term (e i))

private theorem p04_zmod_two_char_one :
    ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = -1
  rw [ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  norm_num
  ring

private theorem p04_radix_two_coefficient_exact
    (j : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change (if (0 : ZMod 2) = 0 then x else -x) =
        ZMod.stdAddChar (0 : ZMod 2) * x
    rw [if_pos rfl, AddChar.map_zero_eq_one]
    simp
  · have h : (1 : ZMod 2) ≠ 0 := by decide
    change (if (1 : ZMod 2) = 0 then x else -x) =
      ZMod.stdAddChar (1 : ZMod 2) * x
    rw [if_neg h, p04_zmod_two_char_one]
    simp

private theorem p04_zmod_four_char_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 4) = Complex.I
  rw [ZMod.stdAddChar_coe]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  norm_num
  ring

private theorem p04_zmod_four_char_two :
    ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  have h : (2 : ZMod 4) = 2 • (1 : ZMod 4) := by norm_num
  rw [h, AddChar.map_nsmul_eq_pow, p04_zmod_four_char_one,
    Complex.I_sq]

private theorem p04_zmod_four_char_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have h : (3 : ZMod 4) = 3 • (1 : ZMod 4) := by norm_num
  rw [h, AddChar.map_nsmul_eq_pow, p04_zmod_four_char_one]
  calc
    Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
    _ = -Complex.I := by rw [Complex.I_sq]; ring

private theorem p04_radix_four_coefficient_exact
    (j : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change (if (0 : ZMod 4) = 0 then x else
        if (0 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (0 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (0 : ZMod 4) * x
    rw [if_pos rfl, AddChar.map_zero_eq_one]
    simp
  · change (if (1 : ZMod 4) = 0 then x else
        if (1 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (1 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (1 : ZMod 4) * x
    have h : (1 : ZMod 4) ≠ 0 := by decide
    rw [if_neg h, if_pos rfl, p04_zmod_four_char_one]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  · change (if (2 : ZMod 4) = 0 then x else
        if (2 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (2 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (2 : ZMod 4) * x
    have h0 : (2 : ZMod 4) ≠ 0 := by decide
    have h1 : (2 : ZMod 4) ≠ 1 := by decide
    rw [if_neg h0, if_neg h1, if_pos rfl, p04_zmod_four_char_two]
    simp
  · change (if (3 : ZMod 4) = 0 then x else
        if (3 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (3 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (3 : ZMod 4) * x
    have h0 : (3 : ZMod 4) ≠ 0 := by decide
    have h1 : (3 : ZMod 4) ≠ 1 := by decide
    have h2 : (3 : ZMod 4) ≠ 2 := by decide
    rw [if_neg h0, if_neg h1, if_neg h2, p04_zmod_four_char_three]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p04_rounded_radix_two_block_formula
    (model : P04WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    p04RoundedRadixTwoBlock model x k =
      p04RoundedComplexAdd model
        (p04RadixTwoCoefficientApply (0 * k) (x 0))
        (p04RadixTwoCoefficientApply (1 * k) (x 1)) := by
  simp [p04RoundedRadixTwoBlock, p04_rounded_complex_sum_eq_recursive,
    p04_recursive_complex_sum]

private theorem p04_zmod_two_sum {M : Type*} [AddCommMonoid M]
    (f : ZMod 2 → M) :
    (∑ j : ZMod 2, f j) = f 0 + f 1 := by
  rw [← Equiv.sum_comp ((ZMod.finEquiv 2).toEquiv) f]
  simp [Fin.sum_univ_two]

private theorem p04_rounded_radix_two_block_error_bound
    (model : P04WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (‖x 0‖ + ‖x 1‖) := by
  rw [p04_rounded_radix_two_block_formula, p04_zmod_two_sum]
  simp only [p04_radix_two_coefficient_exact]
  have h := p04_rounded_complex_add_error_bound model
    (ZMod.stdAddChar (0 * k) * x 0)
    (ZMod.stdAddChar (1 * k) * x 1)
  simpa [norm_mul, p04_root_exact_norm] using h

private theorem p04_rounded_four_add_error_bound
    (model : P04WilkinsonModel) (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) - (a + b + c + d)‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  have hsplit : p04RoundedComplexAdd model u v - (a + b + c + d) =
      (p04RoundedComplexAdd model u v - (u + v)) +
        (u - (a + b)) + (v - (c + d)) := by ring
  change ‖p04RoundedComplexAdd model u v - (a + b + c + d)‖ ≤ _
  rw [hsplit]
  have hu := p04_rounded_complex_add_error_bound model a b
  have hv := p04_rounded_complex_add_error_bound model c d
  have hmain := p04_rounded_complex_add_error_bound model u v
  have hun := p04_rounded_complex_add_norm_bound model a b
  have hvn := p04_rounded_complex_add_norm_bound model c d
  calc
    _ ≤ ‖p04RoundedComplexAdd model u v - (u + v)‖ +
          ‖u - (a + b)‖ + ‖v - (c + d)‖ := by
      have h := norm_add_le
        ((p04RoundedComplexAdd model u v - (u + v)) + (u - (a + b)))
        (v - (c + d))
      linarith [norm_add_le
        (p04RoundedComplexAdd model u v - (u + v)) (u - (a + b))]
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by
      linarith [hmain, hu, hv]
    _ ≤ model.epsilon *
          ((1 + model.epsilon) * (‖a‖ + ‖b‖) +
            (1 + model.epsilon) * (‖c‖ + ‖d‖)) +
          model.epsilon * (‖a‖ + ‖b‖) +
          model.epsilon * (‖c‖ + ‖d‖) := by
      have he := model.epsilon_pos.le
      nlinarith [add_le_add hun hv,
        mul_le_mul_of_nonneg_left (add_le_add hun hv) he]
    _ = _ := by ring

private theorem p04_zmod_four_sum {M : Type*} [AddCommMonoid M]
    (f : ZMod 4 → M) :
    (∑ j : ZMod 4, f j) = f 0 + f 1 + f 2 + f 3 := by
  rw [← Equiv.sum_comp ((ZMod.finEquiv 4).toEquiv) f]
  simp [Fin.sum_univ_four]
  have h2 : ((ZMod.finEquiv 4).toEquiv (2 : Fin 4)) =
      (2 : ZMod 4) := by decide
  have h3 : ((ZMod.finEquiv 4).toEquiv (3 : Fin 4)) =
      (3 : ZMod 4) := by decide
  change (ZMod.finEquiv 4) (2 : Fin 4) = (2 : ZMod 4) at h2
  change (ZMod.finEquiv 4) (3 : Fin 4) = (3 : ZMod 4) at h3
  rw [h2, h3]

private theorem p04_rounded_radix_four_block_error_bound
    (model : P04WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (∑ j : ZMod 4, ‖x j‖) := by
  let a : ℂ := p04RadixFourCoefficientApply (0 * k) (x 0)
  let b : ℂ := p04RadixFourCoefficientApply (1 * k) (x 1)
  let c : ℂ := p04RadixFourCoefficientApply (2 * k) (x 2)
  let d : ℂ := p04RadixFourCoefficientApply (3 * k) (x 3)
  have hformula : p04RoundedRadixFourBlock model x k =
      p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) := by
    simp [p04RoundedRadixFourBlock, a, b, c, d]
    have h2 : ((ZMod.finEquiv 4).toEquiv (2 : Fin 4)) =
        (2 : ZMod 4) := by decide
    have h3 : ((ZMod.finEquiv 4).toEquiv (3 : Fin 4)) =
        (3 : ZMod 4) := by decide
    change (ZMod.finEquiv 4) (2 : Fin 4) = (2 : ZMod 4) at h2
    change (ZMod.finEquiv 4) (3 : Fin 4) = (3 : ZMod 4) at h3
    rw [h2, h3]
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      a + b + c + d := by
    rw [p04_zmod_four_sum]
    simp only [a, b, c, d, p04_radix_four_coefficient_exact]
  rw [hformula, hexact, p04_zmod_four_sum]
  have h := p04_rounded_four_add_error_bound model a b c d
  simpa [a, b, c, d, p04_radix_four_coefficient_exact,
    norm_mul, p04_root_exact_norm] using h

private theorem p04_rounded_generic_radix_block_error_bound
    {q : ℕ} [NeZero q] (model : P04WilkinsonModel)
    (x : ZMod q → ℂ) (k : ZMod q) (hε : model.epsilon ≤ 1) :
    ‖p04RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q *
          (1 + model.epsilon * (3 + 2 * model.gamma) +
            model.epsilon ^ 2 * (2 + 9 * model.gamma)) +
        model.epsilon * (3 + 2 * model.gamma) +
          model.epsilon ^ 2 * (2 + 9 * model.gamma)) *
        (∑ j : ZMod q, ‖x j‖) := by
  let f : ZMod q → ℂ := fun j =>
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let g : ZMod q → ℂ := fun j => ZMod.stdAddChar (j * k) * x j
  let a : ℝ := model.epsilon * (3 + 2 * model.gamma) +
    model.epsilon ^ 2 * (2 + 9 * model.gamma)
  let s : ℝ := ∑ j : ZMod q, ‖x j‖
  have ha : 0 ≤ a := by
    dsimp [a]
    have he := model.epsilon_pos.le
    have hg := model.gamma_nonneg
    positivity
  have hterm (j : ZMod q) : ‖f j - g j‖ ≤ a * ‖x j‖ :=
    p04_rounded_twiddle_error_bound model (j * k) (x j) hε
  have hgnorm (j : ZMod q) : ‖g j‖ = ‖x j‖ := by
    simp [g, norm_mul, p04_root_exact_norm]
  have hfnorm (j : ZMod q) : ‖f j‖ ≤ (1 + a) * ‖x j‖ := by
    calc
      ‖f j‖ = ‖(f j - g j) + g j‖ := by rw [sub_add_cancel]
      _ ≤ ‖f j - g j‖ + ‖g j‖ := norm_add_le _ _
      _ ≤ a * ‖x j‖ + ‖x j‖ := by
        rw [hgnorm]
        linarith [hterm j]
      _ = _ := by ring
  have hfsum : (∑ j : ZMod q, ‖f j‖) ≤ (1 + a) * s := by
    dsimp [s]
    calc
      _ ≤ ∑ j : ZMod q, (1 + a) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => hfnorm j
      _ = _ := by rw [← Finset.mul_sum]
  have herrorsum : ‖∑ j : ZMod q, (f j - g j)‖ ≤ a * s := by
    calc
      _ ≤ ∑ j : ZMod q, ‖f j - g j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, a * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = _ := by rw [← Finset.mul_sum]
  change ‖p04RoundedComplexSum model f - ∑ j : ZMod q, g j‖ ≤ _
  have hsplit : p04RoundedComplexSum model f - (∑ j : ZMod q, g j) =
      (p04RoundedComplexSum model f - ∑ j : ZMod q, f j) +
        ∑ j : ZMod q, (f j - g j) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖p04RoundedComplexSum model f - ∑ j : ZMod q, f j‖ +
        ‖∑ j : ZMod q, (f j - g j)‖ := norm_add_le _ _
    _ ≤ model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q *
          (∑ j : ZMod q, ‖f j‖) + a * s := by
      exact add_le_add (p04_rounded_complex_sum_error_bound model f) herrorsum
    _ ≤ model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q *
          ((1 + a) * s) + a * s := by
      have hc : 0 ≤ model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q := by
        have he := model.epsilon_pos.le
        positivity
      linarith [mul_le_mul_of_nonneg_left hfsum hc]
    _ = _ := by dsimp [a, s]; ring

private theorem p04_generic_radix_scalar_coefficient_bound
    (q : ℕ) (hq : 3 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        t * (q : ℝ) * (1 + t) ^ q *
            (1 + t * (3 + 2 * γ) + t ^ 2 * (2 + 9 * γ)) +
          t * (3 + 2 * γ) + t ^ 2 * (2 + 9 * γ) ≤
          t * (2 * ((q : ℝ) + γ)) + c * t ^ 2 := by
  obtain ⟨cp, hcp, hp⟩ := p04_pow_one_add_linear_bound q
  let A : ℝ := 3 + 2 * γ
  let B : ℝ := 2 + 9 * γ
  let D : ℝ := A + B
  let E : ℝ := cp + D + cp * D
  let c : ℝ := (q : ℝ) * E + B
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro t ht ht1
  have hpow := hp t ht ht1
  have hqreal : 3 ≤ (q : ℝ) := by exact_mod_cast hq
  have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
  have hX : 1 + t * A + t ^ 2 * B ≤ 1 + D * t := by
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_right ht2 hB]
  have hX0 : 0 ≤ 1 + t * A + t ^ 2 * B := by positivity
  have hprod : (1 + cp * t) * (1 + D * t) ≤ 1 + E * t := by
    dsimp [E]
    nlinarith [mul_nonneg (mul_nonneg hcp hD) (sub_nonneg.mpr ht1)]
  have hfirst : t * (q : ℝ) * (1 + t) ^ q *
      (1 + t * A + t ^ 2 * B) ≤
      t * (q : ℝ) * (1 + E * t) := by
    have htq : 0 ≤ t * (q : ℝ) := by positivity
    have hp0 : 0 ≤ (1 + t) ^ q := by positivity
    calc
      _ ≤ t * (q : ℝ) * (1 + cp * t) *
            (1 + t * A + t ^ 2 * B) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow htq) hX0
      _ ≤ t * (q : ℝ) * (1 + cp * t) * (1 + D * t) := by
        have hh : 0 ≤ t * (q : ℝ) * (1 + cp * t) := by positivity
        exact mul_le_mul_of_nonneg_left hX hh
      _ ≤ t * (q : ℝ) * (1 + E * t) := by
        nlinarith [mul_le_mul_of_nonneg_left hprod htq]
  dsimp [A, B, c, E, D] at *
  nlinarith [hfirst, mul_nonneg ht (sub_nonneg.mpr (by linarith : 0 ≤ (q : ℝ) - 3))]

private theorem p04_complex_norm2_sq_formula {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 x ^ 2 = ∑ j : ZMod n, ‖x j‖ ^ 2 := by
  simp only [p04ComplexNorm2, p04ComplexNorm2Sq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem p04_complex_l1_le_sqrt_card_norm2 {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    (∑ j : ZMod n, ‖x j‖) ≤
      Real.sqrt (n : ℝ) * p04ComplexNorm2 x := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (∑ j : ZMod n, ‖x j‖) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hr : 0 ≤ Real.sqrt (n : ℝ) * p04ComplexNorm2 x := by
    dsimp [p04ComplexNorm2]
    positivity
  have hsq : (∑ j : ZMod n, ‖x j‖) ^ 2 ≤
      (n : ℝ) * (∑ j : ZMod n, ‖x j‖ ^ 2) := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod n)))
      (f := fun j => ‖x j‖))
  have hn2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  have hx2 := p04_complex_norm2_sq_formula x
  nlinarith [sq_nonneg (Real.sqrt (n : ℝ) * p04ComplexNorm2 x)]

private theorem p04_complex_norm2_of_pointwise_l1_bound {n : ℕ} [NeZero n]
    (e x : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ k : ZMod n, ‖e k‖ ≤ c * (∑ j : ZMod n, ‖x j‖)) :
    p04ComplexNorm2 e ≤ (n : ℝ) * c * p04ComplexNorm2 x := by
  let s : ℝ := ∑ j : ZMod n, ‖x j‖
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcs : 0 ≤ c * s := mul_nonneg hc hs
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have he2 : p04ComplexNorm2 e ^ 2 ≤ (n : ℝ) * (c * s) ^ 2 := by
    rw [p04_complex_norm2_sq_formula]
    calc
      (∑ j : ZMod n, ‖e j‖ ^ 2) ≤
          ∑ j : ZMod n, (c * s) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_sq).2 (by
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hcs]
          exact hpoint j)
      _ = (n : ℝ) * (c * s) ^ 2 := by simp [ZMod.card]
  have hnorm : p04ComplexNorm2 e ≤ Real.sqrt (n : ℝ) * c * s := by
    have hp : 0 ≤ p04ComplexNorm2 e := Real.sqrt_nonneg _
    have hr : 0 ≤ Real.sqrt (n : ℝ) * c * s := by positivity
    have hroot : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
    nlinarith
  have hsbound := p04_complex_l1_le_sqrt_card_norm2 x
  have hroot : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  calc
    p04ComplexNorm2 e ≤ Real.sqrt (n : ℝ) * c * s := hnorm
    _ ≤ Real.sqrt (n : ℝ) * c *
          (Real.sqrt (n : ℝ) * p04ComplexNorm2 x) := by
      exact mul_le_mul_of_nonneg_left hsbound (by positivity)
    _ = (n : ℝ) * c * p04ComplexNorm2 x := by
      calc
        _ = Real.sqrt (n : ℝ) ^ 2 * c * p04ComplexNorm2 x := by ring
        _ = _ := by rw [hroot]

private theorem p04_block_norm_lift
    {n q b : ℕ} [NeZero n] [NeZero q]
    (reindex : Fin b × ZMod q ≃ ZMod n)
    (perm : ZMod n ≃ ZMod n)
    (x : ZMod n → ℂ) (err : Fin b → ZMod q → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ bi : Fin b,
      p04ComplexNorm2 (err bi) ≤
        C * p04ComplexNorm2 (fun j => x (perm (reindex (bi, j))))) :
    p04ComplexNorm2
        (fun i => err (reindex.symm i).1 (reindex.symm i).2) ≤
      C * p04ComplexNorm2 x := by
  let block : Fin b → ZMod q → ℂ :=
    fun bi j => x (perm (reindex (bi, j)))
  have hb2 (bi : Fin b) :
      (∑ j : ZMod q, ‖err bi j‖ ^ 2) ≤
        C ^ 2 * (∑ j : ZMod q, ‖block bi j‖ ^ 2) := by
    have hnorm := hb bi
    have herr0 : 0 ≤ p04ComplexNorm2 (err bi) := Real.sqrt_nonneg _
    have hblock0 : 0 ≤ p04ComplexNorm2 (block bi) := Real.sqrt_nonneg _
    have h1 := p04_complex_norm2_sq_formula (err bi)
    have h2 := p04_complex_norm2_sq_formula (block bi)
    change p04ComplexNorm2 (err bi) ≤ C * p04ComplexNorm2 (block bi) at hnorm
    nlinarith [sq_nonneg (C * p04ComplexNorm2 (block bi))]
  have hsum :
      (∑ bi : Fin b, ∑ j : ZMod q, ‖err bi j‖ ^ 2) ≤
        C ^ 2 * (∑ bi : Fin b, ∑ j : ZMod q, ‖block bi j‖ ^ 2) := by
    calc
      _ ≤ ∑ bi : Fin b,
          C ^ 2 * (∑ j : ZMod q, ‖block bi j‖ ^ 2) :=
        Finset.sum_le_sum fun bi _ => hb2 bi
      _ = _ := by rw [← Finset.mul_sum]
  have herrsum :
      (∑ i : ZMod n,
        ‖err (reindex.symm i).1 (reindex.symm i).2‖ ^ 2) =
        ∑ bi : Fin b, ∑ j : ZMod q, ‖err bi j‖ ^ 2 := by
    rw [← Equiv.sum_comp reindex (fun i : ZMod n =>
      ‖err (reindex.symm i).1 (reindex.symm i).2‖ ^ 2)]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have hblocksum :
      (∑ bi : Fin b, ∑ j : ZMod q, ‖block bi j‖ ^ 2) =
        ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    calc
      _ = ∑ p : Fin b × ZMod q, ‖x (perm (reindex p))‖ ^ 2 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ i : ZMod n, ‖x (perm i)‖ ^ 2 :=
        Equiv.sum_comp reindex (fun i : ZMod n => ‖x (perm i)‖ ^ 2)
      _ = _ := Equiv.sum_comp perm (fun i : ZMod n => ‖x i‖ ^ 2)
  have he2 :
      p04ComplexNorm2 (fun i => err (reindex.symm i).1 (reindex.symm i).2) ^ 2 ≤
        C ^ 2 * p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq_formula, p04_complex_norm2_sq_formula,
      herrsum]
    calc
      _ ≤ C ^ 2 * (∑ bi : Fin b, ∑ j : ZMod q, ‖block bi j‖ ^ 2) := hsum
      _ = _ := by rw [hblocksum]
  have he0 : 0 ≤ p04ComplexNorm2
      (fun i => err (reindex.symm i).1 (reindex.symm i).2) := Real.sqrt_nonneg _
  have hx0 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hC hx0]

private noncomputable def p04_rounded_radix_block {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  if h2 : q = 2 then
    p04RoundedRadixTwoBlock model (fun j : ZMod 2 => x (h2.symm ▸ j)) (h2 ▸ k)
  else if h4 : q = 4 then
    p04RoundedRadixFourBlock model (fun j : ZMod 4 => x (h4.symm ▸ j)) (h4 ▸ k)
  else p04RoundedGenericRadixBlock model x k

private theorem p04_rounded_radix_block_pointwise_bound
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 →
        ∀ (x : ZMod q → ℂ) (k : ZMod q),
          ‖p04_rounded_radix_block model x k -
              ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
            (model.epsilon *
                (if q = 2 then 1 else if q = 4 then 2 else
                  2 * ((q : ℝ) + γ)) + c * model.epsilon ^ 2) *
              (∑ j : ZMod q, ‖x j‖) := by
  by_cases h2 : q = 2
  · subst q
    refine ⟨0, le_rfl, ?_⟩
    intro model hmodel hε x k
    simpa [p04_rounded_radix_block, p04_zmod_two_sum] using
      p04_rounded_radix_two_block_error_bound model x k
  by_cases h4 : q = 4
  · subst q
    refine ⟨1, by norm_num, ?_⟩
    intro model hmodel hε x k
    simp only [p04_rounded_radix_block,
      dif_neg (by decide : (4 : ℕ) ≠ 2), dif_pos rfl,
      if_neg (by decide : (4 : ℕ) ≠ 2), if_pos rfl, if_true, one_mul]
    change ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon * 2 + model.epsilon ^ 2) *
        (∑ j : ZMod 4, ‖x j‖)
    convert p04_rounded_radix_four_block_error_bound model x k using 1 <;> ring
  have hq3 : 3 ≤ q := by omega
  obtain ⟨c, hc, hscalar⟩ :=
    p04_generic_radix_scalar_coefficient_bound q hq3 γ hγ
  refine ⟨c, hc, ?_⟩
  intro model hmodel hε x k
  have hfirst := p04_rounded_generic_radix_block_error_bound model x k hε
  have hcoeff := hscalar model.epsilon model.epsilon_pos.le hε
  simp only [hmodel] at hfirst
  have hs : 0 ≤ (∑ j : ZMod q, ‖x j‖) :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [p04_rounded_radix_block, dif_neg h2, dif_neg h4,
    if_neg h2, if_neg h4]
  calc
    _ ≤ (model.epsilon * (q : ℝ) * (1 + model.epsilon) ^ q *
            (1 + model.epsilon * (3 + 2 * γ) +
              model.epsilon ^ 2 * (2 + 9 * γ)) +
          model.epsilon * (3 + 2 * γ) +
            model.epsilon ^ 2 * (2 + 9 * γ)) *
          (∑ j : ZMod q, ‖x j‖) := hfirst
    _ ≤ (model.epsilon * (2 * ((q : ℝ) + γ)) + c * model.epsilon ^ 2) *
          (∑ j : ZMod q, ‖x j‖) :=
      mul_le_mul_of_nonneg_right hcoeff hs

private theorem p04_alpha_dominates_block_coefficient
    (q : ℕ) (hq : 2 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    (q : ℝ) * (if q = 2 then 1 else if q = 4 then 2 else
        2 * ((q : ℝ) + γ)) ≤
      Real.sqrt (q : ℝ) * p04Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    simp [p04Alpha, Real.sq_sqrt]
  by_cases h4 : q = 4
  · subst q
    norm_num [p04Alpha]
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hr : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  simp only [if_neg h2, if_neg h4, p04Alpha]
  nlinarith

private theorem p04_stage_block_apply_eq
    {n : ℕ} [NeZero n] (model : P04WilkinsonModel)
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) (i : ZMod n) :
    p04RoundedMixedRadixBlockApply model stage x i =
      p04_rounded_radix_block model
        (fun j : ZMod stage.radix =>
          x (stage.permutation (stage.reindex ((stage.reindex.symm i).1, j))))
        (stage.reindex.symm i).2 := by
  rfl

private theorem p04_stage_block_error_bound
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2
            (fun i => p04RoundedMixedRadixBlockApply model stage x i -
              p04MixedRadixBlockApply stage x i) ≤
            (Real.sqrt (stage.radix : ℝ) *
                model.epsilon * p04Alpha stage.radix γ +
              c * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  let q := stage.radix
  letI : NeZero q := ⟨stage.radix_ne_zero⟩
  obtain ⟨c0, hc0, hpoint⟩ :=
    p04_rounded_radix_block_pointwise_bound stage.radix_two_le γ hγ
  let a : ℝ := if q = 2 then 1 else if q = 4 then 2 else
    2 * ((q : ℝ) + γ)
  have ha : 0 ≤ a := by
    dsimp [a]
    split_ifs <;> try norm_num
    have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
    positivity
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  let c : ℝ := (q : ℝ) * c0
  have hc : 0 ≤ c := mul_nonneg hq hc0
  refine ⟨c, hc, ?_⟩
  intro model hmodel hε x
  let block : Fin stage.blockCount → ZMod q → ℂ :=
    fun bi j => x (stage.permutation (stage.reindex (bi, j)))
  let err : Fin stage.blockCount → ZMod q → ℂ :=
    fun bi k => p04_rounded_radix_block model (block bi) k -
      ∑ j : ZMod q, ZMod.stdAddChar (j * k) * block bi j
  let C : ℝ := (q : ℝ) * (model.epsilon * a + c0 * model.epsilon ^ 2)
  have hε0 := model.epsilon_pos.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (bi : Fin stage.blockCount) :
      p04ComplexNorm2 (err bi) ≤ C * p04ComplexNorm2 (block bi) := by
    have hp (k : ZMod q) :
        ‖err bi k‖ ≤
          (model.epsilon * a + c0 * model.epsilon ^ 2) *
            (∑ j : ZMod q, ‖block bi j‖) := by
      exact hpoint model hmodel hε (block bi) k
    exact p04_complex_norm2_of_pointwise_l1_bound (err bi) (block bi)
      (model.epsilon * a + c0 * model.epsilon ^ 2)
      (by positivity) hp
  have hlift := p04_block_norm_lift stage.reindex stage.permutation x err C hC hb
  have heq : (fun i : ZMod n =>
        err (stage.reindex.symm i).1 (stage.reindex.symm i).2) =
      (fun i : ZMod n =>
        p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i) := by
    funext i
    rw [p04_stage_block_apply_eq]
    rfl
  rw [heq] at hlift
  have halpha := p04_alpha_dominates_block_coefficient q
    stage.radix_two_le γ hγ
  have hcoeff : C ≤
      Real.sqrt (q : ℝ) * model.epsilon * p04Alpha q γ +
        c * model.epsilon ^ 2 := by
    dsimp [C, c, a] at *
    nlinarith [mul_le_mul_of_nonneg_left halpha hε0]
  exact hlift.trans (mul_le_mul_of_nonneg_right hcoeff
    (Real.sqrt_nonneg _))

private theorem p04_complex_norm2_of_pointwise_bound {n : ℕ} [NeZero n]
    (e x : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i : ZMod n, ‖e i‖ ≤ c * ‖x i‖) :
    p04ComplexNorm2 e ≤ c * p04ComplexNorm2 x := by
  have he2 : p04ComplexNorm2 e ^ 2 ≤ c ^ 2 * p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq_formula, p04_complex_norm2_sq_formula]
    calc
      (∑ i : ZMod n, ‖e i‖ ^ 2) ≤
          ∑ i : ZMod n, (c * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq).2 (by
          rw [abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (mul_nonneg hc (norm_nonneg _))]
          exact hpoint i)
      _ = c ^ 2 * (∑ i : ZMod n, ‖x i‖ ^ 2) := by
        simp only [mul_pow, ← Finset.mul_sum]
  have he0 : 0 ≤ p04ComplexNorm2 e := Real.sqrt_nonneg _
  have hx0 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hc hx0]

private theorem p04_exact_twiddle_norm
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) =
      p04ComplexNorm2 x := by
  have hsq : p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) ^ 2 =
      p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq_formula, p04_complex_norm2_sq_formula]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ht : stage.useTwiddle <;>
      simp [p04MixedRadixTwiddleApply, ht, norm_mul, p04_root_exact_norm]
  have h1 : 0 ≤ p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) :=
    Real.sqrt_nonneg _
  have h2 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith

private theorem p04_stage_twiddle_error_bound
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (γ : ℝ) (hγ : 0 ≤ γ) (model : P04WilkinsonModel)
    (hmodel : model.gamma = γ) (hε : model.epsilon ≤ 1)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2
        (fun i => p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i) ≤
      (if stage.useTwiddle then
          model.epsilon * (3 + 2 * γ) +
            model.epsilon ^ 2 * (2 + 9 * γ)
        else 0) * p04ComplexNorm2 x := by
  by_cases ht : stage.useTwiddle
  · simp only [ht, if_true]
    have hc : 0 ≤ model.epsilon * (3 + 2 * γ) +
        model.epsilon ^ 2 * (2 + 9 * γ) := by
      have he := model.epsilon_pos.le
      positivity
    apply p04_complex_norm2_of_pointwise_bound _ x _ hc
    intro i
    simpa only [p04RoundedMixedRadixTwiddleApply,
      p04MixedRadixTwiddleApply, ht, if_true, hmodel] using
      p04_rounded_twiddle_error_bound model (stage.twiddleExponent i) (x i) hε
  · simp only [ht, if_false, zero_mul]
    have heq : (fun i => p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) = (0 : ZMod n → ℂ) := by
      funext i
      simp [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, ht]
    rw [heq]
    simp [p04ComplexNorm2, p04ComplexNorm2Sq]

private theorem p04_complex_norm2_eq_euclidean {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private theorem p04_complex_norm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i => x i + y i) ≤
      p04ComplexNorm2 x + p04ComplexNorm2 y := by
  rw [p04_complex_norm2_eq_euclidean,
    p04_complex_norm2_eq_euclidean x,
    p04_complex_norm2_eq_euclidean y]
  exact norm_add_le _ _

private theorem p04_exact_twiddle_sub
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (x y : ZMod n → ℂ) :
    (fun i => p04MixedRadixTwiddleApply stage x i -
      p04MixedRadixTwiddleApply stage y i) =
      p04MixedRadixTwiddleApply stage (fun i => x i - y i) := by
  funext i
  by_cases ht : stage.useTwiddle <;>
    simp [p04MixedRadixTwiddleApply, ht, mul_sub]

private theorem p04_alpha_nonneg
    (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ p04Alpha q γ := by
  unfold p04Alpha
  split_ifs <;> positivity

private theorem p04_stage_error_bound
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2
            (fun i => p04RoundedMixedRadixStageApply model stage x i -
              p04MixedRadixStageApply stage x i) ≤
            (Real.sqrt (stage.radix : ℝ) * model.epsilon *
                (p04Alpha stage.radix γ +
                  if stage.useTwiddle then 3 + 2 * γ else 0) +
              c * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  obtain ⟨cb, hcb, hblock⟩ := p04_stage_block_error_bound stage γ hγ
  let R : ℝ := Real.sqrt (stage.radix : ℝ)
  let A : ℝ := p04Alpha stage.radix γ
  let T : ℝ := if stage.useTwiddle then 3 + 2 * γ else 0
  let U : ℝ := if stage.useTwiddle then 2 + 9 * γ else 0
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hA : 0 ≤ A := p04_alpha_nonneg _ _ hγ
  have hT : 0 ≤ T := by dsimp [T]; split_ifs <;> linarith
  have hU : 0 ≤ U := by dsimp [U]; split_ifs <;> linarith
  let c : ℝ := cb + R * U + (T + U) * (R * A + cb)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro model hmodel hε x
  let y : ZMod n → ℂ := p04RoundedMixedRadixBlockApply model stage x
  let z : ZMod n → ℂ := p04MixedRadixBlockApply stage x
  let b : ℝ := R * model.epsilon * A + cb * model.epsilon ^ 2
  let t : ℝ := model.epsilon * T + model.epsilon ^ 2 * U
  have he := model.epsilon_pos.le
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hblock' : p04ComplexNorm2 (fun i => y i - z i) ≤
      b * p04ComplexNorm2 x := by
    exact hblock model hmodel hε x
  have hznorm : p04ComplexNorm2 z = R * p04ComplexNorm2 x := by
    have hs := hscale x
    change p04ComplexNorm2 (p04MixedRadixTwiddleApply stage z) = _ at hs
    rw [p04_exact_twiddle_norm] at hs
    exact hs
  have hynorm : p04ComplexNorm2 y ≤ (R + b) * p04ComplexNorm2 x := by
    have htri := p04_complex_norm2_add_le (fun i => y i - z i) z
    have heq : (fun i => (y i - z i) + z i) = y := by
      funext i
      ring
    rw [heq] at htri
    rw [hznorm] at htri
    nlinarith [hblock']
  have htw : p04ComplexNorm2
      (fun i => p04RoundedMixedRadixTwiddleApply model stage y i -
        p04MixedRadixTwiddleApply stage y i) ≤
      t * p04ComplexNorm2 y := by
    by_cases ht : stage.useTwiddle <;>
      simpa [t, T, U, ht] using
        p04_stage_twiddle_error_bound stage γ hγ model hmodel hε y
  have hsplit :
      (fun i => p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) =
      (fun i =>
        (p04RoundedMixedRadixTwiddleApply model stage y i -
          p04MixedRadixTwiddleApply stage y i) +
        (p04MixedRadixTwiddleApply stage y i -
          p04MixedRadixTwiddleApply stage z i)) := by
    funext i
    change p04RoundedMixedRadixTwiddleApply model stage y i -
      p04MixedRadixTwiddleApply stage z i = _
    ring
  have hsecond : p04ComplexNorm2
      (fun i => p04MixedRadixTwiddleApply stage y i -
        p04MixedRadixTwiddleApply stage z i) ≤
      b * p04ComplexNorm2 x := by
    rw [p04_exact_twiddle_sub, p04_exact_twiddle_norm]
    exact hblock'
  have htotal : p04ComplexNorm2
      (fun i => p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
      (t * (R + b) + b) * p04ComplexNorm2 x := by
    rw [hsplit]
    have htri := p04_complex_norm2_add_le
      (fun i => p04RoundedMixedRadixTwiddleApply model stage y i -
        p04MixedRadixTwiddleApply stage y i)
      (fun i => p04MixedRadixTwiddleApply stage y i -
        p04MixedRadixTwiddleApply stage z i)
    have hprod := mul_le_mul_of_nonneg_left hynorm ht0
    nlinarith [htri, htw, hsecond, hprod]
  have hscalar : t * (R + b) + b ≤
      R * model.epsilon * (A + T) + c * model.epsilon ^ 2 := by
    have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
      nlinarith [mul_nonneg he (sub_nonneg.mpr hε)]
    have htwsmall : t ≤ model.epsilon * (T + U) := by
      dsimp [t]
      nlinarith [mul_le_mul_of_nonneg_right he2 hU]
    have hbsmall : b ≤ model.epsilon * (R * A + cb) := by
      dsimp [b]
      nlinarith [mul_le_mul_of_nonneg_right he2 hcb]
    have hprod : t * b ≤
        model.epsilon ^ 2 * (T + U) * (R * A + cb) := by
      have htcoef : 0 ≤ model.epsilon * (T + U) := by positivity
      have hbc : 0 ≤ b := hb0
      calc
        t * b ≤ (model.epsilon * (T + U)) * b :=
          mul_le_mul_of_nonneg_right htwsmall hbc
        _ ≤ (model.epsilon * (T + U)) *
            (model.epsilon * (R * A + cb)) :=
          mul_le_mul_of_nonneg_left hbsmall htcoef
        _ = _ := by ring
    dsimp [t, b, c]
    nlinarith [hprod]
  exact htotal.trans (mul_le_mul_of_nonneg_right hscalar
    (Real.sqrt_nonneg _))

private theorem p04_exact_stage_sub
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (x y : ZMod n → ℂ) :
    (fun i => p04MixedRadixStageApply stage x i -
      p04MixedRadixStageApply stage y i) =
      p04MixedRadixStageApply stage (fun i => x i - y i) := by
  have hblock :
      (fun i => p04MixedRadixBlockApply stage x i -
        p04MixedRadixBlockApply stage y i) =
      p04MixedRadixBlockApply stage (fun i => x i - y i) := by
    funext i
    simp only [p04MixedRadixBlockApply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  funext i
  change p04MixedRadixTwiddleApply stage (p04MixedRadixBlockApply stage x) i -
    p04MixedRadixTwiddleApply stage (p04MixedRadixBlockApply stage y) i =
    p04MixedRadixTwiddleApply stage
      (p04MixedRadixBlockApply stage (fun i => x i - y i)) i
  rw [← hblock]
  exact congrFun (p04_exact_twiddle_sub stage
    (p04MixedRadixBlockApply stage x)
    (p04MixedRadixBlockApply stage y)) i

private theorem p04_stage_error_bound_normalized
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2
            (fun i => p04RoundedMixedRadixStageApply model stage x i -
              p04MixedRadixStageApply stage x i) ≤
            Real.sqrt (stage.radix : ℝ) *
              (model.epsilon *
                  (p04Alpha stage.radix γ +
                    if stage.useTwiddle then 3 + 2 * γ else 0) +
                c * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  obtain ⟨c, hc, hstage⟩ := p04_stage_error_bound stage hscale γ hγ
  refine ⟨c, hc, ?_⟩
  intro model hm hε x
  have hr : 1 ≤ Real.sqrt (stage.radix : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast stage.radix_two_le.trans' (by omega : 1 ≤ 2))
  have hpow : 0 ≤ c * model.epsilon ^ 2 := mul_nonneg hc (sq_nonneg _)
  have hnorm : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  calc
    _ ≤ (Real.sqrt (stage.radix : ℝ) * model.epsilon *
          (p04Alpha stage.radix γ +
            if stage.useTwiddle then 3 + 2 * γ else 0) +
        c * model.epsilon ^ 2) * p04ComplexNorm2 x :=
      hstage model hm hε x
    _ ≤ Real.sqrt (stage.radix : ℝ) *
          (model.epsilon * (p04Alpha stage.radix γ +
            if stage.useTwiddle then 3 + 2 * γ else 0) +
          c * model.epsilon ^ 2) * p04ComplexNorm2 x := by
      apply mul_le_mul_of_nonneg_right _ hnorm
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) hpow]

private theorem p04_stage_error_compose
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (xr xe : ZMod n → ℂ),
        p04ComplexNorm2 (fun i => xr i - xe i) ≤
          (model.epsilon * A + C * model.epsilon ^ 2) * p04ComplexNorm2 xe →
        p04ComplexNorm2
          (fun i => p04RoundedMixedRadixStageApply model stage xr i -
            p04MixedRadixStageApply stage xe i) ≤
          (model.epsilon *
              (A + p04Alpha stage.radix γ +
                if stage.useTwiddle then 3 + 2 * γ else 0) +
            C' * model.epsilon ^ 2) *
            p04ComplexNorm2 (p04MixedRadixStageApply stage xe) := by
  obtain ⟨cs, hcs, hstage⟩ :=
    p04_stage_error_bound_normalized stage hscale γ hγ
  let a : ℝ := p04Alpha stage.radix γ +
    if stage.useTwiddle then 3 + 2 * γ else 0
  let C' : ℝ := C + cs + (a + cs) * (A + C)
  have ha : 0 ≤ a := by
    dsimp [a]
    have halpha := p04_alpha_nonneg stage.radix γ hγ
    split_ifs <;> linarith
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro model hm hε xr xe hinit
  let b : ℝ := model.epsilon * A + C * model.epsilon ^ 2
  let d : ℝ := model.epsilon * a + cs * model.epsilon ^ 2
  have he := model.epsilon_pos.le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let R : ℝ := Real.sqrt (stage.radix : ℝ)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hxe : 0 ≤ p04ComplexNorm2 xe := Real.sqrt_nonneg _
  have hxrnorm : p04ComplexNorm2 xr ≤
      (1 + b) * p04ComplexNorm2 xe := by
    have htri := p04_complex_norm2_add_le (fun i => xr i - xe i) xe
    have heq : (fun i => (xr i - xe i) + xe i) = xr := by
      funext i
      ring
    rw [heq] at htri
    nlinarith [hinit]
  have hlocal : p04ComplexNorm2
      (fun i => p04RoundedMixedRadixStageApply model stage xr i -
        p04MixedRadixStageApply stage xr i) ≤
      R * d * p04ComplexNorm2 xr := by
    exact hstage model hm hε xr
  have hprop : p04ComplexNorm2
      (fun i => p04MixedRadixStageApply stage xr i -
        p04MixedRadixStageApply stage xe i) ≤
      R * b * p04ComplexNorm2 xe := by
    rw [p04_exact_stage_sub, hscale]
    simpa [R, b, mul_assoc] using
      (mul_le_mul_of_nonneg_left hinit hR)
  have htotal : p04ComplexNorm2
      (fun i => p04RoundedMixedRadixStageApply model stage xr i -
        p04MixedRadixStageApply stage xe i) ≤
      R * (d * (1 + b) + b) * p04ComplexNorm2 xe := by
    have hsplit : (fun i => p04RoundedMixedRadixStageApply model stage xr i -
        p04MixedRadixStageApply stage xe i) =
      (fun i =>
        (p04RoundedMixedRadixStageApply model stage xr i -
          p04MixedRadixStageApply stage xr i) +
        (p04MixedRadixStageApply stage xr i -
          p04MixedRadixStageApply stage xe i)) := by
      funext i
      ring
    rw [hsplit]
    have htri := p04_complex_norm2_add_le
      (fun i => p04RoundedMixedRadixStageApply model stage xr i -
        p04MixedRadixStageApply stage xr i)
      (fun i => p04MixedRadixStageApply stage xr i -
        p04MixedRadixStageApply stage xe i)
    have hprod := mul_le_mul_of_nonneg_left hxrnorm (mul_nonneg hR hd)
    nlinarith [htri, hlocal, hprop, hprod]
  have hscalar : d * (1 + b) + b ≤
      model.epsilon * (A + a) + C' * model.epsilon ^ 2 := by
    have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
      nlinarith [mul_nonneg he (sub_nonneg.mpr hε)]
    have hbsmall : b ≤ model.epsilon * (A + C) := by
      dsimp [b]
      nlinarith [mul_le_mul_of_nonneg_right he2 hC]
    have hdsmall : d ≤ model.epsilon * (a + cs) := by
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_right he2 hcs]
    have hprod : d * b ≤ model.epsilon ^ 2 * (a + cs) * (A + C) := by
      calc
        _ ≤ (model.epsilon * (a + cs)) * b :=
          mul_le_mul_of_nonneg_right hdsmall hb
        _ ≤ (model.epsilon * (a + cs)) *
            (model.epsilon * (A + C)) :=
          mul_le_mul_of_nonneg_left hbsmall (by positivity)
        _ = _ := by ring
    dsimp [d, b, C']
    nlinarith [hprod]
  rw [hscale]
  have hcoeff : R * (d * (1 + b) + b) ≤
      R * (model.epsilon * (A + a) + C' * model.epsilon ^ 2) :=
    mul_le_mul_of_nonneg_left hscalar hR
  have hfin := htotal.trans (mul_le_mul_of_nonneg_right hcoeff hxe)
  simpa [a, R, mul_assoc, mul_left_comm, mul_comm, add_assoc] using hfin

private theorem p04_foldl_error_bound
    {n : ℕ} [NeZero n] (stages : List (P04MixedRadixStage n))
    (hscale : ∀ s ∈ stages, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 x)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (xr xe : ZMod n → ℂ),
        p04ComplexNorm2 (fun i => xr i - xe i) ≤
          (model.epsilon * A + C * model.epsilon ^ 2) * p04ComplexNorm2 xe →
        p04ComplexNorm2
          (fun i =>
            (stages.foldl (fun state s =>
                p04RoundedMixedRadixStageApply model s state) xr) i -
            (stages.foldl (fun state s => p04MixedRadixStageApply s state) xe) i) ≤
          (model.epsilon *
              (A + (stages.map fun s => p04Alpha s.radix γ +
                if s.useTwiddle then 3 + 2 * γ else 0).sum) +
            C' * model.epsilon ^ 2) *
            p04ComplexNorm2
              (stages.foldl (fun state s => p04MixedRadixStageApply s state) xe) := by
  induction stages generalizing A C with
  | nil =>
      refine ⟨C, hC, ?_⟩
      intro model hm hε xr xe hinit
      simpa using hinit
  | cons s rest ih =>
      have hs := hscale s (by simp)
      have hrest : ∀ t ∈ rest, ∀ x : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply t x) =
            Real.sqrt (t.radix : ℝ) * p04ComplexNorm2 x := by
        intro t ht x
        exact hscale t (by simp [ht]) x
      obtain ⟨C1, hC1, hstep⟩ :=
        p04_stage_error_compose s hs γ hγ A C hA hC
      have ha : 0 ≤ p04Alpha s.radix γ +
          if s.useTwiddle then 3 + 2 * γ else 0 := by
        have hp := p04_alpha_nonneg s.radix γ hγ
        split_ifs <;> linarith
      obtain ⟨C2, hC2, htail⟩ := ih hrest
        (A + p04Alpha s.radix γ +
          if s.useTwiddle then 3 + 2 * γ else 0)
        C1 (by linarith) hC1
      refine ⟨C2, hC2, ?_⟩
      intro model hm hε xr xe hinit
      have hlocal := hstep model hm hε xr xe hinit
      have hfinal := htail model hm hε
        (p04RoundedMixedRadixStageApply model s xr)
        (p04MixedRadixStageApply s xe) hlocal
      simpa only [List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using hfinal

private theorem p04_fin_twiddle_sum (r : ℕ) (hr : 0 < r) (a : ℝ) :
    (∑ i : Fin r, if i.val + 1 < r then a else 0) =
      ((r : ℝ) - 1) * a := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  rw [Fin.sum_univ_castSucc]
  have hi (i : Fin n) : i.val + 1 < n + 1 := by omega
  simp only [Fin.val_castSucc, Fin.val_last, hi, lt_irrefl, ↓reduceIte]
  simp [Finset.sum_const]

private theorem p04_plan_stage_coefficient_sum
    {n : ℕ} [NeZero n] (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    ((List.ofFn plan.stage).map fun s =>
      p04Alpha s.radix γ +
        if s.useTwiddle then 3 + 2 * γ else 0).sum =
      p04K plan γ := by
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, Finset.sum_add_distrib, p04K]
  have htw : (∑ i : Fin plan.stageCount,
      if (plan.stage i).useTwiddle then 3 + 2 * γ else 0) =
      ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) := by
    simp_rw [plan.twiddle_pattern]
    simpa only [decide_eq_true_eq] using
      p04_fin_twiddle_sum plan.stageCount plan.stageCount_pos (3 + 2 * γ)
  rw [htw]

private theorem p04_permute_norm
    {n : ℕ} [NeZero n] (perm : ZMod n ≃ ZMod n)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04Permute perm x) = p04ComplexNorm2 x := by
  have hsq : p04ComplexNorm2 (p04Permute perm x) ^ 2 =
      p04ComplexNorm2 x ^ 2 := by
    rw [p04_complex_norm2_sq_formula, p04_complex_norm2_sq_formula]
    exact Equiv.sum_comp perm (fun i : ZMod n => ‖x i‖ ^ 2)
  have h1 : 0 ≤ p04ComplexNorm2 (p04Permute perm x) := Real.sqrt_nonneg _
  have h2 : 0 ≤ p04ComplexNorm2 x := Real.sqrt_nonneg _
  nlinarith

private theorem p04_plan_fft_error_bound
    {n : ℕ} [NeZero n] (plan : P04MixedRadixFftPlan n)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2
            (fun i => p04RoundedFftApply plan model x i -
              p04FourierTransform x i) ≤
            (model.epsilon * p04K plan γ + c * model.epsilon ^ 2) *
              p04ComplexNorm2 (p04FourierTransform x) := by
  let stages := List.ofFn plan.stage
  have hs : ∀ s ∈ stages, ∀ z : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s z) =
        Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 z := by
    intro s hmem z
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact plan.stage_norm_scaling i z
  obtain ⟨c, hc, hfold⟩ :=
    p04_foldl_error_bound stages hs γ hγ 0 0 le_rfl le_rfl
  refine ⟨c, hc, ?_⟩
  intro model hm hε x
  have hinit : p04ComplexNorm2 (fun i : ZMod n => x i - x i) ≤
      (model.epsilon * 0 + 0 * model.epsilon ^ 2) * p04ComplexNorm2 x := by
    simp [p04ComplexNorm2, p04ComplexNorm2Sq]
  have hraw := hfold model hm hε x x hinit
  rw [p04_plan_stage_coefficient_sum] at hraw
  let r := p04ApplyRoundedMixedRadixStages model plan.stage x
  let e := p04ApplyMixedRadixStages plan.stage x
  simp only [zero_add] at hraw
  change p04ComplexNorm2 (fun i => r i - e i) ≤
    (model.epsilon * p04K plan γ + c * model.epsilon ^ 2) *
      p04ComplexNorm2 e at hraw
  have heq : (fun i => p04RoundedFftApply plan model x i -
      p04FourierTransform x i) =
      p04Permute plan.finalPermutation (fun i => r i - e i) := by
    funext i
    rw [← plan.exact_factorization x]
    rfl
  rw [heq, p04_permute_norm]
  have hexact : p04ComplexNorm2 (p04FourierTransform x) =
      p04ComplexNorm2 e := by
    rw [← plan.exact_factorization x]
    exact p04_permute_norm plan.finalPermutation e
  rw [hexact]
  exact hraw

private abbrev p04_multi_rest {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :=
  (j : {j : Fin m // j ≠ i}) → ZMod (axis j).order

private noncomputable instance p04_multi_rest_fintype {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    Fintype (p04_multi_rest axis i) := by
  letI (j : {j : Fin m // j ≠ i}) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  infer_instance

private noncomputable def p04_multi_slice_equiv {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    p04_multi_rest axis i × ZMod (axis i).order ≃ P04MultiIndex axis :=
  (Equiv.prodComm _ _).trans
    (Equiv.piSplitAt i (fun j => ZMod (axis j).order)).symm

private theorem p04_multi_slice_equiv_axis {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : p04_multi_rest axis i) (k : ZMod (axis i).order) :
    p04_multi_slice_equiv axis i (r, k) i = k := by
  simp [p04_multi_slice_equiv, Equiv.piSplitAt_symm_apply]

private theorem p04_multi_slice_equiv_rest {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : p04_multi_rest axis i) (k : ZMod (axis i).order)
    (j : Fin m) (hji : j ≠ i) :
    p04_multi_slice_equiv axis i (r, k) j = r ⟨j, hji⟩ := by
  simp [p04_multi_slice_equiv, Equiv.piSplitAt_symm_apply, hji]

private theorem p04_multi_slice_update {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : p04_multi_rest axis i)
    (k j : ZMod (axis i).order) :
    Function.update (p04_multi_slice_equiv axis i (r, k)) i j =
      p04_multi_slice_equiv axis i (r, j) := by
  funext h
  by_cases hhi : h = i
  · subst h
    simp [p04_multi_slice_equiv_axis]
  · rw [Function.update_of_ne hhi,
      p04_multi_slice_equiv_rest axis i r k h hhi,
      p04_multi_slice_equiv_rest axis i r j h hhi]

private theorem p04_multi_norm2_sq_formula {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x ^ 2 = ∑ j : P04MultiIndex axis, ‖x j‖ ^ 2 := by
  classical
  letI (i : Fin m) : NeZero (axis i).order :=
    ⟨Nat.ne_of_gt (axis i).order_pos⟩
  unfold p04MultiNorm2
  simpa using (EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis)))

private theorem p04_multi_norm2_eq_euclidean {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))‖ := by
  rfl

private theorem p04_multi_norm2_add_le {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 (fun j => x j + y j) ≤
      p04MultiNorm2 x + p04MultiNorm2 y := by
  rw [p04_multi_norm2_eq_euclidean,
    p04_multi_norm2_eq_euclidean x,
    p04_multi_norm2_eq_euclidean y]
  exact norm_add_le _ _

private theorem p04_multi_slice_norm_lift {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ r : p04_multi_rest axis i,
      p04ComplexNorm2 (fun k => x (p04_multi_slice_equiv axis i (r, k))) ≤
        c * p04ComplexNorm2
          (fun k => y (p04_multi_slice_equiv axis i (r, k)))) :
    p04MultiNorm2 x ≤ c * p04MultiNorm2 y := by
  classical
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let e := p04_multi_slice_equiv axis i
  have hr2 (r : p04_multi_rest axis i) :
      (∑ k : ZMod (axis i).order, ‖x (e (r, k))‖ ^ 2) ≤
        c ^ 2 * (∑ k : ZMod (axis i).order, ‖y (e (r, k))‖ ^ 2) := by
    have hh := h r
    have hx0 : 0 ≤ p04ComplexNorm2 (fun k => x (e (r, k))) := Real.sqrt_nonneg _
    have hy0 : 0 ≤ p04ComplexNorm2 (fun k => y (e (r, k))) := Real.sqrt_nonneg _
    have hsqx := p04_complex_norm2_sq_formula (fun k => x (e (r, k)))
    have hsqy := p04_complex_norm2_sq_formula (fun k => y (e (r, k)))
    nlinarith [sq_nonneg (c * p04ComplexNorm2 (fun k => y (e (r, k))))]
  have hsum :
      (∑ r : p04_multi_rest axis i,
        ∑ k : ZMod (axis i).order, ‖x (e (r, k))‖ ^ 2) ≤
      c ^ 2 * (∑ r : p04_multi_rest axis i,
        ∑ k : ZMod (axis i).order, ‖y (e (r, k))‖ ^ 2) := by
    calc
      _ ≤ ∑ r : p04_multi_rest axis i,
          c ^ 2 * (∑ k : ZMod (axis i).order, ‖y (e (r, k))‖ ^ 2) :=
        Finset.sum_le_sum fun r _ => hr2 r
      _ = _ := by rw [← Finset.mul_sum]
  have hreindex (z : P04MultiArray axis) :
      (∑ r : p04_multi_rest axis i,
        ∑ k : ZMod (axis i).order, ‖z (e (r, k))‖ ^ 2) =
        ∑ j : P04MultiIndex axis, ‖z j‖ ^ 2 := by
    calc
      _ = ∑ p : p04_multi_rest axis i × ZMod (axis i).order,
          ‖z (e p)‖ ^ 2 := by rw [Fintype.sum_prod_type]
      _ = _ := Equiv.sum_comp e (fun j : P04MultiIndex axis => ‖z j‖ ^ 2)
  have hsquares : p04MultiNorm2 x ^ 2 ≤ c ^ 2 * p04MultiNorm2 y ^ 2 := by
    rw [p04_multi_norm2_sq_formula, p04_multi_norm2_sq_formula]
    rw [← hreindex x, ← hreindex y]
    exact hsum
  have hx0 : 0 ≤ p04MultiNorm2 x := norm_nonneg _
  have hy0 : 0 ≤ p04MultiNorm2 y := norm_nonneg _
  nlinarith [mul_nonneg hc hy0]

private theorem p04_coordinate_slice_exact {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis)
    (r : p04_multi_rest axis i) (k : ZMod (axis i).order) :
    p04CoordinateTransform axis i x (p04_multi_slice_equiv axis i (r, k)) =
      p04FourierTransform
        (fun j => x (p04_multi_slice_equiv axis i (r, j))) k := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp only [p04CoordinateTransform, p04FourierTransform,
    p04_multi_slice_equiv_axis]
  congr 1
  funext j
  rw [p04_multi_slice_update]

private theorem p04_coordinate_slice_rounded {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis)
    (r : p04_multi_rest axis i) (k : ZMod (axis i).order) :
    p04RoundedCoordinateTransform axis i model x
        (p04_multi_slice_equiv axis i (r, k)) =
      p04RoundedFftApply (axis i).plan model
        (fun j => x (p04_multi_slice_equiv axis i (r, j))) k := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp only [p04RoundedCoordinateTransform,
    p04_multi_slice_equiv_axis]
  congr 1
  funext j
  rw [p04_multi_slice_update]

private theorem p04_k_nonneg
    {n : ℕ} [NeZero n] (plan : P04MixedRadixFftPlan n)
    (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ p04K plan γ := by
  unfold p04K
  have hsum : 0 ≤ ∑ i : Fin plan.stageCount,
      p04Alpha (plan.stage i).radix γ :=
    Finset.sum_nonneg fun i _ => p04_alpha_nonneg _ _ hγ
  have hcount : 0 ≤ (plan.stageCount : ℝ) - 1 := by
    have hp : 1 ≤ (plan.stageCount : ℝ) := by
      exact_mod_cast plan.stageCount_pos
    linarith
  have htw : 0 ≤ 3 + 2 * γ := by linarith
  positivity

private theorem p04_coordinate_error_bound {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : P04MultiArray axis,
          p04MultiNorm2
            (fun idx => p04RoundedCoordinateTransform axis i model x idx -
              p04CoordinateTransform axis i x idx) ≤
            (model.epsilon * p04AxisK (axis i) γ +
              c * model.epsilon ^ 2) *
              p04MultiNorm2 (p04CoordinateTransform axis i x) := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  obtain ⟨c, hc, hplan⟩ := p04_plan_fft_error_bound (axis i).plan γ hγ
  refine ⟨c, hc, ?_⟩
  intro model hm hε x
  have hk : 0 ≤ p04AxisK (axis i) γ := by
    exact p04_k_nonneg (axis i).plan γ hγ
  have hcoef : 0 ≤ model.epsilon * p04AxisK (axis i) γ +
      c * model.epsilon ^ 2 := by
    have he := model.epsilon_pos.le
    positivity
  apply p04_multi_slice_norm_lift axis i _ _ _ hcoef
  intro r
  let slice : ZMod (axis i).order → ℂ :=
    fun k => x (p04_multi_slice_equiv axis i (r, k))
  have hs := hplan model hm hε slice
  have hexact : (fun k => p04CoordinateTransform axis i x
      (p04_multi_slice_equiv axis i (r, k))) =
      p04FourierTransform slice := by
    funext k
    exact p04_coordinate_slice_exact axis i x r k
  have hrounded : (fun k => p04RoundedCoordinateTransform axis i model x
      (p04_multi_slice_equiv axis i (r, k))) =
      p04RoundedFftApply (axis i).plan model slice := by
    funext k
    exact p04_coordinate_slice_rounded axis i model x r k
  rw [← hexact, ← hrounded] at hs
  simpa only [p04AxisK] using hs

private theorem p04_fourier_norm_scaling
    {n : ℕ} [NeZero n] (plan : P04MixedRadixFftPlan n)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04FourierTransform x) =
      Real.sqrt (n : ℝ) * p04ComplexNorm2 x := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn
  have h := plan.fourier_rms_scaling x
  unfold p04ComplexRms at h
  apply (div_eq_iff hr.ne').mp at h
  calc
    _ = Real.sqrt (n : ℝ) * (p04ComplexNorm2 x / Real.sqrt (n : ℝ)) *
        Real.sqrt (n : ℝ) := h
    _ = _ := by field_simp [hr.ne']

private theorem p04_multi_sum_slices {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (z : P04MultiArray axis) :
    (∑ idx : P04MultiIndex axis, ‖z idx‖ ^ 2) =
      ∑ r : p04_multi_rest axis i,
        ∑ k : ZMod (axis i).order,
          ‖z (p04_multi_slice_equiv axis i (r, k))‖ ^ 2 := by
  classical
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let e := p04_multi_slice_equiv axis i
  calc
    _ = ∑ p : p04_multi_rest axis i × ZMod (axis i).order,
          ‖z (e p)‖ ^ 2 :=
      (Equiv.sum_comp e (fun idx : P04MultiIndex axis => ‖z idx‖ ^ 2)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

private theorem p04_coordinate_norm_scaling {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04MultiNorm2 (p04CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p04MultiNorm2 x := by
  classical
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let R : ℝ := Real.sqrt ((axis i).order : ℝ)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hslice (r : p04_multi_rest axis i) :
      p04ComplexNorm2
        (fun k => p04CoordinateTransform axis i x
          (p04_multi_slice_equiv axis i (r, k))) =
      R * p04ComplexNorm2
        (fun k => x (p04_multi_slice_equiv axis i (r, k))) := by
    have hh := p04_fourier_norm_scaling (axis i).plan
      (fun k => x (p04_multi_slice_equiv axis i (r, k)))
    have hexact : (fun k => p04CoordinateTransform axis i x
        (p04_multi_slice_equiv axis i (r, k))) =
        p04FourierTransform
          (fun k => x (p04_multi_slice_equiv axis i (r, k))) := by
      funext k
      exact p04_coordinate_slice_exact axis i x r k
    rw [hexact]
    exact hh
  have hsq : p04MultiNorm2 (p04CoordinateTransform axis i x) ^ 2 =
      R ^ 2 * p04MultiNorm2 x ^ 2 := by
    rw [p04_multi_norm2_sq_formula, p04_multi_norm2_sq_formula,
      p04_multi_sum_slices axis i,
      p04_multi_sum_slices axis i]
    simp_rw [← p04_complex_norm2_sq_formula]
    simp_rw [hslice]
    simp only [mul_pow, ← Finset.mul_sum]
  have h1 : 0 ≤ p04MultiNorm2 (p04CoordinateTransform axis i x) := norm_nonneg _
  have h2 : 0 ≤ p04MultiNorm2 x := norm_nonneg _
  nlinarith [mul_nonneg hR h2]

private theorem p04_coordinate_prefix_foldr {m : ℕ}
    (axis : Fin m → P04FftAxis)
    (k : ℕ) (hk : k ≤ m) (x : P04MultiArray axis) :
    (List.ofFn (fun j : Fin k => Fin.castLE hk j)).foldr
        (fun i state => p04CoordinateTransform axis i state) x =
      p04ApplyCoordinatePrefix axis k x := by
  induction k generalizing x with
  | zero => simp [p04ApplyCoordinatePrefix]
  | succ k ih =>
      have hk0 : k ≤ m := by omega
      have hlt : k < m := by omega
      rw [List.ofFn_succ_last, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      have heq : (List.ofFn fun j : Fin k =>
          Fin.castLE hk j.castSucc) =
          List.ofFn (fun j : Fin k => Fin.castLE hk0 j) := by
        congr 1
      rw [heq]
      have hlast : Fin.castLE hk (Fin.last k) = ⟨k, hlt⟩ := by
        apply Fin.ext
        rfl
      rw [hlast]
      rw [ih hk0]
      simp [p04ApplyCoordinatePrefix, p04CoordinateTransformNat, hlt]

private theorem p04_run_output_foldr {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (model : P04WilkinsonModel)
    (run : P04MultidimensionalFftRun plan model) :
    run.computedState 0 =
      (List.ofFn (fun i : Fin m => i)).foldr
        (fun i state => p04RoundedCoordinateTransform plan.axis i model state)
        run.input := by
  let coords : List (Fin m) := List.ofFn (fun i : Fin m => i)
  let f : Fin m → P04MultiArray plan.axis → P04MultiArray plan.axis :=
    fun i state => p04RoundedCoordinateTransform plan.axis i model state
  have haux (i : Fin (m + 1)) :
      run.computedState i =
        (coords.drop i.val).foldr f run.input := by
    induction i using Fin.reverseInduction with
    | last =>
        rw [run.computed_input]
        change run.input = (coords.drop m).foldr f run.input
        have hl : coords.length = m := by simp [coords]
        have hdrop : coords.drop m = [] :=
          List.drop_of_length_le (by omega)
        rw [hdrop]
        rfl
    | cast i ih =>
        have hdrop : coords.drop i.val =
            i :: coords.drop (i.val + 1) := by
          have h := List.drop_eq_getElem_cons (l := coords)
            (i := i.val) (by simpa [coords] using i.isLt)
          simpa [coords, List.getElem_ofFn] using h
        change run.computedState i.castSucc =
          (coords.drop i.val).foldr f run.input
        rw [hdrop, List.foldr_cons]
        change run.computedState i.succ =
          (coords.drop (i.val + 1)).foldr f run.input at ih
        rw [← ih]
        exact run.stage_step i
  simpa [coords] using haux 0

private theorem p04_coordinate_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) :
    (fun idx => p04CoordinateTransform axis i x idx -
      p04CoordinateTransform axis i y idx) =
      p04CoordinateTransform axis i (fun idx => x idx - y idx) := by
  funext idx
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp only [p04CoordinateTransform]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

private theorem p04_coordinate_error_compose {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (xr xe : P04MultiArray axis),
        p04MultiNorm2 (fun idx => xr idx - xe idx) ≤
          (model.epsilon * A + C * model.epsilon ^ 2) * p04MultiNorm2 xe →
        p04MultiNorm2
          (fun idx => p04RoundedCoordinateTransform axis i model xr idx -
            p04CoordinateTransform axis i xe idx) ≤
          (model.epsilon * (A + p04AxisK (axis i) γ) +
            C' * model.epsilon ^ 2) *
              p04MultiNorm2 (p04CoordinateTransform axis i xe) := by
  obtain ⟨cs, hcs, hcoord⟩ := p04_coordinate_error_bound axis i γ hγ
  let K := p04AxisK (axis i) γ
  have hK : 0 ≤ K := p04_k_nonneg (axis i).plan γ hγ
  let C' : ℝ := C + cs + (K + cs) * (A + C)
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨C', hC', ?_⟩
  intro model hm hε xr xe hinit
  let b : ℝ := model.epsilon * A + C * model.epsilon ^ 2
  let d : ℝ := model.epsilon * K + cs * model.epsilon ^ 2
  let R : ℝ := Real.sqrt ((axis i).order : ℝ)
  have he := model.epsilon_pos.le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hxe : 0 ≤ p04MultiNorm2 xe := norm_nonneg _
  have hxrnorm : p04MultiNorm2 xr ≤ (1 + b) * p04MultiNorm2 xe := by
    have htri := p04_multi_norm2_add_le (fun idx => xr idx - xe idx) xe
    have heq : (fun idx => (xr idx - xe idx) + xe idx) = xr := by
      funext idx
      ring
    rw [heq] at htri
    nlinarith [hinit]
  have hlocal : p04MultiNorm2
      (fun idx => p04RoundedCoordinateTransform axis i model xr idx -
        p04CoordinateTransform axis i xr idx) ≤
      R * d * p04MultiNorm2 xr := by
    have hh := hcoord model hm hε xr
    rw [p04_coordinate_norm_scaling] at hh
    simpa [R, d, K, mul_assoc, mul_comm, mul_left_comm] using hh
  have hprop : p04MultiNorm2
      (fun idx => p04CoordinateTransform axis i xr idx -
        p04CoordinateTransform axis i xe idx) ≤
      R * b * p04MultiNorm2 xe := by
    rw [p04_coordinate_sub, p04_coordinate_norm_scaling]
    simpa [R, b, mul_assoc] using
      (mul_le_mul_of_nonneg_left hinit hR)
  have htotal : p04MultiNorm2
      (fun idx => p04RoundedCoordinateTransform axis i model xr idx -
        p04CoordinateTransform axis i xe idx) ≤
      R * (d * (1 + b) + b) * p04MultiNorm2 xe := by
    have hsplit : (fun idx => p04RoundedCoordinateTransform axis i model xr idx -
        p04CoordinateTransform axis i xe idx) =
      (fun idx =>
        (p04RoundedCoordinateTransform axis i model xr idx -
          p04CoordinateTransform axis i xr idx) +
        (p04CoordinateTransform axis i xr idx -
          p04CoordinateTransform axis i xe idx)) := by
      funext idx
      ring
    rw [hsplit]
    have htri := p04_multi_norm2_add_le
      (fun idx => p04RoundedCoordinateTransform axis i model xr idx -
        p04CoordinateTransform axis i xr idx)
      (fun idx => p04CoordinateTransform axis i xr idx -
        p04CoordinateTransform axis i xe idx)
    have hprod := mul_le_mul_of_nonneg_left hxrnorm (mul_nonneg hR hd)
    nlinarith [htri, hlocal, hprop, hprod]
  have hscalar : d * (1 + b) + b ≤
      model.epsilon * (A + K) + C' * model.epsilon ^ 2 := by
    have he2 : model.epsilon ^ 2 ≤ model.epsilon := by
      nlinarith [mul_nonneg he (sub_nonneg.mpr hε)]
    have hbsmall : b ≤ model.epsilon * (A + C) := by
      dsimp [b]
      nlinarith [mul_le_mul_of_nonneg_right he2 hC]
    have hdsmall : d ≤ model.epsilon * (K + cs) := by
      dsimp [d]
      nlinarith [mul_le_mul_of_nonneg_right he2 hcs]
    have hprod : d * b ≤ model.epsilon ^ 2 * (K + cs) * (A + C) := by
      calc
        _ ≤ (model.epsilon * (K + cs)) * b :=
          mul_le_mul_of_nonneg_right hdsmall hb
        _ ≤ (model.epsilon * (K + cs)) *
            (model.epsilon * (A + C)) :=
          mul_le_mul_of_nonneg_left hbsmall (by positivity)
        _ = _ := by ring
    dsimp [d, b, C']
    nlinarith [hprod]
  rw [p04_coordinate_norm_scaling]
  have hcoeff := mul_le_mul_of_nonneg_left hscalar hR
  have hfin := htotal.trans (mul_le_mul_of_nonneg_right hcoeff hxe)
  simpa [K, R, mul_assoc, mul_comm, mul_left_comm, add_assoc] using hfin

private theorem p04_multi_foldl_error_bound {m : ℕ}
    (axis : Fin m → P04FftAxis) (indices : List (Fin m))
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (xr xe : P04MultiArray axis),
        p04MultiNorm2 (fun idx => xr idx - xe idx) ≤
          (model.epsilon * A + C * model.epsilon ^ 2) * p04MultiNorm2 xe →
        p04MultiNorm2
          (fun idx =>
            (indices.foldl (fun state i =>
                p04RoundedCoordinateTransform axis i model state) xr) idx -
            (indices.foldl (fun state i =>
                p04CoordinateTransform axis i state) xe) idx) ≤
          (model.epsilon *
              (A + (indices.map fun i => p04AxisK (axis i) γ).sum) +
            C' * model.epsilon ^ 2) *
            p04MultiNorm2
              (indices.foldl (fun state i =>
                p04CoordinateTransform axis i state) xe) := by
  induction indices generalizing A C with
  | nil =>
      refine ⟨C, hC, ?_⟩
      intro model hm hε xr xe hinit
      simpa using hinit
  | cons i rest ih =>
      obtain ⟨C1, hC1, hstep⟩ :=
        p04_coordinate_error_compose axis i γ hγ A C hA hC
      have hK : 0 ≤ p04AxisK (axis i) γ :=
        p04_k_nonneg (axis i).plan γ hγ
      obtain ⟨C2, hC2, htail⟩ := ih
        (A + p04AxisK (axis i) γ) C1 (by linarith) hC1
      refine ⟨C2, hC2, ?_⟩
      intro model hm hε xr xe hinit
      have hlocal := hstep model hm hε xr xe hinit
      have hfinal := htail model hm hε
        (p04RoundedCoordinateTransform axis i model xr)
        (p04CoordinateTransform axis i xe) hlocal
      simpa only [List.foldl_cons, List.map_cons, List.sum_cons, add_assoc] using hfinal

private theorem p04_reverse_axes_sum {m : ℕ}
    (axis : Fin m → P04FftAxis) (γ : ℝ) :
    (((List.ofFn (fun i : Fin m => i)).reverse).map
      fun i => p04AxisK (axis i) γ).sum =
      ∑ i : Fin m, p04AxisK (axis i) γ := by
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem p04_foldl_reverse_axes {m : ℕ}
    (axis : Fin m → P04FftAxis)
    (model : P04WilkinsonModel) (x : P04MultiArray axis) :
    ((List.ofFn (fun i : Fin m => i)).reverse).foldl
        (fun state i => p04RoundedCoordinateTransform axis i model state) x =
      (List.ofFn (fun i : Fin m => i)).foldr
        (fun i state => p04RoundedCoordinateTransform axis i model state) x := by
  simpa using (List.foldr_reverse
    (l := (List.ofFn (fun i : Fin m => i)).reverse)
    (f := fun i state => p04RoundedCoordinateTransform axis i model state)
    (b := x)).symm

private theorem p04_foldl_reverse_axes_exact {m : ℕ}
    (axis : Fin m → P04FftAxis) (x : P04MultiArray axis) :
    ((List.ofFn (fun i : Fin m => i)).reverse).foldl
        (fun state i => p04CoordinateTransform axis i state) x =
      p04ApplyCoordinatePrefix axis m x := by
  have h := (List.foldr_reverse
    (l := (List.ofFn (fun i : Fin m => i)).reverse)
    (f := fun i state => p04CoordinateTransform axis i state)
    (b := x)).symm
  have h1 : ((List.ofFn (fun i : Fin m => i)).reverse).foldl
      (fun state i => p04CoordinateTransform axis i state) x =
      (List.ofFn (fun i : Fin m => i)).foldr
        (fun i state => p04CoordinateTransform axis i state) x := by
    simpa using h
  exact h1.trans (by simpa using p04_coordinate_prefix_foldr axis m le_rfl x)

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
  let indices : List (Fin m) :=
    (List.ofFn (fun i : Fin m => i)).reverse
  obtain ⟨c, hc, hfold⟩ :=
    p04_multi_foldl_error_bound plan.axis indices γ family.gamma_nonneg
      0 0 le_rfl le_rfl
  refine ⟨c, hc, 1, by norm_num, ?_⟩
  intro ε hε
  let model := family.model ε
  let run := family.run ε
  have hm : model.gamma = γ := family.model_gamma ε
  have he : model.epsilon ≤ 1 := by
    rw [family.model_epsilon ε]
    exact hε
  have hinit : p04MultiNorm2
      (fun idx : P04MultiIndex plan.axis =>
        family.input idx - family.input idx) ≤
      (model.epsilon * 0 + 0 * model.epsilon ^ 2) *
        p04MultiNorm2 family.input := by
    have hzero : (fun idx : P04MultiIndex plan.axis =>
        family.input idx - family.input idx) =
        (0 : P04MultiArray plan.axis) := by
      funext idx
      simp
    rw [hzero]
    simp [p04MultiNorm2]
  have hraw := hfold model hm he family.input family.input hinit
  rw [p04_reverse_axes_sum] at hraw
  simp only [zero_add] at hraw
  have hrounded :
      indices.foldl
          (fun state i => p04RoundedCoordinateTransform plan.axis i model state)
          family.input = run.computedState 0 := by
    rw [p04_foldl_reverse_axes]
    rw [← family.run_input ε]
    exact (p04_run_output_foldr plan model run).symm
  have hexact :
      indices.foldl
          (fun state i => p04CoordinateTransform plan.axis i state)
          family.input = p04FamilyMultiExactOutput family := by
    exact p04_foldl_reverse_axes_exact plan.axis family.input
  rw [hrounded, hexact] at hraw
  have herror : p04FamilyMultiFftRoundoffError family ε =
      (fun idx => run.computedState 0 idx -
        p04FamilyMultiExactOutput family idx) := by
    rfl
  rw [← herror] at hraw
  rw [family.model_epsilon ε] at hraw
  have hcard : 0 < p04MultiCardinality plan.axis := by
    unfold p04MultiCardinality
    exact Finset.prod_pos fun i _ => (plan.axis i).order_pos
  have hroot : 0 < Real.sqrt (p04MultiCardinality plan.axis : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hcard)
  have hn : 0 < p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
    have hnonneg : 0 ≤ p04MultiNorm2 (p04FamilyMultiExactOutput family) :=
      norm_nonneg _
    have hne : p04MultiNorm2 (p04FamilyMultiExactOutput family) ≠ 0 := by
      intro hz
      have hz' : p04MultiRms (p04FamilyMultiExactOutput family) = 0 := by
        simp [p04MultiRms, hz]
      linarith
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hratio :
      p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) /
          p04MultiNorm2 (p04FamilyMultiExactOutput family) ≤
        ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
          c * ε.1 ^ 2 := by
    exact (div_le_iff₀ hn).2 hraw
  calc
    p04MultiRms (p04FamilyMultiFftRoundoffError family ε) /
        p04MultiRms (p04FamilyMultiExactOutput family) =
        p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) /
          p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
      unfold p04MultiRms
      exact div_div_div_cancel_right₀ hroot.ne' _ _
    _ ≤ _ := hratio

end VSCLReuse

import VSCLReuse.P04.Definitions

namespace VSCLReuse

private lemma p04_norm_mk_le_of_abs_le
    {a b c d : ℝ} (hac : |a| ≤ |c|) (hbd : |b| ≤ |d|) :
    ‖(⟨a, b⟩ : ℂ)‖ ≤ ‖(⟨c, d⟩ : ℂ)‖ := by
  simp only [Complex.norm_eq_sqrt_sq_add_sq]
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.mpr hac) (sq_le_sq.mpr hbd))

private lemma p04_flAdd_abs_error (model : P04WilkinsonModel) (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤ model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, h⟩ := model.add_model a b
  rw [h]
  have ha : |a * θa * model.epsilon| ≤ |a| * model.epsilon := by
    rw [abs_mul, abs_mul, abs_of_pos model.epsilon_pos]
    calc
      |a| * |θa| * model.epsilon ≤ |a| * 1 * model.epsilon := by
        gcongr
        exact le_of_lt model.epsilon_pos
      _ = |a| * model.epsilon := by ring
  have hb : |b * θb * model.epsilon| ≤ |b| * model.epsilon := by
    rw [abs_mul, abs_mul, abs_of_pos model.epsilon_pos]
    calc
      |b| * |θb| * model.epsilon ≤ |b| * 1 * model.epsilon := by
        gcongr
        exact le_of_lt model.epsilon_pos
      _ = |b| * model.epsilon := by ring
  convert (abs_add_le (a * θa * model.epsilon) (b * θb * model.epsilon)).trans
    (add_le_add ha hb) using 1 <;> ring

private lemma p04_roundedComplexAdd_error (model : P04WilkinsonModel) (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  let u : ℂ := ⟨|x.re|, |x.im|⟩
  let v : ℂ := ⟨|y.re|, |y.im|⟩
  have hu : ‖u‖ = ‖x‖ := by
    simp [u, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hv : ‖v‖ = ‖y‖ := by
    simp [v, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hcoord :
      ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
        ‖(⟨model.epsilon * (|x.re| + |y.re|),
           model.epsilon * (|x.im| + |y.im|)⟩ : ℂ)‖ := by
    apply p04_norm_mk_le_of_abs_le
    · simpa [p04RoundedComplexAdd, abs_mul,
        abs_of_pos model.epsilon_pos,
        abs_of_nonneg (add_nonneg (abs_nonneg x.re) (abs_nonneg y.re))] using
        p04_flAdd_abs_error model x.re y.re
    · simpa [p04RoundedComplexAdd, abs_mul,
        abs_of_pos model.epsilon_pos,
        abs_of_nonneg (add_nonneg (abs_nonneg x.im) (abs_nonneg y.im))] using
        p04_flAdd_abs_error model x.im y.im
  calc
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
        ‖(⟨model.epsilon * (|x.re| + |y.re|),
           model.epsilon * (|x.im| + |y.im|)⟩ : ℂ)‖ := hcoord
    _ = model.epsilon * ‖u + v‖ := by
      have heq : (⟨model.epsilon * (|x.re| + |y.re|),
           model.epsilon * (|x.im| + |y.im|)⟩ : ℂ) =
          (model.epsilon : ℂ) * (u + v) := by
        apply Complex.ext
        · simp [u, v, Complex.mul_re]
        · simp [u, v, Complex.mul_im]
      rw [heq, norm_mul, Complex.norm_of_nonneg (le_of_lt model.epsilon_pos)]
    _ ≤ model.epsilon * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le u v) (le_of_lt model.epsilon_pos)
    _ = model.epsilon * (‖x‖ + ‖y‖) := by rw [hu, hv]

private lemma p04_roundedComplexSum_two (model : P04WilkinsonModel)
    (term : ZMod 2 → ℂ) :
    p04RoundedComplexSum model term =
      p04RoundedComplexAdd model (term 0) (term 1) := by
  simp [p04RoundedComplexSum, p04RoundedComplexAdd, recursiveSum]

private lemma p04_flMul_abs_error (model : P04WilkinsonModel) (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * (|a| * |b|) := by
  obtain ⟨θ, hθ, h⟩ := model.mul_model a b
  rw [h]
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        |a| * |b| * |θ| * model.epsilon := by
      rw [show a * b * (1 + θ * model.epsilon) - a * b =
        a * b * θ * model.epsilon by ring, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg he]
    _ ≤ |a| * |b| * 1 * model.epsilon := by gcongr
    _ = model.epsilon * (|a| * |b|) := by ring

private lemma p04_abs_diag_products_le (x y : ℂ) :
    |x.re| * |y.re| + |x.im| * |y.im| ≤ ‖x‖ * ‖y‖ := by
  let u : ℂ := ⟨|x.re|, |x.im|⟩
  let v : ℂ := ⟨|y.re|, -|y.im|⟩
  have hu : ‖u‖ = ‖x‖ := by simp [u, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hv : ‖v‖ = ‖y‖ := by simp [v, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  calc
    |x.re| * |y.re| + |x.im| * |y.im| = (u * v).re := by
      simp [u, v, Complex.mul_re]
    _ ≤ ‖u * v‖ := Complex.re_le_norm _
    _ = ‖x‖ * ‖y‖ := by rw [norm_mul, hu, hv]

private lemma p04_abs_cross_products_le (x y : ℂ) :
    |x.re| * |y.im| + |x.im| * |y.re| ≤ ‖x‖ * ‖y‖ := by
  let u : ℂ := ⟨|x.re|, |x.im|⟩
  let v : ℂ := ⟨|y.re|, |y.im|⟩
  have hu : ‖u‖ = ‖x‖ := by simp [u, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hv : ‖v‖ = ‖y‖ := by simp [v, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  calc
    |x.re| * |y.im| + |x.im| * |y.re| = (u * v).im := by
      simp [u, v, Complex.mul_im]
    _ ≤ ‖u * v‖ := Complex.im_le_norm _
    _ = ‖x‖ * ‖y‖ := by rw [norm_mul, hu, hv]

private lemma p04_norm_mk_le_three_halves
    {a b c : ℝ} (hc : 0 ≤ c) (ha : |a| ≤ c) (hb : |b| ≤ c) :
    ‖(⟨a, b⟩ : ℂ)‖ ≤ (3 / 2 : ℝ) * c := by
  have hbasic : ‖(⟨a, b⟩ : ℂ)‖ ≤ ‖(⟨c, c⟩ : ℂ)‖ :=
    p04_norm_mk_le_of_abs_le (by simpa [abs_of_nonneg hc] using ha)
      (by simpa [abs_of_nonneg hc] using hb)
  have heq : ‖(⟨c, c⟩ : ℂ)‖ = Real.sqrt 2 * c := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    convert Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (c ^ 2) using 1
    · ring
    · rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  calc
    ‖(⟨a, b⟩ : ℂ)‖ ≤ ‖(⟨c, c⟩ : ℂ)‖ := hbasic
    _ = Real.sqrt 2 * c := heq
    _ ≤ (3 / 2 : ℝ) * c := mul_le_mul_of_nonneg_right hsqrt hc

private lemma p04_flMul_abs_value (model : P04WilkinsonModel) (a b : ℝ) :
    |model.flMul a b| ≤ (1 + model.epsilon) * (|a| * |b|) := by
  have h := p04_flMul_abs_error model a b
  have htri := abs_add_le (a * b) (model.flMul a b - a * b)
  rw [show a * b + (model.flMul a b - a * b) = model.flMul a b by ring] at htri
  rw [abs_mul] at htri
  nlinarith

private lemma p04_roundedComplexMul_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (3 + 2 * model.epsilon) * (‖x‖ * ‖y‖) := by
  let A := model.flMul x.re y.re
  let B := model.flMul x.im y.im
  let C := model.flMul x.re y.im
  let D := model.flMul x.im y.re
  let v : ℂ := ⟨A - B, C + D⟩
  let P := ‖x‖ * ‖y‖
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hdiag : |x.re| * |y.re| + |x.im| * |y.im| ≤ P :=
    p04_abs_diag_products_le x y
  have hcross : |x.re| * |y.im| + |x.im| * |y.re| ≤ P :=
    p04_abs_cross_products_le x y
  have hA := p04_flMul_abs_error model x.re y.re
  have hB := p04_flMul_abs_error model x.im y.im
  have hC := p04_flMul_abs_error model x.re y.im
  have hD := p04_flMul_abs_error model x.im y.re
  have hAval := p04_flMul_abs_value model x.re y.re
  have hBval := p04_flMul_abs_value model x.im y.im
  have hCval := p04_flMul_abs_value model x.re y.im
  have hDval := p04_flMul_abs_value model x.im y.re
  have hsumdiag : |A| + |B| ≤ (1 + model.epsilon) * P := by
    have hfirst : |A| + |B| ≤
        (1 + model.epsilon) *
          (|x.re| * |y.re| + |x.im| * |y.im|) := by
      dsimp [A, B]
      nlinarith [hAval, hBval]
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left hdiag (by linarith))
  have hsumcross : |C| + |D| ≤ (1 + model.epsilon) * P := by
    have hfirst : |C| + |D| ≤
        (1 + model.epsilon) *
          (|x.re| * |y.im| + |x.im| * |y.re|) := by
      dsimp [C, D]
      nlinarith [hCval, hDval]
    exact hfirst.trans
      (mul_le_mul_of_nonneg_left hcross (by linarith))
  have hA' : |A - x.re * y.re| ≤ model.epsilon * (|x.re| * |y.re|) := hA
  have hB' : |B - x.im * y.im| ≤ model.epsilon * (|x.im| * |y.im|) := hB
  have hC' : |C - x.re * y.im| ≤ model.epsilon * (|x.re| * |y.im|) := hC
  have hD' : |D - x.im * y.re| ≤ model.epsilon * (|x.im| * |y.re|) := hD
  have hmultre : |(v - x * y).re| ≤ model.epsilon * P := by
    have htri := abs_add_le (A - x.re * y.re) (-(B - x.im * y.im))
    have heq : (v - x * y).re =
        (A - x.re * y.re) + -(B - x.im * y.im) := by
      simp [v, A, B, Complex.mul_re]; ring
    rw [heq]
    rw [abs_neg] at htri
    nlinarith
  have hmultim : |(v - x * y).im| ≤ model.epsilon * P := by
    have htri := abs_add_le (C - x.re * y.im) (D - x.im * y.re)
    have heq : (v - x * y).im =
        (C - x.re * y.im) + (D - x.im * y.re) := by
      simp [v, C, D, Complex.mul_im]; ring
    rw [heq]
    nlinarith
  have hmult : ‖v - x * y‖ ≤ (3 / 2 : ℝ) * (model.epsilon * P) :=
    p04_norm_mk_le_three_halves (mul_nonneg he hP)
      (by simpa using hmultre) (by simpa using hmultim)
  have haddre :
      |(p04RoundedComplexMul model x y - v).re| ≤
        model.epsilon * (1 + model.epsilon) * P := by
    have hadd := p04_flAdd_abs_error model A (-B)
    have heq : (p04RoundedComplexMul model x y - v).re =
        model.flAdd A (-B) - (A + -B) := by
      simp [p04RoundedComplexMul, v, A, B]; ring
    rw [heq]
    rw [abs_neg] at hadd
    exact hadd.trans (mul_le_mul_of_nonneg_left hsumdiag he) |>.trans (by ring_nf; rfl)
  have haddim :
      |(p04RoundedComplexMul model x y - v).im| ≤
        model.epsilon * (1 + model.epsilon) * P := by
    have hadd := p04_flAdd_abs_error model C D
    have heq : (p04RoundedComplexMul model x y - v).im =
        model.flAdd C D - (C + D) := by
      simp [p04RoundedComplexMul, v, C, D]
    rw [heq]
    exact hadd.trans (mul_le_mul_of_nonneg_left hsumcross he) |>.trans (by ring_nf; rfl)
  have hadd : ‖p04RoundedComplexMul model x y - v‖ ≤
      (3 / 2 : ℝ) * (model.epsilon * (1 + model.epsilon) * P) :=
    p04_norm_mk_le_three_halves
      (by positivity) (by simpa using haddre) (by simpa using haddim)
  have htri := norm_add_le
    (p04RoundedComplexMul model x y - v) (v - x * y)
  rw [show p04RoundedComplexMul model x y - v + (v - x * y) =
      p04RoundedComplexMul model x y - x * y by abel] at htri
  nlinarith [mul_nonneg (sq_nonneg model.epsilon) hP]

private lemma p04_stdAddChar_eq_angle {q : ℕ} [NeZero q] (j : ZMod q) :
    ZMod.stdAddChar j =
      (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ) := by
  rw [p04StdAddChar_positive_exp]
  have hangle :
      2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ) =
        (p04RootAngle j : ℂ) * Complex.I := by
    push_cast [p04RootAngle]
    ring
  rw [hangle, Complex.exp_mul_I]
  apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

private lemma p04_flCos_abs_error (model : P04WilkinsonModel) (a : ℝ) :
    |model.flCos a - Real.cos a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, h⟩ := model.cos_model a
  rw [h, show Real.cos a + model.gamma * θ * model.epsilon - Real.cos a =
    model.gamma * θ * model.epsilon by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_pos model.epsilon_pos]
  calc
    model.gamma * |θ| * model.epsilon ≤
        model.gamma * 1 * model.epsilon :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ model.gamma_nonneg)
        (le_of_lt model.epsilon_pos)
    _ = model.gamma * model.epsilon := by ring

private lemma p04_flSin_abs_error (model : P04WilkinsonModel) (a : ℝ) :
    |model.flSin a - Real.sin a| ≤ model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, h⟩ := model.sin_model a
  rw [h, show Real.sin a + model.gamma * θ * model.epsilon - Real.sin a =
    model.gamma * θ * model.epsilon by ring]
  rw [abs_mul, abs_mul, abs_of_nonneg model.gamma_nonneg,
    abs_of_pos model.epsilon_pos]
  calc
    model.gamma * |θ| * model.epsilon ≤
        model.gamma * 1 * model.epsilon :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hθ model.gamma_nonneg)
        (le_of_lt model.epsilon_pos)
    _ = model.gamma * model.epsilon := by ring

private lemma p04_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      (3 / 2 : ℝ) * (model.gamma * model.epsilon) := by
  rw [p04_stdAddChar_eq_angle]
  apply p04_norm_mk_le_three_halves
  · exact mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos)
  · simpa [p04RoundedRoot] using p04_flCos_abs_error model (p04RootAngle j)
  · simpa [p04RoundedRoot] using p04_flSin_abs_error model (p04RootAngle j)

private lemma p04_stdAddChar_norm {q : ℕ} [NeZero q] (j : ZMod q) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

private lemma p04_roundedRoot_norm {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤
      1 + (3 / 2 : ℝ) * (model.gamma * model.epsilon) := by
  have htri := norm_add_le
    (p04RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
  rw [sub_add_cancel, p04_stdAddChar_norm] at htri
  linarith [p04_roundedRoot_error model j]

private lemma p04_roundedRootMul_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) (x : ℂ) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      model.epsilon *
        ((3 + 2 * model.epsilon) *
            (1 + (3 / 2 : ℝ) * (model.gamma * model.epsilon)) +
          (3 / 2 : ℝ) * model.gamma) * ‖x‖ := by
  let r := p04RoundedRoot model j
  let z := ZMod.stdAddChar j
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hmul := p04_roundedComplexMul_error model r x
  have hroot := p04_roundedRoot_error model j
  have hrnorm := p04_roundedRoot_norm model j
  have hstep : ‖r * x - z * x‖ ≤
      ((3 / 2 : ℝ) * (model.gamma * model.epsilon)) * ‖x‖ := by
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hroot hx
  have htri := norm_add_le
    (p04RoundedComplexMul model r x - r * x) (r * x - z * x)
  rw [show p04RoundedComplexMul model r x - r * x + (r * x - z * x) =
      p04RoundedComplexMul model r x - z * x by abel] at htri
  have hfactor : 0 ≤ model.epsilon * (3 + 2 * model.epsilon) := by positivity
  have hmul' : ‖p04RoundedComplexMul model r x - r * x‖ ≤
      model.epsilon * (3 + 2 * model.epsilon) *
        (1 + (3 / 2 : ℝ) * (model.gamma * model.epsilon)) * ‖x‖ := by
    calc
      _ ≤ model.epsilon * (3 + 2 * model.epsilon) * (‖r‖ * ‖x‖) := hmul
      _ ≤ model.epsilon * (3 + 2 * model.epsilon) *
            ((1 + (3 / 2 : ℝ) * (model.gamma * model.epsilon)) * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrnorm hx) hfactor
      _ = _ := by ring
  dsimp [r, z] at *
  nlinarith [htri, hstep, hmul']

private noncomputable def p04RoundedComplexRecursive (model : P04WilkinsonModel) :
    (n : ℕ) → (Fin n → ℂ) → ℂ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then v ⟨0, by omega⟩
      else p04RoundedComplexAdd model
        (p04RoundedComplexRecursive model n (fun i => v i.castSucc))
        (v (Fin.last n))

private lemma p04RoundedComplexRecursive_re (model : P04WilkinsonModel) :
    ∀ n (v : Fin n → ℂ),
      (p04RoundedComplexRecursive model n v).re =
        recursiveSum model.flAdd n (fun i => (v i).re) := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
      intro v
      simp only [p04RoundedComplexRecursive, recursiveSum]
      split_ifs with h
      · rfl
      · simp [p04RoundedComplexAdd, ih]

private lemma p04RoundedComplexRecursive_im (model : P04WilkinsonModel) :
    ∀ n (v : Fin n → ℂ),
      (p04RoundedComplexRecursive model n v).im =
        recursiveSum model.flAdd n (fun i => (v i).im) := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih =>
      intro v
      simp only [p04RoundedComplexRecursive, recursiveSum]
      split_ifs with h
      · rfl
      · simp [p04RoundedComplexAdd, ih]

private lemma p04RoundedComplexSum_eq_recursive {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    p04RoundedComplexSum model term =
      p04RoundedComplexRecursive model q
        (fun i => term ((ZMod.finEquiv q).toEquiv i)) := by
  apply Complex.ext
  · exact (p04RoundedComplexRecursive_re model q _).symm
  · exact (p04RoundedComplexRecursive_im model q _).symm

private lemma p04RoundedComplexRecursive_error (model : P04WilkinsonModel) :
    ∀ n (v : Fin (n + 1) → ℂ),
      ‖p04RoundedComplexRecursive model (n + 1) v - ∑ i, v i‖ ≤
        ((1 + model.epsilon) ^ n - 1) * (∑ i, ‖v i‖) := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [p04RoundedComplexRecursive]
  | succ n ih =>
      intro v
      let w : Fin (n + 1) → ℂ := fun i => v i.castSucc
      let z : ℂ := v (Fin.last (n + 1))
      let r : ℂ := p04RoundedComplexRecursive model (n + 1) w
      let s : ℂ := ∑ i, w i
      let S : ℝ := ∑ i, ‖w i‖
      let t : ℝ := ‖z‖
      let c : ℝ := (1 + model.epsilon) ^ n - 1
      have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hc : 0 ≤ c := by
        dsimp [c]
        linarith [one_le_pow₀ (show (1 : ℝ) ≤ 1 + model.epsilon by linarith) (n := n)]
      have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have ht : 0 ≤ t := norm_nonneg _
      have hrec : ‖r - s‖ ≤ c * S := ih w
      have hsum : (∑ i : Fin (n + 2), v i) = s + z := by
        simp [s, z, w, Fin.sum_univ_castSucc]
      have hnormr : ‖r‖ ≤ S + c * S := by
        have htri := norm_add_le (r - s) s
        rw [sub_add_cancel] at htri
        have hnorms : ‖s‖ ≤ S := by
          simpa [s, S] using norm_sum_le Finset.univ w
        linarith
      have hadd := p04_roundedComplexAdd_error model r z
      have hstep :
          p04RoundedComplexRecursive model (n + 2) v =
            p04RoundedComplexAdd model r z := by
        simp [p04RoundedComplexRecursive, r, z, w]
      have htri :
          ‖p04RoundedComplexRecursive model (n + 2) v - (s + z)‖ ≤
            ‖p04RoundedComplexAdd model r z - (r + z)‖ + ‖r - s‖ := by
        rw [hstep]
        have h := norm_add_le
          (p04RoundedComplexAdd model r z - (r + z)) (r - s)
        convert h using 1 <;> congr 1 <;> abel
      have hpow : 1 ≤ (1 + model.epsilon) ^ n :=
        one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + model.epsilon)
      have hcoeff : model.epsilon ≤
          (1 + model.epsilon) ^ (n + 1) - 1 := by
        rw [pow_succ]
        nlinarith [mul_nonneg he (sub_nonneg.mpr hpow)]
      have hgoal :
          ‖p04RoundedComplexRecursive model (n + 2) v - (s + z)‖ ≤
            ((1 + model.epsilon) ^ (n + 1) - 1) * (S + t) := by
        have h1 : ‖p04RoundedComplexAdd model r z - (r + z)‖ ≤
            model.epsilon * (S + c * S + t) := by
          calc
            _ ≤ model.epsilon * (‖r‖ + ‖z‖) := hadd
            _ ≤ model.epsilon * (S + c * S + t) := by
              apply mul_le_mul_of_nonneg_left _ he
              dsimp [t]
              linarith
        have h2 : ((1 + model.epsilon) ^ (n + 1) - 1) =
            c + model.epsilon * (1 + c) := by
          dsimp [c]
          rw [pow_succ]
          ring
        rw [h2]
        have h3 : 0 ≤ c + model.epsilon * (1 + c) - model.epsilon := by
          nlinarith [mul_nonneg he hc]
        nlinarith [mul_nonneg h3 ht]
      simpa [hsum, Fin.sum_univ_castSucc, S, t] using hgoal

private lemma p04RoundedComplexSum_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j, term j‖ ≤
      ((1 + model.epsilon) ^ (q - 1) - 1) * (∑ j, ‖term j‖) := by
  cases q with
  | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
  | succ n =>
      rw [p04RoundedComplexSum_eq_recursive]
      simpa only [Nat.add_sub_cancel,
        Equiv.sum_comp (ZMod.finEquiv (n + 1)).toEquiv]
        using p04RoundedComplexRecursive_error model n
          (fun i => term ((ZMod.finEquiv (n + 1)).toEquiv i))

private lemma p04_radixTwo_coefficient_eq (j : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change p04RadixTwoCoefficientApply (0 : ZMod 2) x =
        ZMod.stdAddChar (0 : ZMod 2) * x
    have hz : ZMod.stdAddChar (0 : ZMod 2) = 1 :=
      (ZMod.stdAddChar : AddChar (ZMod 2) ℂ).map_zero_eq_one
    simp [p04RadixTwoCoefficientApply, hz]
  · have hangle : p04RootAngle (1 : ZMod 2) = Real.pi := by
      have hval : (1 : ZMod 2).val = 1 := by decide
      simp [p04RootAngle, hval]
    change p04RadixTwoCoefficientApply (1 : ZMod 2) x =
      ZMod.stdAddChar (1 : ZMod 2) * x
    rw [p04_stdAddChar_eq_angle, hangle]
    simp only [Real.cos_pi, Real.sin_pi]
    have hne : (1 : ZMod 2) ≠ 0 := by decide
    simp only [p04RadixTwoCoefficientApply, if_neg hne]
    have hm : (⟨-1, 0⟩ : ℂ) = -1 := by
      apply Complex.ext <;> norm_num
    rw [hm]
    ring

private lemma p04_radixFour_coefficient_eq (j : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  have hchar0 : ZMod.stdAddChar (0 : ZMod 4) = 1 :=
    (ZMod.stdAddChar : AddChar (ZMod 4) ℂ).map_zero_eq_one
  have hchar1 : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
    rw [p04_stdAddChar_eq_angle]
    have hangle : p04RootAngle (1 : ZMod 4) = Real.pi / 2 := by
      have hval : (1 : ZMod 4).val = 1 := by decide
      simp [p04RootAngle, hval]
      ring
    rw [hangle, Real.cos_pi_div_two, Real.sin_pi_div_two]
    apply Complex.ext <;> norm_num
  have hchar2 : ZMod.stdAddChar (2 : ZMod 4) = -1 := by
    have htwo : (2 : ZMod 4) = 1 + 1 := by decide
    rw [htwo, AddChar.map_add_eq_mul, hchar1]
    norm_num
  have hchar3 : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
    have hthree : (3 : ZMod 4) = 2 + 1 := by decide
    rw [hthree, AddChar.map_add_eq_mul, hchar2, hchar1]
    ring
  fin_cases j
  · change p04RadixFourCoefficientApply (0 : ZMod 4) x =
      ZMod.stdAddChar (0 : ZMod 4) * x
    rw [hchar0]
    simp only [p04RadixFourCoefficientApply, one_mul, if_true]
  · change p04RadixFourCoefficientApply (1 : ZMod 4) x =
      ZMod.stdAddChar (1 : ZMod 4) * x
    rw [hchar1]
    have hne : (1 : ZMod 4) ≠ 0 := by decide
    simp only [p04RadixFourCoefficientApply, if_neg hne, if_true]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

  · change p04RadixFourCoefficientApply (2 : ZMod 4) x =
      ZMod.stdAddChar (2 : ZMod 4) * x
    rw [hchar2]
    have h20 : (2 : ZMod 4) ≠ 0 := by decide
    have h21 : (2 : ZMod 4) ≠ 1 := by decide
    simp only [p04RadixFourCoefficientApply, if_neg h20, if_neg h21,
      if_true]
    ring
  · change p04RadixFourCoefficientApply (3 : ZMod 4) x =
      ZMod.stdAddChar (3 : ZMod 4) * x
    rw [hchar3]
    have h30 : (3 : ZMod 4) ≠ 0 := by decide
    have h31 : (3 : ZMod 4) ≠ 1 := by decide
    have h32 : (3 : ZMod 4) ≠ 2 := by decide
    simp only [p04RadixFourCoefficientApply, if_neg h30, if_neg h31,
      if_neg h32]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private lemma p04_roundedRadixTwoBlock_error (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  simp_rw [p04RoundedRadixTwoBlock, p04_radixTwo_coefficient_eq]
  have h := p04RoundedComplexSum_error model
    (fun j : ZMod 2 => ZMod.stdAddChar (j * k) * x j)
  simpa [p04_stdAddChar_norm] using h

private lemma p04_roundedAddTree_error (model : P04WilkinsonModel)
    (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) - ((a + b) + (c + d))‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  let S := ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hu := p04_roundedComplexAdd_error model a b
  have hv := p04_roundedComplexAdd_error model c d
  have huv := p04_roundedComplexAdd_error model u v
  have hunorm : ‖u‖ ≤ (1 + model.epsilon) * (‖a‖ + ‖b‖) := by
    have h := norm_add_le (u - (a + b)) (a + b)
    rw [sub_add_cancel] at h
    have hab := norm_add_le a b
    dsimp [u] at *
    nlinarith
  have hvnorm : ‖v‖ ≤ (1 + model.epsilon) * (‖c‖ + ‖d‖) := by
    have h := norm_add_le (v - (c + d)) (c + d)
    rw [sub_add_cancel] at h
    have hcd := norm_add_le c d
    dsimp [v] at *
    nlinarith
  have hinner : ‖(u + v) - ((a + b) + (c + d))‖ ≤
      model.epsilon * S := by
    have h := norm_add_le (u - (a + b)) (v - (c + d))
    rw [show u - (a + b) + (v - (c + d)) =
        (u + v) - ((a + b) + (c + d)) by abel] at h
    dsimp [u, v] at *
    nlinarith
  have htri := norm_add_le
    (p04RoundedComplexAdd model u v - (u + v))
    ((u + v) - ((a + b) + (c + d)))
  rw [show p04RoundedComplexAdd model u v - (u + v) +
      ((u + v) - ((a + b) + (c + d))) =
      p04RoundedComplexAdd model u v - ((a + b) + (c + d)) by abel] at htri
  have houter : ‖p04RoundedComplexAdd model u v - (u + v)‖ ≤
      model.epsilon * (1 + model.epsilon) * S := by
    have hnorm : ‖u‖ + ‖v‖ ≤ (1 + model.epsilon) * S := by
      dsimp [S]
      nlinarith [hunorm, hvnorm]
    calc
      _ ≤ model.epsilon * (‖u‖ + ‖v‖) := huv
      _ ≤ model.epsilon * ((1 + model.epsilon) * S) :=
        mul_le_mul_of_nonneg_left hnorm he
      _ = _ := by ring
  dsimp [u, v] at *
  nlinarith

private lemma p04_roundedRadixFourBlock_error (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (∑ j : ZMod 4, ‖x j‖) := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let term : Fin 4 → ℂ := fun i =>
    p04RadixFourCoefficientApply (index i * k) (x (index i))
  have hterm (i : Fin 4) :
      term i = ZMod.stdAddChar (index i * k) * x (index i) := by
    exact p04_radixFour_coefficient_eq (index i * k) (x (index i))
  have hsum : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      (term 0 + term 1) + (term 2 + term 3) := by
    rw [← Equiv.sum_comp index]
    simp_rw [← hterm]
    simp [Fin.sum_univ_succ]
    ring
  have hnorm : (∑ j : ZMod 4, ‖x j‖) =
      ‖term 0‖ + ‖term 1‖ + ‖term 2‖ + ‖term 3‖ := by
    rw [← Equiv.sum_comp index]
    have htnorm (i : Fin 4) : ‖term i‖ = ‖x (index i)‖ := by
      rw [hterm, norm_mul, p04_stdAddChar_norm, one_mul]
    simp_rw [← htnorm]
    simp [Fin.sum_univ_succ]
    ring
  rw [hsum, hnorm]
  exact p04_roundedAddTree_error model (term 0) (term 1) (term 2) (term 3)

private noncomputable def p04RootMulCoeff (model : P04WilkinsonModel) : ℝ :=
  model.epsilon *
    ((3 + 2 * model.epsilon) *
        (1 + (3 / 2 : ℝ) * (model.gamma * model.epsilon)) +
      (3 / 2 : ℝ) * model.gamma)

private lemma p04RootMulCoeff_nonneg (model : P04WilkinsonModel) :
    0 ≤ p04RootMulCoeff model := by
  have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hg : 0 ≤ model.gamma := model.gamma_nonneg
  unfold p04RootMulCoeff
  positivity

private lemma p04_roundedGenericRadixBlock_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p04RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (((1 + model.epsilon) ^ (q - 1) - 1) *
          (1 + p04RootMulCoeff model) + p04RootMulCoeff model) *
        (∑ j : ZMod q, ‖x j‖) := by
  let u : ZMod q → ℂ := fun j =>
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let v : ZMod q → ℂ := fun j => ZMod.stdAddChar (j * k) * x j
  let δ := p04RootMulCoeff model
  let A := (1 + model.epsilon) ^ (q - 1) - 1
  let S := ∑ j : ZMod q, ‖x j‖
  have hδ : 0 ≤ δ := p04RootMulCoeff_nonneg model
  have hA : 0 ≤ A := by
    dsimp [A]
    linarith [one_le_pow₀
      (show (1 : ℝ) ≤ 1 + model.epsilon by linarith [model.epsilon_pos])
      (n := q - 1)]
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlocal (j : ZMod q) : ‖u j - v j‖ ≤ δ * ‖x j‖ := by
    exact p04_roundedRootMul_error model (j * k) (x j)
  have hunorm (j : ZMod q) : ‖u j‖ ≤ (1 + δ) * ‖x j‖ := by
    have htri := norm_add_le (u j - v j) (v j)
    rw [sub_add_cancel, show ‖v j‖ = ‖x j‖ by
      simp [v, p04_stdAddChar_norm]] at htri
    nlinarith [hlocal j]
  have hsumerr : ‖∑ j : ZMod q, u j - ∑ j : ZMod q, v j‖ ≤ δ * S := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j : ZMod q, ‖u j - v j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, δ * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => hlocal j
      _ = δ * S := by simp [S, Finset.mul_sum]
  have hsumunorm : (∑ j : ZMod q, ‖u j‖) ≤ (1 + δ) * S := by
    calc
      _ ≤ ∑ j : ZMod q, (1 + δ) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => hunorm j
      _ = (1 + δ) * S := by simp [S, Finset.mul_sum]
  have hround := p04RoundedComplexSum_error model u
  have htri := norm_add_le
    (p04RoundedComplexSum model u - ∑ j, u j)
    ((∑ j, u j) - ∑ j, v j)
  rw [show p04RoundedComplexSum model u - ∑ j, u j +
      ((∑ j, u j) - ∑ j, v j) =
      p04RoundedComplexSum model u - ∑ j, v j by abel] at htri
  have hround' : ‖p04RoundedComplexSum model u - ∑ j, u j‖ ≤
      A * ((1 + δ) * S) := hround.trans
    (mul_le_mul_of_nonneg_left hsumunorm hA)
  dsimp [p04RoundedGenericRadixBlock, u, v, A, δ, S] at *
  nlinarith

private lemma p04_block_norm_bound {α β : Type*} [Fintype α] [Fintype β]
    (x e : α × β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ a b, ‖e (a, b)‖ ≤ C * ∑ j : β, ‖x (a, j)‖) :
    Real.sqrt (∑ p : α × β, ‖e p‖ ^ 2) ≤
      (Fintype.card β : ℝ) * C *
        Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := by
  let q : ℝ := Fintype.card β
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hqc : 0 ≤ q * C := mul_nonneg hq hC
  have hsquare : (∑ p : α × β, ‖e p‖ ^ 2) ≤
      (q * C) ^ 2 * ∑ p : α × β, ‖x p‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ a : α, ∑ b : β, ‖e (a, b)‖ ^ 2) ≤
          ∑ a : α, (q * C) ^ 2 * ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        let S : ℝ := ∑ j : β, ‖x (a, j)‖
        have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
        have hsq : S ^ 2 ≤ q * ∑ j : β, ‖x (a, j)‖ ^ 2 := by
          simpa [S, q] using
            (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset β)) (f := fun j => ‖x (a, j)‖))
        calc
          (∑ b : β, ‖e (a, b)‖ ^ 2) ≤
              ∑ b : β, (C * S) ^ 2 := by
            apply Finset.sum_le_sum
            intro b _
            exact sq_le_sq.mpr (by
              rw [abs_of_nonneg (norm_nonneg _),
                abs_of_nonneg (mul_nonneg hC hS)]
              exact hpoint a b)
          _ = q * (C * S) ^ 2 := by simp [q]
          _ = (q * C ^ 2) * S ^ 2 := by ring
          _ ≤ (q * C ^ 2) * (q * ∑ j : β, ‖x (a, j)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (q * C) ^ 2 * ∑ j : β, ‖x (a, j)‖ ^ 2 := by ring
      _ = (q * C) ^ 2 * ∑ a : α, ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        rw [Finset.mul_sum]
  have hxsum : 0 ≤ ∑ p : α × β, ‖x p‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    Real.sqrt (∑ p : α × β, ‖e p‖ ^ 2) ≤
        Real.sqrt ((q * C) ^ 2 * ∑ p : α × β, ‖x p‖ ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = q * C * Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg (q * C)), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hqc]
    _ = (Fintype.card β : ℝ) * C *
          Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := rfl

private noncomputable def p04RadixBlockCoeff
    (model : P04WilkinsonModel) (q : ℕ) : ℝ :=
  if q = 2 then model.epsilon
  else if q = 4 then model.epsilon * (2 + model.epsilon)
  else ((1 + model.epsilon) ^ (q - 1) - 1) *
      (1 + p04RootMulCoeff model) + p04RootMulCoeff model

private lemma p04RadixBlockCoeff_nonneg (model : P04WilkinsonModel)
    (q : ℕ) : 0 ≤ p04RadixBlockCoeff model q := by
  unfold p04RadixBlockCoeff
  split_ifs
  · exact le_of_lt model.epsilon_pos
  · have he : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
    positivity
  · have hA : 0 ≤ (1 + model.epsilon) ^ (q - 1) - 1 := by
      linarith [one_le_pow₀
        (show (1 : ℝ) ≤ 1 + model.epsilon by linarith [model.epsilon_pos])
        (n := q - 1)]
    have hδ := p04RootMulCoeff_nonneg model
    positivity

private lemma p04_roundedRadixTwoBlock_error_cast {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (hq : q = 2)
    (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p04RoundedRadixTwoBlock model (fun j : ZMod 2 => x (hq.symm ▸ j))
        (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod q, ‖x j‖ := by
  cases hq
  simpa using p04_roundedRadixTwoBlock_error model x k

private lemma p04_roundedRadixFourBlock_error_cast {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (hq : q = 4)
    (x : ZMod q → ℂ) (k : ZMod q) :
    ‖p04RoundedRadixFourBlock model (fun j : ZMod 4 => x (hq.symm ▸ j))
        (hq ▸ k) -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 + model.epsilon) *
        ∑ j : ZMod q, ‖x j‖ := by
  cases hq
  simpa using p04_roundedRadixFourBlock_error model x k

private lemma p04_roundedMixedRadixBlock_pointwise {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (i : ZMod n) :
    ‖p04RoundedMixedRadixBlockApply model stage x i -
        p04MixedRadixBlockApply stage x i‖ ≤
      p04RadixBlockCoeff model stage.radix *
        ∑ j : ZMod stage.radix,
          ‖x (stage.permutation
            (stage.reindex ((stage.reindex.symm i).1, j)))‖ := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let bi := stage.reindex.symm i
  by_cases h2 : stage.radix = 2
  · simp only [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
      dif_pos h2, p04RadixBlockCoeff, if_pos h2]
    exact p04_roundedRadixTwoBlock_error_cast model h2
      (fun j : ZMod stage.radix =>
        x (stage.permutation (stage.reindex (bi.1, j)))) bi.2
  · by_cases h4 : stage.radix = 4
    · simp only [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
        dif_neg h2, dif_pos h4, p04RadixBlockCoeff, if_neg h2,
        if_pos h4]
      exact p04_roundedRadixFourBlock_error_cast model h4
        (fun j : ZMod stage.radix =>
          x (stage.permutation (stage.reindex (bi.1, j)))) bi.2
    · simp only [p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
        dif_neg h2, dif_neg h4, p04RadixBlockCoeff,
        if_neg h2, if_neg h4]
      exact p04_roundedGenericRadixBlock_error model
        (fun j => x (stage.permutation (stage.reindex (bi.1, j)))) bi.2

private lemma p04_roundedMixedRadixBlock_norm {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i) ≤
      (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix *
        p04ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let f : ZMod n → ℂ := fun i =>
    p04RoundedMixedRadixBlockApply model stage x i -
      p04MixedRadixBlockApply stage x i
  let e : Fin stage.blockCount × ZMod stage.radix → ℂ :=
    fun p => f (stage.reindex p)
  let v : Fin stage.blockCount × ZMod stage.radix → ℂ :=
    fun p => x (stage.permutation (stage.reindex p))
  have hpoint (a : Fin stage.blockCount) (b : ZMod stage.radix) :
      ‖e (a, b)‖ ≤ p04RadixBlockCoeff model stage.radix *
        ∑ j : ZMod stage.radix, ‖v (a, j)‖ := by
    simpa [e, v, f] using
      p04_roundedMixedRadixBlock_pointwise model stage x (stage.reindex (a, b))
  have h := p04_block_norm_bound v e
    (p04RadixBlockCoeff model stage.radix)
    (p04RadixBlockCoeff_nonneg model stage.radix) hpoint
  have heqE : (∑ p : Fin stage.blockCount × ZMod stage.radix,
      ‖e p‖ ^ 2) = ∑ i : ZMod n, ‖f i‖ ^ 2 := by
    exact Equiv.sum_comp stage.reindex (fun i => ‖f i‖ ^ 2)
  have heqV : (∑ p : Fin stage.blockCount × ZMod stage.radix,
      ‖v p‖ ^ 2) = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
    calc
      _ = ∑ i : ZMod n, ‖x (stage.permutation i)‖ ^ 2 :=
        Equiv.sum_comp stage.reindex _
      _ = ∑ i : ZMod n, ‖x i‖ ^ 2 :=
        Equiv.sum_comp stage.permutation (fun i => ‖x i‖ ^ 2)
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq, f, heqE, heqV] using h

private lemma p04_sqrt_sum_sq_pointwise {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hpoint : ∀ i, ‖x i‖ ≤ C * ‖y i‖) :
    Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤
      C * Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
  have hsquare : (∑ i, ‖x i‖ ^ 2) ≤ C ^ 2 * (∑ i, ‖y i‖ ^ 2) := by
    calc
      _ ≤ ∑ i, (C * ‖y i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq.mpr (by
          rw [abs_of_nonneg (norm_nonneg _),
            abs_of_nonneg (mul_nonneg hC (norm_nonneg _))]
          exact hpoint i)
      _ = C ^ 2 * (∑ i, ‖y i‖ ^ 2) := by
        simp [Finset.mul_sum]
        ring
  calc
    Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤
        Real.sqrt (C ^ 2 * ∑ i, ‖y i‖ ^ 2) :=
      Real.sqrt_le_sqrt hsquare
    _ = C * Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hC]

private lemma p04ComplexNorm2_triangle {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i => x i + y i) ≤
      p04ComplexNorm2 x + p04ComplexNorm2 y := by
  let X : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 y
  have hX : p04ComplexNorm2 x = ‖X‖ := by
    simp [p04ComplexNorm2, p04ComplexNorm2Sq, EuclideanSpace.norm_eq, X]
  have hY : p04ComplexNorm2 y = ‖Y‖ := by
    simp [p04ComplexNorm2, p04ComplexNorm2Sq, EuclideanSpace.norm_eq, Y]
  have hXY : p04ComplexNorm2 (fun i => x i + y i) = ‖X + Y‖ := by
    simp [p04ComplexNorm2, p04ComplexNorm2Sq, EuclideanSpace.norm_eq, X, Y]
  rw [hX, hY, hXY]
  exact norm_add_le X Y

private lemma p04_exactTwiddle_norm {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) =
      p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [p04MixedRadixTwiddleApply]
  split_ifs
  · simp [p04_stdAddChar_norm]
  · rfl

private lemma p04_roundedTwiddle_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i) ≤
      (if stage.useTwiddle then p04RootMulCoeff model else 0) *
        p04ComplexNorm2 x := by
  by_cases h : stage.useTwiddle = true
  · have hpoint (i : ZMod n) :
        ‖p04RoundedMixedRadixTwiddleApply model stage x i -
            p04MixedRadixTwiddleApply stage x i‖ ≤
          p04RootMulCoeff model * ‖x i‖ := by
      simpa [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, h, p04RootMulCoeff] using
        p04_roundedRootMul_error model (stage.twiddleExponent i) (x i)
    simpa [h, p04ComplexNorm2, p04ComplexNorm2Sq] using
      (p04_sqrt_sum_sq_pointwise
        (fun i => p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i)
        x (p04RootMulCoeff model) (p04RootMulCoeff_nonneg model) hpoint)
  · have hf : stage.useTwiddle = false := Bool.eq_false_iff.mpr h
    simp [p04RoundedMixedRadixTwiddleApply,
      p04MixedRadixTwiddleApply, hf, p04ComplexNorm2,
      p04ComplexNorm2Sq]

private lemma p04_exactTwiddle_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    (fun i => p04MixedRadixTwiddleApply stage x i -
      p04MixedRadixTwiddleApply stage y i) =
        p04MixedRadixTwiddleApply stage (fun i => x i - y i) := by
  funext i
  by_cases h : stage.useTwiddle = true
  · simp [p04MixedRadixTwiddleApply, h, mul_sub]
  · have hf : stage.useTwiddle = false := Bool.eq_false_iff.mpr h
    simp [p04MixedRadixTwiddleApply, hf]

private lemma p04_roundedMixedRadixStage_norm {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ)
    (hscale : p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
      Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x) :
    p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixStageApply model stage x i -
          p04MixedRadixStageApply stage x i) ≤
      ((stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix +
        (if stage.useTwiddle then p04RootMulCoeff model else 0) *
          (Real.sqrt (stage.radix : ℝ) +
            (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix)) *
        p04ComplexNorm2 x := by
  let y := p04RoundedMixedRadixBlockApply model stage x
  let z := p04MixedRadixBlockApply stage x
  let B := (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix
  let δ := if stage.useTwiddle then p04RootMulCoeff model else 0
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Nat.cast_nonneg _) (p04RadixBlockCoeff_nonneg model _)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    split_ifs <;> positivity [p04RootMulCoeff_nonneg model]
  have hx : 0 ≤ p04ComplexNorm2 x := by
    unfold p04ComplexNorm2
    positivity
  have hblock : p04ComplexNorm2 (fun i => y i - z i) ≤
      B * p04ComplexNorm2 x :=
    p04_roundedMixedRadixBlock_norm model stage x
  have hz : p04ComplexNorm2 z =
      Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x := by
    rw [← p04_exactTwiddle_norm stage z]
    exact hscale
  have hynorm : p04ComplexNorm2 y ≤
      (Real.sqrt (stage.radix : ℝ) + B) * p04ComplexNorm2 x := by
    have ht := p04ComplexNorm2_triangle (fun i => y i - z i) z
    have heq : (fun i => (y i - z i) + z i) = y := by funext i; ring
    rw [heq, hz] at ht
    nlinarith
  have htwid : p04ComplexNorm2 (fun i =>
      p04RoundedMixedRadixTwiddleApply model stage y i -
        p04MixedRadixTwiddleApply stage y i) ≤
      δ * p04ComplexNorm2 y := p04_roundedTwiddle_error model stage y
  have hlin : p04ComplexNorm2 (fun i =>
      p04MixedRadixTwiddleApply stage y i -
        p04MixedRadixTwiddleApply stage z i) =
      p04ComplexNorm2 (fun i => y i - z i) := by
    rw [p04_exactTwiddle_sub, p04_exactTwiddle_norm]
  have htri := p04ComplexNorm2_triangle
    (fun i => p04RoundedMixedRadixTwiddleApply model stage y i -
      p04MixedRadixTwiddleApply stage y i)
    (fun i => p04MixedRadixTwiddleApply stage y i -
      p04MixedRadixTwiddleApply stage z i)
  have heq : (fun i =>
      (p04RoundedMixedRadixTwiddleApply model stage y i -
      p04MixedRadixTwiddleApply stage y i) +
      (p04MixedRadixTwiddleApply stage y i -
      p04MixedRadixTwiddleApply stage z i)) =
    (fun i => p04RoundedMixedRadixStageApply model stage x i -
      p04MixedRadixStageApply stage x i) := by
    funext i
    simp [p04RoundedMixedRadixStageApply, p04MixedRadixStageApply, y, z]
  rw [heq, hlin] at htri
  dsimp [B, δ] at *
  nlinarith [mul_le_mul_of_nonneg_left hynorm hδ]

private lemma p04_mixedRadixBlock_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    (fun i => p04MixedRadixBlockApply stage x i -
      p04MixedRadixBlockApply stage y i) =
        p04MixedRadixBlockApply stage (fun i => x i - y i) := by
  funext i
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  simp [p04MixedRadixBlockApply, mul_sub, Finset.sum_sub_distrib]

private lemma p04_mixedRadixStage_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    (fun i => p04MixedRadixStageApply stage x i -
      p04MixedRadixStageApply stage y i) =
        p04MixedRadixStageApply stage (fun i => x i - y i) := by
  rw [p04MixedRadixStageApply, p04MixedRadixStageApply,
    p04MixedRadixStageApply, p04_exactTwiddle_sub,
    p04_mixedRadixBlock_sub]

private noncomputable def p04StageCoeff (model : P04WilkinsonModel)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n) : ℝ :=
  let a := Real.sqrt (stage.radix : ℝ) *
    p04RadixBlockCoeff model stage.radix
  a + (if stage.useTwiddle then p04RootMulCoeff model else 0) * (1 + a)

private lemma p04StageCoeff_nonneg (model : P04WilkinsonModel)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n) :
    0 ≤ p04StageCoeff model stage := by
  unfold p04StageCoeff
  have hroot := p04RootMulCoeff_nonneg model
  have hblock := p04RadixBlockCoeff_nonneg model stage.radix
  split_ifs <;> positivity

private lemma p04_roundedMixedRadixStage_rel {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ)
    (hscale : p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
      Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x) :
    p04ComplexNorm2 (fun i =>
        p04RoundedMixedRadixStageApply model stage x i -
          p04MixedRadixStageApply stage x i) ≤
      p04StageCoeff model stage *
        p04ComplexNorm2 (p04MixedRadixStageApply stage x) := by
  have h := p04_roundedMixedRadixStage_norm model stage x hscale
  rw [hscale]
  unfold p04StageCoeff
  have hq : (Real.sqrt (stage.radix : ℝ)) ^ 2 = (stage.radix : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hresult :
      ((stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix +
        (if stage.useTwiddle then p04RootMulCoeff model else 0) *
          (Real.sqrt (stage.radix : ℝ) +
            (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix)) *
        p04ComplexNorm2 x =
      (Real.sqrt (stage.radix : ℝ) *
          p04RadixBlockCoeff model stage.radix +
        (if stage.useTwiddle then p04RootMulCoeff model else 0) *
          (1 + Real.sqrt (stage.radix : ℝ) *
            p04RadixBlockCoeff model stage.radix)) *
        (Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x) := by
    have hscalar :
        (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix +
          (if stage.useTwiddle then p04RootMulCoeff model else 0) *
            (Real.sqrt (stage.radix : ℝ) +
              (stage.radix : ℝ) * p04RadixBlockCoeff model stage.radix) =
        (Real.sqrt (stage.radix : ℝ) *
            p04RadixBlockCoeff model stage.radix +
          (if stage.useTwiddle then p04RootMulCoeff model else 0) *
            (1 + Real.sqrt (stage.radix : ℝ) *
              p04RadixBlockCoeff model stage.radix)) *
          Real.sqrt (stage.radix : ℝ) := by
      calc
        _ = (Real.sqrt (stage.radix : ℝ)) ^ 2 *
              p04RadixBlockCoeff model stage.radix +
            (if stage.useTwiddle then p04RootMulCoeff model else 0) *
              (Real.sqrt (stage.radix : ℝ) +
                (Real.sqrt (stage.radix : ℝ)) ^ 2 *
                  p04RadixBlockCoeff model stage.radix) := by rw [hq]
        _ = _ := by ring
    calc
      _ = ((Real.sqrt (stage.radix : ℝ) *
              p04RadixBlockCoeff model stage.radix +
            (if stage.useTwiddle then p04RootMulCoeff model else 0) *
              (1 + Real.sqrt (stage.radix : ℝ) *
                p04RadixBlockCoeff model stage.radix)) *
            Real.sqrt (stage.radix : ℝ)) * p04ComplexNorm2 x := by
        rw [hscalar]
      _ = _ := by ring
  exact hresult ▸ h

private structure P04BoundedStep (V : Type*) [AddCommGroup V]
    (N : V → ℝ) where
  exactApply : V → V
  roundedApply : V → V
  scale : ℝ
  coeff : ℝ
  scale_nonneg : 0 ≤ scale
  coeff_nonneg : 0 ≤ coeff
  exact_sub : ∀ x y, exactApply (x - y) = exactApply x - exactApply y
  exact_scale : ∀ x, N (exactApply x) = scale * N x
  local_error : ∀ x, N (roundedApply x - exactApply x) ≤ coeff * N (exactApply x)

private noncomputable def p04StepExactFold {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) (x : V) : V :=
  steps.foldl (fun state step => step.exactApply state) x

private noncomputable def p04StepRoundedFold {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) (x : V) : V :=
  steps.foldl (fun state step => step.roundedApply state) x

private noncomputable def p04StepScaleProduct {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) : ℝ :=
  (steps.map (fun step => step.scale)).prod

private noncomputable def p04StepErrorProduct {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) : ℝ :=
  (steps.map (fun step => 1 + step.coeff)).prod

private lemma p04StepScaleProduct_nonneg {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) :
    0 ≤ p04StepScaleProduct steps := by
  induction steps with
  | nil => simp [p04StepScaleProduct]
  | cons step steps ih =>
      simp only [p04StepScaleProduct, List.map_cons, List.prod_cons]
      exact mul_nonneg step.scale_nonneg ih

private lemma p04StepErrorProduct_one_le {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) :
    1 ≤ p04StepErrorProduct steps := by
  induction steps with
  | nil => simp [p04StepErrorProduct]
  | cons step steps ih =>
      simp only [p04StepErrorProduct, List.map_cons, List.prod_cons]
      exact one_le_mul_of_one_le_of_one_le (by linarith [step.coeff_nonneg]) ih

private lemma P04BoundedStep.two_input {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (htriangle : ∀ x y, N (x + y) ≤ N x + N y)
    (step : P04BoundedStep V N) (x y : V) :
    N (step.roundedApply x - step.exactApply y) ≤
      step.scale * ((1 + step.coeff) * N (x - y) +
        step.coeff * N y) := by
  have hlin : step.exactApply x - step.exactApply y =
      step.exactApply (x - y) := (step.exact_sub x y).symm
  have hexactnorm : N (step.exactApply x) ≤
      step.scale * (N (x - y) + N y) := by
    have h := htriangle
      (step.exactApply x - step.exactApply y) (step.exactApply y)
    rw [sub_add_cancel, hlin] at h
    calc
      _ ≤ N (step.exactApply (x - y)) + N (step.exactApply y) := h
      _ = _ := by rw [step.exact_scale, step.exact_scale]; ring
  have hlocal := step.local_error x
  have htri := htriangle
    (step.roundedApply x - step.exactApply x)
    (step.exactApply x - step.exactApply y)
  rw [show step.roundedApply x - step.exactApply x +
      (step.exactApply x - step.exactApply y) =
      step.roundedApply x - step.exactApply y by abel,
    hlin, step.exact_scale] at htri
  have hbound := mul_le_mul_of_nonneg_left hexactnorm step.coeff_nonneg
  nlinarith

private lemma p04StepFold_error {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (htriangle : ∀ x y, N (x + y) ≤ N x + N y)
    (steps : List (P04BoundedStep V N)) (x y : V) :
    N (p04StepRoundedFold steps x - p04StepExactFold steps y) ≤
      p04StepScaleProduct steps *
        (p04StepErrorProduct steps * N (x - y) +
          (p04StepErrorProduct steps - 1) * N y) := by
  induction steps generalizing x y with
  | nil => simp [p04StepRoundedFold, p04StepExactFold,
      p04StepScaleProduct, p04StepErrorProduct]
  | cons step steps ih =>
      have hfirst := step.two_input htriangle x y
      have htail := ih (step.roundedApply x) (step.exactApply y)
      have hP : 0 ≤ p04StepErrorProduct steps :=
        le_trans zero_le_one (p04StepErrorProduct_one_le steps)
      have hQ : 0 ≤ p04StepScaleProduct steps :=
        p04StepScaleProduct_nonneg steps
      have hmul := mul_le_mul_of_nonneg_left hfirst hP
      have hbound :
          p04StepErrorProduct steps *
              N (step.roundedApply x - step.exactApply y) +
            (p04StepErrorProduct steps - 1) *
              N (step.exactApply y) ≤
          p04StepErrorProduct steps *
              (step.scale *
                ((1 + step.coeff) * N (x - y) +
                  step.coeff * N y)) +
            (p04StepErrorProduct steps - 1) *
              (step.scale * N y) := by
        rw [step.exact_scale]
        linarith
      have htail' := htail.trans
        (mul_le_mul_of_nonneg_left hbound hQ)
      dsimp [p04StepScaleProduct, p04StepErrorProduct] at htail'
      simp only [p04StepRoundedFold, p04StepExactFold,
        p04StepScaleProduct, p04StepErrorProduct,
        List.foldl_cons, List.map_cons, List.prod_cons] at ⊢
      convert htail' using 1 <;> ring

private noncomputable def p04FftStageStep {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (i : Fin plan.stageCount) :
    P04BoundedStep (ZMod n → ℂ) p04ComplexNorm2 where
  exactApply := p04MixedRadixStageApply (plan.stage i)
  roundedApply := p04RoundedMixedRadixStageApply model (plan.stage i)
  scale := Real.sqrt ((plan.stage i).radix : ℝ)
  coeff := p04StageCoeff model (plan.stage i)
  scale_nonneg := Real.sqrt_nonneg _
  coeff_nonneg := p04StageCoeff_nonneg model (plan.stage i)
  exact_sub := by
    intro x y
    exact (p04_mixedRadixStage_sub (plan.stage i) x y).symm
  exact_scale := plan.stage_norm_scaling i
  local_error := by
    intro x
    exact p04_roundedMixedRadixStage_rel model (plan.stage i) x
      (plan.stage_norm_scaling i x)

private lemma p04FftStageStep_roundedFold {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) :
    p04StepRoundedFold (List.ofFn (p04FftStageStep plan model)) x =
      p04ApplyRoundedMixedRadixStages model plan.stage x := by
  unfold p04StepRoundedFold p04ApplyRoundedMixedRadixStages
  have h1 : List.ofFn (p04FftStageStep plan model) =
      (List.ofFn (fun i : Fin plan.stageCount => i)).map
        (p04FftStageStep plan model) := by
    simpa using (List.ofFn_comp' (fun i : Fin plan.stageCount => i)
      (p04FftStageStep plan model))
  have h2 : List.ofFn plan.stage =
      (List.ofFn (fun i : Fin plan.stageCount => i)).map plan.stage := by
    simpa using (List.ofFn_comp' (fun i : Fin plan.stageCount => i) plan.stage)
  rw [h1, h2]
  simp only [List.foldl_map]
  congr 1

private lemma p04FftStageStep_exactFold {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) :
    p04StepExactFold (List.ofFn (p04FftStageStep plan model)) x =
      p04ApplyMixedRadixStages plan.stage x := by
  unfold p04StepExactFold p04ApplyMixedRadixStages
  have h1 : List.ofFn (p04FftStageStep plan model) =
      (List.ofFn (fun i : Fin plan.stageCount => i)).map
        (p04FftStageStep plan model) := by
    simpa using (List.ofFn_comp' (fun i : Fin plan.stageCount => i)
      (p04FftStageStep plan model))
  have h2 : List.ofFn plan.stage =
      (List.ofFn (fun i : Fin plan.stageCount => i)).map plan.stage := by
    simpa using (List.ofFn_comp' (fun i : Fin plan.stageCount => i) plan.stage)
  rw [h1, h2]
  simp only [List.foldl_map]
  congr 1

private lemma p04StepExactFold_scale {V : Type*} [AddCommGroup V]
    {N : V → ℝ} (steps : List (P04BoundedStep V N)) (x : V) :
    N (p04StepExactFold steps x) = p04StepScaleProduct steps * N x := by
  induction steps generalizing x with
  | nil => simp [p04StepExactFold, p04StepScaleProduct]
  | cons step steps ih =>
      simp only [p04StepExactFold, p04StepScaleProduct,
        List.foldl_cons, List.map_cons, List.prod_cons]
      rw [← p04StepExactFold, ih, step.exact_scale]
      dsimp [p04StepScaleProduct]
      ring

private lemma p04_complexNorm_perm {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04Permute permutation x) = p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq p04Permute
  congr 1
  exact Equiv.sum_comp permutation (fun i => ‖x i‖ ^ 2)

private lemma p04_complexNorm_perm_sub {n : ℕ} [NeZero n]
    (permutation : ZMod n ≃ ZMod n) (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
      p04Permute permutation x i - p04Permute permutation y i) =
      p04ComplexNorm2 (fun i => x i - y i) := by
  simpa [p04Permute] using
    p04_complexNorm_perm permutation (fun i => x i - y i)

private lemma p04_roundedFft_norm_product_bound {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
      p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
      (p04StepErrorProduct
          (List.ofFn (p04FftStageStep plan model)) - 1) *
        p04ComplexNorm2 (p04FourierTransform x) := by
  let steps := List.ofFn (p04FftStageStep plan model)
  have hfold := p04StepFold_error p04ComplexNorm2_triangle steps x x
  have hscale := p04StepExactFold_scale steps x
  have hfact := plan.exact_factorization x
  have hrounded := p04FftStageStep_roundedFold plan model x
  have hexact := p04FftStageStep_exactFold plan model x
  have hperm := p04_complexNorm_perm_sub plan.finalPermutation
    (p04StepRoundedFold steps x) (p04StepExactFold steps x)
  have hnormfact : p04ComplexNorm2 (p04FourierTransform x) =
      p04ComplexNorm2 (p04StepExactFold steps x) := by
    rw [← hfact, ← hexact]
    exact p04_complexNorm_perm plan.finalPermutation _
  have hbase : p04ComplexNorm2
      (fun i => p04StepRoundedFold steps x i - p04StepExactFold steps x i) ≤
      (p04StepErrorProduct steps - 1) *
        p04ComplexNorm2 (p04StepExactFold steps x) := by
    have hzero : (x - x : ZMod n → ℂ) = 0 := sub_self x
    rw [hzero] at hfold
    have hnormzero : p04ComplexNorm2 (0 : ZMod n → ℂ) = 0 := by
      simp [p04ComplexNorm2, p04ComplexNorm2Sq]
    rw [hnormzero, mul_zero, zero_add] at hfold
    calc
      _ ≤ p04StepScaleProduct steps *
            ((p04StepErrorProduct steps - 1) * p04ComplexNorm2 x) := hfold
      _ = (p04StepErrorProduct steps - 1) *
            p04ComplexNorm2 (p04StepExactFold steps x) := by
        rw [hscale]
        ring
  calc
    p04ComplexNorm2 (fun i =>
        p04RoundedFftApply plan model x i - p04FourierTransform x i) =
      p04ComplexNorm2 (fun i =>
        p04Permute plan.finalPermutation (p04StepRoundedFold steps x) i -
          p04Permute plan.finalPermutation (p04StepExactFold steps x) i) := by
      congr 1
      funext i
      simp only [p04RoundedFftApply]
      rw [← hfact, ← hexact, ← hrounded]
    _ = p04ComplexNorm2 (fun i =>
          p04StepRoundedFold steps x i - p04StepExactFold steps x i) := hperm
    _ ≤ (p04StepErrorProduct steps - 1) *
          p04ComplexNorm2 (p04StepExactFold steps x) := hbase
    _ = (p04StepErrorProduct steps - 1) *
          p04ComplexNorm2 (p04FourierTransform x) := by rw [hnormfact]

private abbrev p04OtherIndex {m : ℕ} (axis : Fin m → P04FftAxis)
    (i : Fin m) :=
  (j : {j : Fin m // j ≠ i}) → ZMod (axis j).order

private def p04MultiIndexEquiv {m : ℕ} (axis : Fin m → P04FftAxis)
    (i : Fin m) :
    (p04OtherIndex axis i × ZMod (axis i).order) ≃ P04MultiIndex axis :=
  (Equiv.prodComm (p04OtherIndex axis i) (ZMod (axis i).order)).trans
    (Equiv.piSplitAt i (fun j => ZMod (axis j).order)).symm

private lemma p04MultiIndexEquiv_apply_axis {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (other : p04OtherIndex axis i) (z : ZMod (axis i).order) :
    p04MultiIndexEquiv axis i (other, z) i = z := by
  simp [p04MultiIndexEquiv, Equiv.piSplitAt]

private lemma p04MultiIndexEquiv_update {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (other : p04OtherIndex axis i) (z w : ZMod (axis i).order) :
    Function.update (p04MultiIndexEquiv axis i (other, z)) i w =
      p04MultiIndexEquiv axis i (other, w) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [p04MultiIndexEquiv_apply_axis]
  · simp [p04MultiIndexEquiv, Equiv.piSplitAt, Function.update, h]

private lemma p04_coordinate_slice {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) (other : p04OtherIndex axis i)
    (z : ZMod (axis i).order) :
    p04CoordinateTransform axis i x (p04MultiIndexEquiv axis i (other, z)) =
      p04FourierTransform
        (fun w => x (p04MultiIndexEquiv axis i (other, w))) z := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp [p04CoordinateTransform, p04FourierTransform,
    p04MultiIndexEquiv_apply_axis, p04MultiIndexEquiv_update]

private lemma p04_rounded_coordinate_slice {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis)
    (other : p04OtherIndex axis i) (z : ZMod (axis i).order) :
    p04RoundedCoordinateTransform axis i model x
        (p04MultiIndexEquiv axis i (other, z)) =
      p04RoundedFftApply (axis i).plan model
        (fun w => x (p04MultiIndexEquiv axis i (other, w))) z := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp [p04RoundedCoordinateTransform,
    p04MultiIndexEquiv_apply_axis, p04MultiIndexEquiv_update]

private lemma p04_fiber_norm_bound {α β : Type*} [Fintype α] [Fintype β]
    (x e : α × β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfiber : ∀ a,
      Real.sqrt (∑ b : β, ‖e (a, b)‖ ^ 2) ≤
        C * Real.sqrt (∑ b : β, ‖x (a, b)‖ ^ 2)) :
    Real.sqrt (∑ p : α × β, ‖e p‖ ^ 2) ≤
      C * Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := by
  have hsq : (∑ p : α × β, ‖e p‖ ^ 2) ≤
      C ^ 2 * ∑ p : α × β, ‖x p‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ a : α, ∑ b : β, ‖e (a, b)‖ ^ 2) ≤
          ∑ a : α, C ^ 2 * ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        have hE : 0 ≤ ∑ b : β, ‖e (a, b)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hX : 0 ≤ ∑ b : β, ‖x (a, b)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h :
            (Real.sqrt (∑ b : β, ‖e (a, b)‖ ^ 2)) ^ 2 ≤
              (C * Real.sqrt (∑ b : β, ‖x (a, b)‖ ^ 2)) ^ 2 :=
          sq_le_sq.mpr (by
          rw [abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (mul_nonneg hC (Real.sqrt_nonneg _))]
          exact hfiber a)
        rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hX] at h
        exact h
      _ = C ^ 2 * ∑ a : α, ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        rw [Finset.mul_sum]
  calc
    Real.sqrt (∑ p : α × β, ‖e p‖ ^ 2) ≤
        Real.sqrt (C ^ 2 * ∑ p : α × β, ‖x p‖ ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = C * Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hC]

private lemma p04MultiNorm2_eq_sqrt_sum {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x = Real.sqrt (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
  unfold p04MultiNorm2
  simp [EuclideanSpace.norm_eq]

private lemma p04_roundedCoordinate_norm_product_bound {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis) :
    p04MultiNorm2 (fun index =>
        p04RoundedCoordinateTransform axis i model x index -
          p04CoordinateTransform axis i x index) ≤
      (p04StepErrorProduct
          (List.ofFn (p04FftStageStep (axis i).plan model)) - 1) *
        p04MultiNorm2 (p04CoordinateTransform axis i x) := by
  letI (j : Fin m) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  let e := p04MultiIndexEquiv axis i
  let C := p04StepErrorProduct
    (List.ofFn (p04FftStageStep (axis i).plan model)) - 1
  let error : p04OtherIndex axis i × ZMod (axis i).order → ℂ :=
    fun p => p04RoundedCoordinateTransform axis i model x (e p) -
      p04CoordinateTransform axis i x (e p)
  let exact : p04OtherIndex axis i × ZMod (axis i).order → ℂ :=
    fun p => p04CoordinateTransform axis i x (e p)
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [p04StepErrorProduct_one_le
      (List.ofFn (p04FftStageStep (axis i).plan model))]
  have hfiber (other : p04OtherIndex axis i) :
      Real.sqrt (∑ z : ZMod (axis i).order, ‖error (other, z)‖ ^ 2) ≤
        C * Real.sqrt (∑ z : ZMod (axis i).order,
          ‖exact (other, z)‖ ^ 2) := by
    let slice : ZMod (axis i).order → ℂ := fun z => x (e (other, z))
    have h := p04_roundedFft_norm_product_bound (axis i).plan model slice
    simpa [p04ComplexNorm2, p04ComplexNorm2Sq, error, exact,
      C, slice, e, p04_coordinate_slice,
      p04_rounded_coordinate_slice] using h
  have h := p04_fiber_norm_bound exact error C hC hfiber
  have heqError : (∑ p : p04OtherIndex axis i × ZMod (axis i).order,
      ‖error p‖ ^ 2) =
      ∑ index : P04MultiIndex axis,
        ‖p04RoundedCoordinateTransform axis i model x index -
          p04CoordinateTransform axis i x index‖ ^ 2 := by
    exact Equiv.sum_comp e (fun index =>
      ‖p04RoundedCoordinateTransform axis i model x index -
        p04CoordinateTransform axis i x index‖ ^ 2)
  have heqExact : (∑ p : p04OtherIndex axis i × ZMod (axis i).order,
      ‖exact p‖ ^ 2) =
      ∑ index : P04MultiIndex axis,
        ‖p04CoordinateTransform axis i x index‖ ^ 2 := by
    exact Equiv.sum_comp e (fun index =>
      ‖p04CoordinateTransform axis i x index‖ ^ 2)
  simpa [p04MultiNorm2_eq_sqrt_sum, heqError, heqExact,
    error, exact, C] using h

private lemma p04_fiber_norm_scale {α β : Type*} [Fintype α] [Fintype β]
    (x y : α × β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hfiber : ∀ a,
      Real.sqrt (∑ b : β, ‖y (a, b)‖ ^ 2) =
        C * Real.sqrt (∑ b : β, ‖x (a, b)‖ ^ 2)) :
    Real.sqrt (∑ p : α × β, ‖y p‖ ^ 2) =
      C * Real.sqrt (∑ p : α × β, ‖x p‖ ^ 2) := by
  have hsq : (∑ p : α × β, ‖y p‖ ^ 2) =
      C ^ 2 * ∑ p : α × β, ‖x p‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ a : α, ∑ b : β, ‖y (a, b)‖ ^ 2) =
          ∑ a : α, C ^ 2 * ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        have hE : 0 ≤ ∑ b : β, ‖y (a, b)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hX : 0 ≤ ∑ b : β, ‖x (a, b)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h := congrArg (fun t : ℝ => t ^ 2) (hfiber a)
        change (Real.sqrt (∑ b : β, ‖y (a, b)‖ ^ 2)) ^ 2 =
          (C * Real.sqrt (∑ b : β, ‖x (a, b)‖ ^ 2)) ^ 2 at h
        rw [mul_pow, Real.sq_sqrt hE, Real.sq_sqrt hX] at h
        exact h
      _ = C ^ 2 * ∑ a : α, ∑ b : β, ‖x (a, b)‖ ^ 2 := by
        rw [Finset.mul_sum]
  rw [hsq, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hC]

private lemma p04_fft_norm_scaling {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04FourierTransform x) =
      Real.sqrt (n : ℝ) * p04ComplexNorm2 x := by
  have h := plan.fourier_rms_scaling x
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 (NeZero.pos n)))
  unfold p04ComplexRms at h
  apply (div_left_inj' hs).mp
  simpa [mul_div_assoc] using h

private lemma p04_coordinate_norm_scaling {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04MultiNorm2 (p04CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p04MultiNorm2 x := by
  letI (j : Fin m) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  let e := p04MultiIndexEquiv axis i
  let exact : p04OtherIndex axis i × ZMod (axis i).order → ℂ :=
    fun p => p04CoordinateTransform axis i x (e p)
  let input : p04OtherIndex axis i × ZMod (axis i).order → ℂ :=
    fun p => x (e p)
  have hfiber (other : p04OtherIndex axis i) :
      Real.sqrt (∑ z : ZMod (axis i).order, ‖exact (other, z)‖ ^ 2) =
        Real.sqrt ((axis i).order : ℝ) *
          Real.sqrt (∑ z : ZMod (axis i).order,
            ‖input (other, z)‖ ^ 2) := by
    let slice : ZMod (axis i).order → ℂ := fun z => x (e (other, z))
    have h := p04_fft_norm_scaling (axis i).plan slice
    simpa [p04ComplexNorm2, p04ComplexNorm2Sq, exact,
      input, slice, e, p04_coordinate_slice] using h
  have h := p04_fiber_norm_scale input exact
    (Real.sqrt ((axis i).order : ℝ)) (Real.sqrt_nonneg _) hfiber
  have heqExact : (∑ p : p04OtherIndex axis i × ZMod (axis i).order,
      ‖exact p‖ ^ 2) =
      ∑ index : P04MultiIndex axis,
        ‖p04CoordinateTransform axis i x index‖ ^ 2 := by
    exact Equiv.sum_comp e (fun index =>
      ‖p04CoordinateTransform axis i x index‖ ^ 2)
  have heqInput : (∑ p : p04OtherIndex axis i × ZMod (axis i).order,
      ‖input p‖ ^ 2) =
      ∑ index : P04MultiIndex axis, ‖x index‖ ^ 2 := by
    exact Equiv.sum_comp e (fun index => ‖x index‖ ^ 2)
  simpa [p04MultiNorm2_eq_sqrt_sum, heqExact, heqInput,
    exact, input] using h

private lemma p04MultiNorm2_triangle {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 (x + y) ≤ p04MultiNorm2 x + p04MultiNorm2 y := by
  let X : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 y
  have hX : p04MultiNorm2 x = ‖X‖ := by rfl
  have hY : p04MultiNorm2 y = ‖Y‖ := by rfl
  have hXY : p04MultiNorm2 (x + y) = ‖X + Y‖ := by rfl
  rw [hX, hY, hXY]
  exact norm_add_le X Y

private lemma p04CoordinateTransform_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) :
    p04CoordinateTransform axis i (x - y) =
      p04CoordinateTransform axis i x -
        p04CoordinateTransform axis i y := by
  funext index
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp [p04CoordinateTransform, mul_sub, Finset.sum_sub_distrib]

private noncomputable def p04MultiStep {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (model : P04WilkinsonModel) (i : Fin m) :
    P04BoundedStep (P04MultiArray plan.axis) p04MultiNorm2 where
  exactApply := p04CoordinateTransform plan.axis i
  roundedApply := p04RoundedCoordinateTransform plan.axis i model
  scale := Real.sqrt ((plan.axis i).order : ℝ)
  coeff := p04StepErrorProduct
    (List.ofFn (p04FftStageStep (plan.axis i).plan model)) - 1
  scale_nonneg := Real.sqrt_nonneg _
  coeff_nonneg := by
    linarith [p04StepErrorProduct_one_le
      (List.ofFn (p04FftStageStep (plan.axis i).plan model))]
  exact_sub := p04CoordinateTransform_sub plan.axis i
  exact_scale := p04_coordinate_norm_scaling plan.axis i
  local_error := p04_roundedCoordinate_norm_product_bound plan.axis i model

private lemma p04_exact_coordinate_fold {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P04MultiArray axis) :
    (List.ofFn (fun i : Fin k => Fin.castLE hk i)).foldr
      (fun i state => p04CoordinateTransform axis i state) x =
      p04ApplyCoordinatePrefix axis k x := by
  induction k generalizing x with
  | zero => simp [p04ApplyCoordinatePrefix]
  | succ k ih =>
      have hk' : k ≤ m := by omega
      have hklt : k < m := by omega
      rw [List.ofFn_succ']
      have hlist :
          (List.ofFn
              (fun i : Fin k => Fin.castLE hk i.castSucc)) =
            List.ofFn (fun i : Fin k => Fin.castLE hk' i) := by
        congr 1
      rw [hlist]
      have hlast : Fin.castLE hk (Fin.last k) = ⟨k, hklt⟩ := rfl
      rw [hlast, List.concat_eq_append, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      rw [ih]
      simp [p04ApplyCoordinatePrefix, p04CoordinateTransformNat, hklt]

private lemma p04_run_coordinate_fold {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (model : P04WilkinsonModel)
    (run : P04MultidimensionalFftRun plan model)
    (k : ℕ) (hk : k ≤ m) :
    (List.ofFn (fun i : Fin k => Fin.castLE hk i)).foldr
      (fun i state => p04RoundedCoordinateTransform plan.axis i model state)
      (run.computedState ⟨k, by omega⟩) = run.computedState 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ m := by omega
      have hklt : k < m := by omega
      rw [List.ofFn_succ']
      have hlist :
          (List.ofFn (fun i : Fin k => Fin.castLE hk i.castSucc)) =
            List.ofFn (fun i : Fin k => Fin.castLE hk' i) := by
        congr 1
      rw [hlist]
      have hlast : Fin.castLE hk (Fin.last k) = ⟨k, hklt⟩ := rfl
      rw [hlast, List.concat_eq_append, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]
      have hstep := run.stage_step (⟨k, hklt⟩ : Fin m)
      have hstate :
          p04RoundedCoordinateTransform plan.axis ⟨k, hklt⟩ model
            (run.computedState ⟨k + 1, by omega⟩) =
          run.computedState ⟨k, by omega⟩ := by
        simpa using hstep.symm
      rw [hstate]
      exact ih hk'

private lemma p04MultiStep_roundedFold {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (model : P04WilkinsonModel)
    (run : P04MultidimensionalFftRun plan model) :
    p04StepRoundedFold (List.ofFn (p04MultiStep plan model)).reverse
      run.input = run.computedState 0 := by
  let steps := List.ofFn (p04MultiStep plan model)
  have hlist : steps =
      (List.ofFn (fun i : Fin m => i)).map (p04MultiStep plan model) := by
    simpa [steps] using
      (List.ofFn_comp' (fun i : Fin m => i) (p04MultiStep plan model))
  have hrun := p04_run_coordinate_fold plan model run m (le_refl m)
  rw [show run.computedState ⟨m, by omega⟩ = run.input by
    simpa using run.computed_input] at hrun
  unfold p04StepRoundedFold
  rw [← List.foldr_eq_foldl_reverse]
  dsimp [steps] at hlist
  rw [hlist, List.foldr_map]
  simpa using hrun

private lemma p04MultiStep_exactFold {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m)
    (model : P04WilkinsonModel)
    (x : P04MultiArray plan.axis) :
    p04StepExactFold (List.ofFn (p04MultiStep plan model)).reverse x =
      p04ApplyCoordinatePrefix plan.axis m x := by
  let steps := List.ofFn (p04MultiStep plan model)
  have hlist : steps =
      (List.ofFn (fun i : Fin m => i)).map (p04MultiStep plan model) := by
    simpa [steps] using
      (List.ofFn_comp' (fun i : Fin m => i) (p04MultiStep plan model))
  have hexact := p04_exact_coordinate_fold plan.axis m (le_refl m) x
  unfold p04StepExactFold
  rw [← List.foldr_eq_foldl_reverse]
  dsimp [steps] at hlist
  rw [hlist, List.foldr_map]
  simpa using hexact

private structure P04FirstOrder (f : ℝ → ℝ) (a : ℝ) where
  linear_nonneg : 0 ≤ a
  second : ℝ
  second_nonneg : 0 ≤ second
  bound : ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
    0 ≤ f u ∧ f u ≤ a * u + second * u ^ 2

private def P04FirstOrder.zero :
    P04FirstOrder (fun _ : ℝ => 0) 0 where
  linear_nonneg := le_refl _
  second := 0
  second_nonneg := le_refl _
  bound := by intro u hu hu1; simp

private def P04FirstOrder.identity :
    P04FirstOrder (fun u : ℝ => u) 1 where
  linear_nonneg := by norm_num
  second := 0
  second_nonneg := le_refl _
  bound := by intro u hu hu1; constructor <;> nlinarith

private def P04FirstOrder.add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : P04FirstOrder f a) (hg : P04FirstOrder g b) :
    P04FirstOrder (fun u => f u + g u) (a + b) where
  linear_nonneg := add_nonneg hf.linear_nonneg hg.linear_nonneg
  second := hf.second + hg.second
  second_nonneg := add_nonneg hf.second_nonneg hg.second_nonneg
  bound := by
    intro u hu hu1
    obtain ⟨hf0, hf1⟩ := hf.bound u hu hu1
    obtain ⟨hg0, hg1⟩ := hg.bound u hu hu1
    constructor <;> nlinarith

private def P04FirstOrder.scale {f : ℝ → ℝ} {a c : ℝ}
    (hc : 0 ≤ c) (hf : P04FirstOrder f a) :
    P04FirstOrder (fun u => c * f u) (c * a) where
  linear_nonneg := mul_nonneg hc hf.linear_nonneg
  second := c * hf.second
  second_nonneg := mul_nonneg hc hf.second_nonneg
  bound := by
    intro u hu hu1
    obtain ⟨hf0, hf1⟩ := hf.bound u hu hu1
    constructor
    · exact mul_nonneg hc hf0
    · have h := mul_le_mul_of_nonneg_left hf1 hc
      nlinarith

private def P04FirstOrder.product {f g : ℝ → ℝ} {a b : ℝ}
    (hf : P04FirstOrder f a) (hg : P04FirstOrder g b) :
    P04FirstOrder (fun u => f u + g u + f u * g u) (a + b) where
  linear_nonneg := add_nonneg hf.linear_nonneg hg.linear_nonneg
  second := hf.second + hg.second +
    (a + hf.second) * (b + hg.second)
  second_nonneg := by positivity [hf.linear_nonneg, hg.linear_nonneg,
    hf.second_nonneg, hg.second_nonneg]
  bound := by
    intro u hu hu1
    obtain ⟨hf0, hf1⟩ := hf.bound u hu hu1
    obtain ⟨hg0, hg1⟩ := hg.bound u hu hu1
    have hu2 : u ^ 2 ≤ u := by nlinarith [sq_nonneg u]
    have hfu : f u ≤ (a + hf.second) * u := by
      nlinarith [mul_le_mul_of_nonneg_left hu2 hf.second_nonneg]
    have hgu : g u ≤ (b + hg.second) * u := by
      nlinarith [mul_le_mul_of_nonneg_left hu2 hg.second_nonneg]
    have hprod : f u * g u ≤
        ((a + hf.second) * (b + hg.second)) * u ^ 2 := by
      have h := mul_le_mul hfu hgu hg0
        (by positivity [hf.linear_nonneg, hf.second_nonneg])
      nlinarith
    constructor
    · exact add_nonneg (add_nonneg hf0 hg0) (mul_nonneg hf0 hg0)
    · nlinarith

private def P04FirstOrder.weaken {f : ℝ → ℝ} {a b : ℝ}
    (hf : P04FirstOrder f a) (hab : a ≤ b) :
    P04FirstOrder f b where
  linear_nonneg := le_trans hf.linear_nonneg hab
  second := hf.second
  second_nonneg := hf.second_nonneg
  bound := by
    intro u hu hu1
    obtain ⟨hf0, hf1⟩ := hf.bound u hu hu1
    constructor
    · exact hf0
    · nlinarith [mul_le_mul_of_nonneg_right hab hu]

private noncomputable def p04PowErr (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ n - 1

private noncomputable def p04PowErr_firstOrder (n : ℕ) :
    P04FirstOrder (p04PowErr n) (n : ℝ) := by
  induction n with
  | zero =>
      have hfun : p04PowErr 0 = fun _ : ℝ => 0 := by
        funext u
        simp [p04PowErr]
      rw [hfun]
      simpa using P04FirstOrder.zero
  | succ n ih =>
      have h := P04FirstOrder.product ih P04FirstOrder.identity
      have hfun : (fun u : ℝ => p04PowErr n u + u +
          p04PowErr n u * u) = p04PowErr (n + 1) := by
        funext u
        simp [p04PowErr, pow_succ]
        ring
      rw [hfun] at h
      simpa using h

private noncomputable def p04RootMulCoeffValue (γ u : ℝ) : ℝ :=
  u * ((3 + 2 * u) * (1 + (3 / 2 : ℝ) * (γ * u)) +
    (3 / 2 : ℝ) * γ)

private noncomputable def p04RootMulCoeffValue_firstOrder (γ : ℝ) (hγ : 0 ≤ γ) :
    P04FirstOrder (p04RootMulCoeffValue γ)
      (3 + (3 / 2 : ℝ) * γ) where
  linear_nonneg := by positivity
  second := 2 + 8 * γ
  second_nonneg := by positivity
  bound := by
    intro u hu hu1
    have hu3 : u ^ 3 ≤ u ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
    have hγ3 := mul_le_mul_of_nonneg_left hu3 hγ
    unfold p04RootMulCoeffValue
    constructor
    · positivity
    · nlinarith [hγ3]

private noncomputable def p04RadixBlockCoeffValue (γ : ℝ)
    (q : ℕ) (u : ℝ) : ℝ :=
  if q = 2 then u
  else if q = 4 then u * (2 + u)
  else p04PowErr (q - 1) u * (1 + p04RootMulCoeffValue γ u) +
    p04RootMulCoeffValue γ u

private noncomputable def p04RadixBlockLinear (γ : ℝ) (q : ℕ) : ℝ :=
  if q = 2 then 1
  else if q = 4 then 2
  else ((q - 1 : ℕ) : ℝ) + 3 + (3 / 2 : ℝ) * γ

private noncomputable def p04RadixBlockCoeffValue_firstOrder
    (γ : ℝ) (hγ : 0 ≤ γ) (q : ℕ) :
    P04FirstOrder (p04RadixBlockCoeffValue γ q)
      (p04RadixBlockLinear γ q) := by
  by_cases h2 : q = 2
  · simpa [p04RadixBlockCoeffValue, p04RadixBlockLinear, h2] using
      P04FirstOrder.identity
  · by_cases h4 : q = 4
    · subst q
      change P04FirstOrder (fun u : ℝ => u * (2 + u)) 2
      refine ⟨by norm_num, 1, by norm_num, ?_⟩
      intro u hu hu1
      constructor
      · positivity
      · nlinarith
    · have h := P04FirstOrder.product
        (p04PowErr_firstOrder (q - 1))
        (p04RootMulCoeffValue_firstOrder γ hγ)
      have hfun :
          (fun u : ℝ => p04PowErr (q - 1) u +
              p04RootMulCoeffValue γ u +
              p04PowErr (q - 1) u * p04RootMulCoeffValue γ u) =
            p04RadixBlockCoeffValue γ q := by
        funext u
        simp [p04RadixBlockCoeffValue, h2, h4]
        ring
      rw [hfun] at h
      simpa [p04RadixBlockLinear, h2, h4, add_assoc] using h

private noncomputable def p04StageCoeffValue (γ : ℝ)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n)
    (u : ℝ) : ℝ :=
  let a := Real.sqrt (stage.radix : ℝ) *
    p04RadixBlockCoeffValue γ stage.radix u
  a + (if stage.useTwiddle then p04RootMulCoeffValue γ u else 0) *
    (1 + a)

private noncomputable def p04StageLinear (γ : ℝ)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n) : ℝ :=
  Real.sqrt (stage.radix : ℝ) * p04RadixBlockLinear γ stage.radix +
    (if stage.useTwiddle then 3 + (3 / 2 : ℝ) * γ else 0)

private noncomputable def p04StageCoeffValue_firstOrder
    (γ : ℝ) (hγ : 0 ≤ γ)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n) :
    P04FirstOrder (p04StageCoeffValue γ stage)
      (p04StageLinear γ stage) := by
  let a : ℝ → ℝ := fun u => Real.sqrt (stage.radix : ℝ) *
    p04RadixBlockCoeffValue γ stage.radix u
  let b : ℝ → ℝ := fun u =>
    if stage.useTwiddle then p04RootMulCoeffValue γ u else 0
  have ha : P04FirstOrder a
      (Real.sqrt (stage.radix : ℝ) * p04RadixBlockLinear γ stage.radix) :=
    P04FirstOrder.scale (Real.sqrt_nonneg _)
      (p04RadixBlockCoeffValue_firstOrder γ hγ stage.radix)
  have hb : P04FirstOrder b
      (if stage.useTwiddle then 3 + (3 / 2 : ℝ) * γ else 0) := by
    by_cases h : stage.useTwiddle = true
    · simpa [b, h] using p04RootMulCoeffValue_firstOrder γ hγ
    · have hf : stage.useTwiddle = false := Bool.eq_false_iff.mpr h
      simpa [b, hf] using P04FirstOrder.zero
  have h := P04FirstOrder.product ha hb
  have hfun : (fun u => a u + b u + a u * b u) =
      p04StageCoeffValue γ stage := by
    funext u
    by_cases htw : stage.useTwiddle = true
    · simp [a, b, p04StageCoeffValue, htw]
      ring
    · have hf : stage.useTwiddle = false := Bool.eq_false_iff.mpr htw
      simp [a, b, p04StageCoeffValue, hf]
  rw [hfun] at h
  simpa [p04StageLinear] using h

private lemma p04RadixBlockLinear_le_alpha (q : ℕ)
    (hq : 2 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    Real.sqrt (q : ℝ) * p04RadixBlockLinear γ q ≤ p04Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    simp [p04RadixBlockLinear, p04Alpha]
  · by_cases h4 : q = 4
    · subst q
      norm_num [p04RadixBlockLinear, p04Alpha, h2]
    · have hsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q)]
        norm_num
      have hlinear : p04RadixBlockLinear γ q ≤ 2 * ((q : ℝ) + γ) := by
        simp [p04RadixBlockLinear, h2, h4, hsub]
        have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hlinear
        (Real.sqrt_nonneg (q : ℝ))
      convert hmul using 1 <;> simp [p04Alpha, h2, h4] <;> ring

private lemma p04StageLinear_le_budget (γ : ℝ) (hγ : 0 ≤ γ)
    {n : ℕ} [NeZero n] (stage : P04MixedRadixStage n) :
    p04StageLinear γ stage ≤
      p04Alpha stage.radix γ +
        (if stage.useTwiddle then 3 + 2 * γ else 0) := by
  have hblock := p04RadixBlockLinear_le_alpha
    stage.radix stage.radix_two_le γ hγ
  unfold p04StageLinear
  by_cases h : stage.useTwiddle = true
  · simp [h]
    nlinarith
  · have hf : stage.useTwiddle = false := Bool.eq_false_iff.mpr h
    simpa [hf] using hblock

private noncomputable def p04FirstOrder_listProduct {α : Type*}
    (l : List α) (f : α → ℝ → ℝ) (a : α → ℝ)
    (h : ∀ i, P04FirstOrder (f i) (a i)) :
    P04FirstOrder
      (fun u => (l.map (fun i => 1 + f i u)).prod - 1)
      (l.map a).sum := by
  induction l with
  | nil =>
      simpa using P04FirstOrder.zero
  | cons i l ih =>
      let g : ℝ → ℝ := fun u => (l.map (fun j => 1 + f j u)).prod - 1
      have hproduct := P04FirstOrder.product (h i) ih
      have hfun :
          (fun u => f i u + g u + f i u * g u) =
            (fun u => ((i :: l).map (fun j => 1 + f j u)).prod - 1) := by
        funext u
        simp [g]
        ring
      rw [hfun] at hproduct
      simpa [List.map_cons, List.sum_cons, add_comm, add_left_comm,
        add_assoc] using hproduct

private lemma p04_listOfFn_sum : ∀ n (f : Fin n → ℝ),
    (List.ofFn f).sum = ∑ i : Fin n, f i := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
      intro f
      rw [List.ofFn_succ', List.sum_concat, Fin.sum_univ_castSucc]
      exact congrArg (fun t : ℝ => t + f (Fin.last n))
        (ih (fun i => f i.castSucc))

private lemma p04_listOfFn_prod : ∀ n (f : Fin n → ℝ),
    (List.ofFn f).prod = ∏ i : Fin n, f i := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
      intro f
      rw [List.ofFn_succ', List.prod_concat, Fin.prod_univ_castSucc]
      exact congrArg (fun t : ℝ => t * f (Fin.last n))
        (ih (fun i => f i.castSucc))

private lemma p04_twiddle_indicator_sum (s : ℕ) (hs : 0 < s)
    (t : ℝ) :
    (∑ i : Fin s, if i.val + 1 < s then t else 0) =
      ((s - 1 : ℕ) : ℝ) * t := by
  cases s with
  | zero => omega
  | succ k =>
      rw [Fin.sum_univ_castSucc]
      have hlt (i : Fin k) : i.castSucc.val + 1 < k + 1 := by
        simp
      simp [hlt]

private lemma p04_stage_budget_sum_eq_K {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    (∑ i : Fin plan.stageCount,
      (p04Alpha (plan.stage i).radix γ +
        (if (plan.stage i).useTwiddle = true then 3 + 2 * γ else 0))) =
      p04K plan γ := by
  rw [Finset.sum_add_distrib]
  have htwiddle :
      (∑ i : Fin plan.stageCount,
        if (plan.stage i).useTwiddle = true then 3 + 2 * γ else 0) =
      ((plan.stageCount - 1 : ℕ) : ℝ) * (3 + 2 * γ) := by
    simp_rw [plan.twiddle_pattern]
    simpa using p04_twiddle_indicator_sum plan.stageCount
      plan.stageCount_pos (3 + 2 * γ)
  rw [htwiddle]
  unfold p04K
  congr 1
  have hcast : ((plan.stageCount - 1 : ℕ) : ℝ) =
      (plan.stageCount : ℝ) - 1 := by
    rw [Nat.cast_sub (by have hp := plan.stageCount_pos; omega : 1 ≤ plan.stageCount)]
    norm_num
  rw [hcast]

private noncomputable def p04FftCoeffValue {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ u : ℝ) : ℝ :=
  (∏ i : Fin plan.stageCount,
    (1 + p04StageCoeffValue γ (plan.stage i) u)) - 1

private noncomputable def p04FftCoeffValue_firstOrder {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    P04FirstOrder (p04FftCoeffValue plan γ) (p04K plan γ) := by
  let f : Fin plan.stageCount → ℝ → ℝ :=
    fun i => p04StageCoeffValue γ (plan.stage i)
  let a : Fin plan.stageCount → ℝ :=
    fun i => p04StageLinear γ (plan.stage i)
  have hlist := p04FirstOrder_listProduct
    (List.ofFn (fun i : Fin plan.stageCount => i)) f a
    (fun i => p04StageCoeffValue_firstOrder γ hγ (plan.stage i))
  have hlinear : (∑ i : Fin plan.stageCount, a i) ≤ p04K plan γ := by
    calc
      _ ≤ ∑ i : Fin plan.stageCount,
          (p04Alpha (plan.stage i).radix γ +
            if (plan.stage i).useTwiddle = true then 3 + 2 * γ else 0) := by
        apply Finset.sum_le_sum
        intro i _
        exact p04StageLinear_le_budget γ hγ (plan.stage i)
      _ = p04K plan γ := p04_stage_budget_sum_eq_K plan γ
  have hfunc :
      (fun u => ((List.ofFn (fun i : Fin plan.stageCount => i)).map
        (fun i => 1 + f i u)).prod - 1) =
      p04FftCoeffValue plan γ := by
    funext u
    rw [List.map_ofFn, p04_listOfFn_prod]
    rfl
  have hsum : ((List.ofFn (fun i : Fin plan.stageCount => i)).map a).sum =
      ∑ i : Fin plan.stageCount, a i := by
    rw [List.map_ofFn, p04_listOfFn_sum]
    rfl
  rw [hfunc, hsum] at hlist
  exact hlist.weaken hlinear

private noncomputable def p04MultiCoeffValue {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ u : ℝ) : ℝ :=
  (∏ i : Fin m,
    (1 + p04FftCoeffValue (plan.axis i).plan γ u)) - 1

private noncomputable def p04MultiCoeffValue_firstOrder {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ) (hγ : 0 ≤ γ) :
    P04FirstOrder (p04MultiCoeffValue plan γ)
      (∑ i : Fin m, p04AxisK (plan.axis i) γ) := by
  let f : Fin m → ℝ → ℝ :=
    fun i => p04FftCoeffValue (plan.axis i).plan γ
  let a : Fin m → ℝ := fun i => p04AxisK (plan.axis i) γ
  have hlist := p04FirstOrder_listProduct
    (List.ofFn (fun i : Fin m => i)) f a
    (fun i => by
      simpa [a, f, p04AxisK] using
        p04FftCoeffValue_firstOrder (plan.axis i).plan γ hγ)
  have hfunc :
      (fun u => ((List.ofFn (fun i : Fin m => i)).map
        (fun i => 1 + f i u)).prod - 1) =
      p04MultiCoeffValue plan γ := by
    funext u
    rw [List.map_ofFn, p04_listOfFn_prod]
    rfl
  have hsum : ((List.ofFn (fun i : Fin m => i)).map a).sum =
      ∑ i : Fin m, a i := by
    rw [List.map_ofFn, p04_listOfFn_sum]
    rfl
  rw [hfunc, hsum] at hlist
  exact hlist

private lemma p04StageCoeff_eq_value {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n) :
    p04StageCoeff model stage =
      p04StageCoeffValue model.gamma stage model.epsilon := by
  simp [p04StageCoeff, p04StageCoeffValue,
    p04RadixBlockCoeff, p04RadixBlockCoeffValue,
    p04RootMulCoeff, p04RootMulCoeffValue, p04PowErr]

private lemma p04_fft_errorProduct_eq_value {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel) :
    p04StepErrorProduct (List.ofFn (p04FftStageStep plan model)) - 1 =
      p04FftCoeffValue plan model.gamma model.epsilon := by
  unfold p04StepErrorProduct p04FftCoeffValue
  rw [List.map_ofFn, p04_listOfFn_prod]
  congr 1

private lemma p04_multi_errorProduct_eq_value {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (model : P04WilkinsonModel) :
    p04StepErrorProduct (List.ofFn (p04MultiStep plan model)).reverse - 1 =
      p04MultiCoeffValue plan model.gamma model.epsilon := by
  unfold p04StepErrorProduct p04MultiCoeffValue
  rw [List.map_reverse, List.prod_reverse, List.map_ofFn,
    p04_listOfFn_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change 1 + (p04StepErrorProduct
    (List.ofFn (p04FftStageStep (plan.axis i).plan model)) - 1) =
    1 + p04FftCoeffValue (plan.axis i).plan model.gamma model.epsilon
  rw [p04_fft_errorProduct_eq_value]

private lemma p04_multidimensional_norm_product_bound {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (model : P04WilkinsonModel)
    (run : P04MultidimensionalFftRun plan model) :
    p04MultiNorm2 (p04MultiVecSub (p04MultiComputedOutput run)
      (p04MultiExactOutput run)) ≤
      p04MultiCoeffValue plan model.gamma model.epsilon *
        p04MultiNorm2 (p04MultiExactOutput run) := by
  let steps := (List.ofFn (p04MultiStep plan model)).reverse
  have hfold := p04StepFold_error p04MultiNorm2_triangle steps
    run.input run.input
  have hscale := p04StepExactFold_scale steps run.input
  have hrounded := p04MultiStep_roundedFold plan model run
  have hexact := p04MultiStep_exactFold plan model run.input
  have hbase : p04MultiNorm2
      (p04StepRoundedFold steps run.input -
        p04StepExactFold steps run.input) ≤
      (p04StepErrorProduct steps - 1) *
        p04MultiNorm2 (p04StepExactFold steps run.input) := by
    have hzero : (run.input - run.input : P04MultiArray plan.axis) = 0 :=
      sub_self run.input
    rw [hzero] at hfold
    have hnormzero : p04MultiNorm2 (0 : P04MultiArray plan.axis) = 0 := by
      simp [p04MultiNorm2]
    rw [hnormzero, mul_zero, zero_add] at hfold
    calc
      _ ≤ p04StepScaleProduct steps *
        ((p04StepErrorProduct steps - 1) * p04MultiNorm2 run.input) := hfold
      _ = (p04StepErrorProduct steps - 1) *
        p04MultiNorm2 (p04StepExactFold steps run.input) := by
          rw [hscale]
          ring
  simpa [p04MultiVecSub, p04MultiComputedOutput, p04MultiExactOutput,
    steps, hrounded, hexact, p04_multi_errorProduct_eq_value] using hbase

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
  let estimate := p04MultiCoeffValue_firstOrder plan γ family.gamma_nonneg
  have hcard_nat : 0 < p04MultiCardinality plan.axis := by
    unfold p04MultiCardinality
    exact Finset.prod_pos fun i _ => (plan.axis i).order_pos
  have hcard : 0 < Real.sqrt (p04MultiCardinality plan.axis : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast hcard_nat
  refine ⟨estimate.second, estimate.second_nonneg, 1, by norm_num, ?_⟩
  intro ε hε
  have hnorm :
      p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) ≤
        p04MultiCoeffValue plan γ ε.1 *
          p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
    simpa only [p04FamilyMultiFftRoundoffError,
      p04FamilyMultiExactOutput, p04MultiExactOutput,
      p04MultiComputedOutput, family.run_input ε,
      family.model_gamma ε, family.model_epsilon ε] using
      p04_multidimensional_norm_product_bound plan
        (family.model ε) (family.run ε)
  have hrms :
      p04MultiRms (p04FamilyMultiFftRoundoffError family ε) ≤
        p04MultiCoeffValue plan γ ε.1 *
          p04MultiRms (p04FamilyMultiExactOutput family) := by
    unfold p04MultiRms
    apply (div_le_iff₀ hcard).2
    calc
      _ ≤ p04MultiCoeffValue plan γ ε.1 *
        p04MultiNorm2 (p04FamilyMultiExactOutput family) := hnorm
      _ = (p04MultiCoeffValue plan γ ε.1 *
          (p04MultiNorm2 (p04FamilyMultiExactOutput family) /
            Real.sqrt (p04MultiCardinality plan.axis : ℝ))) *
            Real.sqrt (p04MultiCardinality plan.axis : ℝ) := by
        field_simp
  calc
    _ ≤ p04MultiCoeffValue plan γ ε.1 := by
      apply (div_le_iff₀ hexactOutput).2
      exact hrms
    _ ≤ ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
        estimate.second * ε.1 ^ 2 := by
      simpa [mul_comm] using
        (estimate.bound ε.1 (le_of_lt ε.2) hε).2

end VSCLReuse

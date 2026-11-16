import VSCLReuse.P04.Definitions

namespace VSCLReuse

private theorem p04_flAdd_abs_error (model : P04WilkinsonModel)
    (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hfl⟩ := model.add_model a b
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  rw [hfl]
  have heq : a * (1 + θa * model.epsilon) +
      b * (1 + θb * model.epsilon) - (a + b) =
      a * θa * model.epsilon + b * θb * model.epsilon := by ring
  rw [heq]
  calc
    |a * θa * model.epsilon + b * θb * model.epsilon|
        ≤ |a * θa * model.epsilon| + |b * θb * model.epsilon| :=
          abs_add_le _ _
    _ = model.epsilon * (|a| * |θa| + |b| * |θb|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hε]
          ring
    _ ≤ model.epsilon * (|a| + |b|) := by
          apply mul_le_mul_of_nonneg_left _ hε
          simpa using add_le_add
            (mul_le_mul_of_nonneg_left hθa (abs_nonneg a))
            (mul_le_mul_of_nonneg_left hθb (abs_nonneg b))

private theorem p04_flMul_abs_error (model : P04WilkinsonModel)
    (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * |a * b| := by
  obtain ⟨θ, hθ, hfl⟩ := model.mul_model a b
  rw [hfl]
  have heq : a * b * (1 + θ * model.epsilon) - a * b =
      model.epsilon * θ * (a * b) := by ring
  rw [heq, abs_mul, abs_mul, abs_of_pos model.epsilon_pos]
  convert mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hθ (abs_nonneg (a * b)))
    (le_of_lt model.epsilon_pos) using 1 <;> ring

private theorem p04_flMul_abs_bound (model : P04WilkinsonModel)
    (a b : ℝ) :
    |model.flMul a b| ≤ (1 + model.epsilon) * |a * b| := by
  calc
    |model.flMul a b| ≤ |model.flMul a b - a * b| + |a * b| := by
      simpa only [sub_add_cancel] using
        (abs_add_le (model.flMul a b - a * b) (a * b))
    _ ≤ model.epsilon * |a * b| + |a * b| := by
      gcongr
      exact p04_flMul_abs_error model a b
    _ = (1 + model.epsilon) * |a * b| := by ring

private theorem p04_rounded_pair_abs_error (model : P04WilkinsonModel)
    (p q f g : ℝ)
    (hf : |f - p| ≤ model.epsilon * |p|)
    (hg : |g - q| ≤ model.epsilon * |q|) :
    |model.flAdd f g - (p + q)| ≤
      model.epsilon * (2 + model.epsilon) * (|p| + |q|) := by
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hfa : |f| ≤ (1 + model.epsilon) * |p| := by
    calc
      |f| ≤ |f - p| + |p| := by
        simpa only [sub_add_cancel] using abs_add_le (f - p) p
      _ ≤ model.epsilon * |p| + |p| := add_le_add hf le_rfl
      _ = (1 + model.epsilon) * |p| := by ring
  have hga : |g| ≤ (1 + model.epsilon) * |q| := by
    calc
      |g| ≤ |g - q| + |q| := by
        simpa only [sub_add_cancel] using abs_add_le (g - q) q
      _ ≤ model.epsilon * |q| + |q| := add_le_add hg le_rfl
      _ = (1 + model.epsilon) * |q| := by ring
  have hsplit : model.flAdd f g - (p + q) =
      (model.flAdd f g - (f + g)) + ((f - p) + (g - q)) := by ring
  rw [hsplit]
  calc
    |(model.flAdd f g - (f + g)) + ((f - p) + (g - q))|
        ≤ |model.flAdd f g - (f + g)| + (|f - p| + |g - q|) := by
          exact (abs_add_le _ _).trans
            (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ model.epsilon * (|f| + |g|) +
        (model.epsilon * |p| + model.epsilon * |q|) := by
          exact add_le_add (p04_flAdd_abs_error model f g)
            (add_le_add hf hg)
    _ ≤ model.epsilon * ((1 + model.epsilon) * |p| +
        (1 + model.epsilon) * |q|) +
        (model.epsilon * |p| + model.epsilon * |q|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hfa hga) hε) le_rfl
    _ = model.epsilon * (2 + model.epsilon) * (|p| + |q|) := by ring

private theorem p04_complex_norm_le_of_componentwise
    {z w : ℂ} (hre : |z.re| ≤ |w.re|) (him : |z.im| ≤ |w.im|) :
    ‖z‖ ≤ ‖w‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.mpr hre) (sq_le_sq.mpr him))

private theorem p04_roundedComplexMul_component_error
    (model : P04WilkinsonModel) (a b : ℂ) :
    |(p04RoundedComplexMul model a b - a * b).re| ≤
        model.epsilon * (2 + model.epsilon) *
          (|a.re * b.re| + |a.im * b.im|) ∧
    |(p04RoundedComplexMul model a b - a * b).im| ≤
        model.epsilon * (2 + model.epsilon) *
          (|a.re * b.im| + |a.im * b.re|) := by
  constructor
  · have h := p04_rounded_pair_abs_error model
        (a.re * b.re) (-(a.im * b.im))
        (model.flMul a.re b.re) (-model.flMul a.im b.im)
        (p04_flMul_abs_error model a.re b.re)
        (by simpa only [neg_sub_neg, abs_sub_comm, abs_neg] using
          p04_flMul_abs_error model a.im b.im)
    simpa [p04RoundedComplexMul, Complex.mul_re, sub_eq_add_neg] using h
  · have h := p04_rounded_pair_abs_error model
        (a.re * b.im) (a.im * b.re)
        (model.flMul a.re b.im) (model.flMul a.im b.re)
        (p04_flMul_abs_error model a.re b.im)
        (p04_flMul_abs_error model a.im b.re)
    simpa [p04RoundedComplexMul, Complex.mul_im] using h

private theorem p04_abs_bilinear_norm_le (a b : ℂ) :
    ‖(⟨|a.re * b.re| + |a.im * b.im|,
        |a.re * b.im| + |a.im * b.re|⟩ : ℂ)‖ ≤
      (3 / 2 : ℝ) * ‖a‖ * ‖b‖ := by
  let ar := |a.re|
  let ai := |a.im|
  let br := |b.re|
  let bi := |b.im|
  have ha : ‖a‖ ^ 2 = ar ^ 2 + ai ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, ar, ai, sq_abs]
    ring
  have hb : ‖b‖ ^ 2 = br ^ 2 + bi ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, br, bi, sq_abs]
    ring
  have h₁ : (ar * br + ai * bi) ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (ar * bi - ai * br)]
  have h₂ : (ar * bi + ai * br) ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (ar * br - ai * bi)]
  have hc : ‖(⟨|a.re * b.re| + |a.im * b.im|,
        |a.re * b.im| + |a.im * b.re|⟩ : ℂ)‖ ^ 2 =
      (ar * br + ai * bi) ^ 2 + (ar * bi + ai * br) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, ar, ai, br, bi, abs_mul]
    ring
  have hn : 0 ≤ (3 / 2 : ℝ) * ‖a‖ * ‖b‖ := by positivity
  have hsq : ‖(⟨|a.re * b.re| + |a.im * b.im|,
        |a.re * b.im| + |a.im * b.re|⟩ : ℂ)‖ ^ 2 ≤
      ((3 / 2 : ℝ) * ‖a‖ * ‖b‖) ^ 2 := by
    rw [hc]
    nlinarith [sq_nonneg (‖a‖ * ‖b‖)]
  nlinarith [hsq, norm_nonneg (⟨|a.re * b.re| + |a.im * b.im|,
        |a.re * b.im| + |a.im * b.re|⟩ : ℂ)]

private theorem p04_roundedComplexMul_error (model : P04WilkinsonModel)
    (a b : ℂ) :
    ‖p04RoundedComplexMul model a b - a * b‖ ≤
      model.epsilon * (2 + model.epsilon) * (3 / 2 : ℝ) * ‖a‖ * ‖b‖ := by
  let C : ℂ := ⟨|a.re * b.re| + |a.im * b.im|,
    |a.re * b.im| + |a.im * b.re|⟩
  let t : ℝ := model.epsilon * (2 + model.epsilon)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg (le_of_lt model.epsilon_pos) (by linarith [model.epsilon_pos])
  obtain ⟨hre₀, him₀⟩ := p04_roundedComplexMul_component_error model a b
  have hre : |(p04RoundedComplexMul model a b - a * b).re| ≤
      |(t • C).re| := by
    simpa [t, C, Complex.real_smul,
      abs_of_nonneg ht,
      abs_of_nonneg (by positivity :
        0 ≤ |a.re| * |b.re| + |a.im| * |b.im|)] using hre₀
  have him : |(p04RoundedComplexMul model a b - a * b).im| ≤
      |(t • C).im| := by
    simpa [t, C, Complex.real_smul,
      abs_of_nonneg ht,
      abs_of_nonneg (by positivity :
        0 ≤ |a.re| * |b.im| + |a.im| * |b.re|)] using him₀
  calc
    ‖p04RoundedComplexMul model a b - a * b‖
        ≤ ‖t • C‖ := p04_complex_norm_le_of_componentwise hre him
    _ = t * ‖C‖ := by
      rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht]
    _ ≤ t * ((3 / 2 : ℝ) * ‖a‖ * ‖b‖) := by
      exact mul_le_mul_of_nonneg_left (p04_abs_bilinear_norm_le a b) ht
    _ = model.epsilon * (2 + model.epsilon) * (3 / 2 : ℝ) * ‖a‖ * ‖b‖ := by
      dsimp [t]
      ring

private theorem p04_flSin_abs_error (model : P04WilkinsonModel)
    (a : ℝ) :
    |model.flSin a - Real.sin a| ≤
      model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hfl⟩ := model.sin_model a
  rw [hfl]
  have heq : Real.sin a + model.gamma * θ * model.epsilon -
      Real.sin a = model.gamma * model.epsilon * θ := by ring
  rw [heq, abs_mul, abs_of_nonneg
    (mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos))]
  simpa using mul_le_mul_of_nonneg_left hθ
    (mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos))

private theorem p04_flCos_abs_error (model : P04WilkinsonModel)
    (a : ℝ) :
    |model.flCos a - Real.cos a| ≤
      model.gamma * model.epsilon := by
  obtain ⟨θ, hθ, hfl⟩ := model.cos_model a
  rw [hfl]
  have heq : Real.cos a + model.gamma * θ * model.epsilon -
      Real.cos a = model.gamma * model.epsilon * θ := by ring
  rw [heq, abs_mul, abs_of_nonneg
    (mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos))]
  simpa using mul_le_mul_of_nonneg_left hθ
    (mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos))

private theorem p04_stdAddChar_eq_rootAngle {q : ℕ} [NeZero q]
    (j : ZMod q) :
    ZMod.stdAddChar j =
      (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ) := by
  rw [p04StdAddChar_positive_exp]
  have harg : (2 * Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (q : ℂ) =
      (p04RootAngle j : ℂ) * Complex.I := by
    simp only [p04RootAngle, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    ring
  rw [harg]
  apply Complex.ext
  · exact Complex.exp_ofReal_mul_I_re _
  · exact Complex.exp_ofReal_mul_I_im _

private theorem p04_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      2 * model.gamma * model.epsilon := by
  rw [p04_stdAddChar_eq_rootAngle]
  have hre := p04_flCos_abs_error model (p04RootAngle j)
  have him := p04_flSin_abs_error model (p04RootAngle j)
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (p04RoundedRoot model j -
      (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ))
  simp only [p04RoundedRoot, Complex.sub_re, Complex.sub_im] at hnorm
  change ‖(⟨model.flCos (p04RootAngle j), model.flSin (p04RootAngle j)⟩ : ℂ) -
      ⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩‖ ≤ _
  linarith

private theorem p04_stdAddChar_norm {q : ℕ} [NeZero q]
    (j : ZMod q) : ‖ZMod.stdAddChar j‖ = 1 := by
  rw [p04_stdAddChar_eq_rootAngle]
  have h : (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ) =
      Complex.exp ((p04RootAngle j : ℂ) * Complex.I) := by
    apply Complex.ext
    · exact (Complex.exp_ofReal_mul_I_re _).symm
    · exact (Complex.exp_ofReal_mul_I_im _).symm
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem p04_roundedRoot_norm_bound {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤ 1 + 2 * model.gamma * model.epsilon := by
  have h := norm_add_le
    (p04RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
  rw [sub_add_cancel, p04_stdAddChar_norm] at h
  linarith [p04_roundedRoot_error model j]

private theorem p04_roundedRootMul_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
        model.epsilon ^ 2 * (2 + 10 * model.gamma) * ‖x‖ := by
  let r := p04RoundedRoot model j
  let z := ZMod.stdAddChar j
  have hγ : 0 ≤ model.gamma := model.gamma_nonneg
  have hε₀ : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoeff : (2 + model.epsilon) * (3 / 2 : ℝ) *
      (1 + 2 * model.gamma * model.epsilon) + 2 * model.gamma ≤
      (3 + 2 * model.gamma) + model.epsilon * (2 + 10 * model.gamma) := by
    have haux : 0 ≤ model.gamma * model.epsilon * (1 - model.epsilon) := by
      exact mul_nonneg (mul_nonneg hγ hε₀) (sub_nonneg.mpr hε)
    nlinarith
  have hfac : 0 ≤ model.epsilon * (2 + model.epsilon) * (3 / 2 : ℝ) := by
    positivity
  have hroot := p04_roundedRoot_norm_bound model j
  have hmul := p04_roundedComplexMul_error model r x
  have hrooterr := p04_roundedRoot_error model j
  have hsplit : p04RoundedComplexMul model r x - z * x =
      (p04RoundedComplexMul model r x - r * x) + (r - z) * x := by ring
  change ‖p04RoundedComplexMul model r x - z * x‖ ≤ _
  rw [hsplit]
  calc
    ‖(p04RoundedComplexMul model r x - r * x) + (r - z) * x‖
        ≤ ‖p04RoundedComplexMul model r x - r * x‖ + ‖(r - z) * x‖ :=
          norm_add_le _ _
    _ ≤ model.epsilon * (2 + model.epsilon) * (3 / 2 : ℝ) *
          ‖r‖ * ‖x‖ + 2 * model.gamma * model.epsilon * ‖x‖ := by
          rw [norm_mul]
          exact add_le_add hmul
            (mul_le_mul_of_nonneg_right hrooterr (norm_nonneg x))
    _ ≤ model.epsilon * (2 + model.epsilon) * (3 / 2 : ℝ) *
          (1 + 2 * model.gamma * model.epsilon) * ‖x‖ +
          2 * model.gamma * model.epsilon * ‖x‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hroot hfac) (norm_nonneg x)) le_rfl
    _ ≤ model.epsilon * (3 + 2 * model.gamma) * ‖x‖ +
          model.epsilon ^ 2 * (2 + 10 * model.gamma) * ‖x‖ := by
          have hscaled := mul_le_mul_of_nonneg_left hcoeff
            (mul_nonneg hε₀ (norm_nonneg x))
          nlinarith

private theorem p04_pow_one_add_second_order (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        (1 + ε) ^ n ≤ 1 + (n : ℝ) * ε + C * ε ^ 2 := by
  induction n with
  | zero =>
      refine ⟨0, le_refl _, ?_⟩
      intro ε hε₀ hε₁
      simp
  | succ n ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨2 * C + n, by positivity, ?_⟩
      intro ε hε₀ hε₁
      have hbase := hbound ε hε₀ hε₁
      have hmul := mul_le_mul_of_nonneg_right hbase (by linarith : 0 ≤ 1 + ε)
      have hcube : C * ε ^ 2 * ε ≤ C * ε ^ 2 := by
        exact mul_le_of_le_one_right (mul_nonneg hC (sq_nonneg ε)) hε₁
      rw [pow_succ]
      push_cast
      nlinarith

private theorem p04_pow_product_second_order
    (n : ℕ) (A B C : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hpow : (1 + ε) ^ n ≤ 1 + (n : ℝ) * ε + C * ε ^ 2) :
    (1 + ε) ^ n * (1 + ε * A + ε ^ 2 * B) - 1 ≤
      ε * ((n : ℝ) + A) +
        ε ^ 2 * (C + (n : ℝ) * A + B + (n : ℝ) * B + C * A + C * B) := by
  have hfactor : 0 ≤ 1 + ε * A + ε ^ 2 * B := by positivity
  have hprod := mul_le_mul_of_nonneg_right hpow hfactor
  have h3 : ε ^ 3 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε₁)]
  have h4 : ε ^ 4 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr
      (by nlinarith [sq_nonneg (1 - ε)] : ε ^ 2 ≤ 1))]
  have hCA := mul_le_mul_of_nonneg_left h3 (mul_nonneg hC hA)
  have hnB := mul_le_mul_of_nonneg_left h3
    (mul_nonneg (Nat.cast_nonneg n) hB)
  have hCB := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC hB)
  nlinarith

private noncomputable def p04_recursiveComplexSum (model : P04WilkinsonModel)
    (n : ℕ) (v : Fin n → ℂ) : ℂ :=
  ⟨recursiveSum model.flAdd n (fun i ↦ (v i).re),
    recursiveSum model.flAdd n (fun i ↦ (v i).im)⟩

private theorem p04_recursiveComplexSum_zero (model : P04WilkinsonModel)
    (v : Fin 0 → ℂ) : p04_recursiveComplexSum model 0 v = 0 := by
  apply Complex.ext <;> simp [p04_recursiveComplexSum, recursiveSum]

private theorem p04_recursiveComplexSum_succ (model : P04WilkinsonModel)
    (n : ℕ) (v : Fin (n + 1) → ℂ) :
    p04_recursiveComplexSum model (n + 1) v =
      if h : n = 0 then v ⟨0, by omega⟩
      else p04RoundedComplexAdd model
        (p04_recursiveComplexSum model n (fun i ↦ v i.castSucc))
        (v (Fin.last n)) := by
  by_cases h : n = 0
  · subst n
    simp [p04_recursiveComplexSum, recursiveSum]
  · simp [p04_recursiveComplexSum, recursiveSum, h,
      p04RoundedComplexAdd]

private theorem p04_roundedComplexAdd_error (model : P04WilkinsonModel)
    (a b : ℂ) :
    ‖p04RoundedComplexAdd model a b - (a + b)‖ ≤
      model.epsilon * (‖a‖ + ‖b‖) := by
  let A : ℂ := ⟨|a.re|, |a.im|⟩
  let B : ℂ := ⟨|b.re|, |b.im|⟩
  have hA : ‖A‖ = ‖a‖ := by
    simp [A, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hB : ‖B‖ = ‖b‖ := by
    simp [B, Complex.norm_eq_sqrt_sq_add_sq, sq_abs]
  have hre : |(p04RoundedComplexAdd model a b - (a + b)).re| ≤
      |(model.epsilon • (A + B)).re| := by
    simpa [p04RoundedComplexAdd, A, B, Complex.real_smul,
      abs_of_pos model.epsilon_pos,
      abs_of_nonneg (add_nonneg (abs_nonneg a.re) (abs_nonneg b.re))] using
      p04_flAdd_abs_error model a.re b.re
  have him : |(p04RoundedComplexAdd model a b - (a + b)).im| ≤
      |(model.epsilon • (A + B)).im| := by
    simpa [p04RoundedComplexAdd, A, B, Complex.real_smul,
      abs_of_pos model.epsilon_pos,
      abs_of_nonneg (add_nonneg (abs_nonneg a.im) (abs_nonneg b.im))] using
      p04_flAdd_abs_error model a.im b.im
  calc
    ‖p04RoundedComplexAdd model a b - (a + b)‖
        ≤ ‖model.epsilon • (A + B)‖ :=
          p04_complex_norm_le_of_componentwise hre him
    _ = model.epsilon * ‖A + B‖ := by
          rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos model.epsilon_pos]
    _ ≤ model.epsilon * (‖A‖ + ‖B‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le A B) (le_of_lt model.epsilon_pos)
    _ = model.epsilon * (‖a‖ + ‖b‖) := by rw [hA, hB]

private theorem p04_recursiveComplexSum_error (model : P04WilkinsonModel)
    (n : ℕ) (v : Fin n → ℂ) :
    ‖p04_recursiveComplexSum model n v - ∑ i, v i‖ ≤
      ((1 + model.epsilon) ^ n - 1) * ∑ i, ‖v i‖ := by
  induction n with
  | zero =>
      simp [p04_recursiveComplexSum_zero]
  | succ n ih =>
      have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hpow : 0 ≤ (1 + model.epsilon) ^ n - 1 := by
        have h := one_le_pow₀ (n := n) (show (1 : ℝ) ≤ 1 + model.epsilon by linarith)
        linarith
      let u : Fin n → ℂ := fun i ↦ v i.castSucc
      let y : ℂ := v (Fin.last n)
      let R : ℂ := p04_recursiveComplexSum model n u
      let S : ℂ := ∑ i, u i
      let U : ℝ := ∑ i, ‖u i‖
      have hS : ‖S‖ ≤ U := by
        dsimp [S, U]
        exact norm_sum_le Finset.univ u
      have hR : ‖R - S‖ ≤ ((1 + model.epsilon) ^ n - 1) * U :=
        ih u
      have hRnorm : ‖R‖ ≤ U + ‖R - S‖ := by
        have h := norm_add_le (R - S) S
        rw [sub_add_cancel] at h
        linarith
      have hUsum : (∑ i : Fin (n + 1), ‖v i‖) = U + ‖y‖ := by
        exact Fin.sum_univ_castSucc _
      have hVsum : (∑ i : Fin (n + 1), v i) = S + y := by
        exact Fin.sum_univ_castSucc _
      by_cases hn : n = 0
      · subst n
        rw [p04_recursiveComplexSum_succ]
        simp [hVsum, hUsum, u, y, S, U]
        exact mul_nonneg hε (norm_nonneg (v 0))
      · rw [p04_recursiveComplexSum_succ, dif_neg hn, hVsum]
        change ‖p04RoundedComplexAdd model R y - (S + y)‖ ≤ _
        have hsplit : p04RoundedComplexAdd model R y - (S + y) =
            (p04RoundedComplexAdd model R y - (R + y)) + (R - S) := by ring
        rw [hsplit, hUsum]
        have hlocal := p04_roundedComplexAdd_error model R y
        have htri := norm_add_le
          (p04RoundedComplexAdd model R y - (R + y)) (R - S)
        have hU : 0 ≤ U := by
          dsimp [U]
          exact Finset.sum_nonneg fun i hi ↦ norm_nonneg (u i)
        have hbig : U ≤ U + ‖y‖ := by linarith [norm_nonneg y]
        have hrec : ‖R - S‖ ≤
            ((1 + model.epsilon) ^ n - 1) * (U + ‖y‖) :=
          hR.trans (mul_le_mul_of_nonneg_left hbig hpow)
        have hcoeff : 0 ≤ 1 + model.epsilon := by linarith
        have hscaled := mul_le_mul_of_nonneg_left hrec hcoeff
        rw [pow_succ]
        nlinarith

private theorem p04_roundedComplexSum_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j, term j‖ ≤
      ((1 + model.epsilon) ^ q - 1) * ∑ j, ‖term j‖ := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  have h := p04_recursiveComplexSum_error model q (fun i ↦ term (index i))
  have hsum : (∑ i : Fin q, term (index i)) = ∑ j : ZMod q, term j :=
    Equiv.sum_comp index term
  have hsumNorm : (∑ i : Fin q, ‖term (index i)‖) =
      ∑ j : ZMod q, ‖term j‖ := Equiv.sum_comp index (fun j ↦ ‖term j‖)
  rw [hsum, hsumNorm] at h
  simpa [p04RoundedComplexSum, p04_recursiveComplexSum, index] using h

private noncomputable def p04_powCoeff (q : ℕ) : ℝ :=
  Classical.choose (p04_pow_one_add_second_order q)

private theorem p04_powCoeff_nonneg (q : ℕ) : 0 ≤ p04_powCoeff q :=
  (Classical.choose_spec (p04_pow_one_add_second_order q)).1

private theorem p04_powCoeff_bound (q : ℕ) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    (1 + ε) ^ q ≤ 1 + (q : ℝ) * ε + p04_powCoeff q * ε ^ 2 :=
  (Classical.choose_spec (p04_pow_one_add_second_order q)).2 ε hε₀ hε₁

private noncomputable def p04_sumPerturbCoeff (q : ℕ) (A B : ℝ) : ℝ :=
  let C := p04_powCoeff q
  C + (q : ℝ) * A + B + (q : ℝ) * B + C * A + C * B

private theorem p04_sumPerturbCoeff_nonneg (q : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ p04_sumPerturbCoeff q A B := by
  dsimp [p04_sumPerturbCoeff]
  have hC := p04_powCoeff_nonneg q
  positivity

private theorem p04_roundedComplexSum_perturb {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (F G : ZMod q → ℂ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : model.epsilon ≤ 1)
    (hFG : ∀ j, ‖F j - G j‖ ≤
      (model.epsilon * A + model.epsilon ^ 2 * B) * ‖G j‖) :
    ‖p04RoundedComplexSum model F - ∑ j, G j‖ ≤
      (model.epsilon * ((q : ℝ) + A) +
        model.epsilon ^ 2 * p04_sumPerturbCoeff q A B) *
        ∑ j, ‖G j‖ := by
  let C := p04_powCoeff q
  have hC : 0 ≤ C := p04_powCoeff_nonneg q
  let δ : ℝ := model.epsilon * A + model.epsilon ^ 2 * B
  let X : ℝ := ∑ j : ZMod q, ‖G j‖
  have hε₀ : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hX : 0 ≤ X := by
    dsimp [X]
    exact Finset.sum_nonneg fun j hj ↦ norm_nonneg (G j)
  have hpow₀ : 0 ≤ (1 + model.epsilon) ^ q - 1 := by
    have h := one_le_pow₀ (n := q)
      (show (1 : ℝ) ≤ 1 + model.epsilon by linarith)
    linarith
  have hFnorm (j : ZMod q) : ‖F j‖ ≤ (1 + δ) * ‖G j‖ := by
    have h := norm_add_le (F j - G j) (G j)
    rw [sub_add_cancel] at h
    have hj := hFG j
    dsimp [δ]
    nlinarith
  have hsumFnorm : (∑ j : ZMod q, ‖F j‖) ≤ (1 + δ) * X := by
    calc
      (∑ j : ZMod q, ‖F j‖) ≤ ∑ j : ZMod q, (1 + δ) * ‖G j‖ :=
        Finset.sum_le_sum fun j hj ↦ hFnorm j
      _ = (1 + δ) * X := by rw [← Finset.mul_sum]
  have hsumDiff : ‖(∑ j : ZMod q, F j) - ∑ j : ZMod q, G j‖ ≤ δ * X := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : ZMod q, (F j - G j)‖ ≤ ∑ j : ZMod q, ‖F j - G j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, δ * ‖G j‖ :=
        Finset.sum_le_sum fun j hj ↦ hFG j
      _ = δ * X := by rw [← Finset.mul_sum]
  have hRound := p04_roundedComplexSum_error model F
  have hsplit : p04RoundedComplexSum model F - ∑ j, G j =
      (p04RoundedComplexSum model F - ∑ j, F j) +
        ((∑ j, F j) - ∑ j, G j) := by ring
  have htotal : ‖p04RoundedComplexSum model F - ∑ j, G j‖ ≤
      ((1 + model.epsilon) ^ q * (1 + δ) - 1) * X := by
    rw [hsplit]
    have htri := norm_add_le
      (p04RoundedComplexSum model F - ∑ j, F j)
      ((∑ j, F j) - ∑ j, G j)
    have hroundScaled := mul_le_mul_of_nonneg_left hsumFnorm hpow₀
    nlinarith
  have hpoly := p04_pow_product_second_order q A B C hA hB hC
    model.epsilon hε₀ hε (p04_powCoeff_bound q model.epsilon hε₀ hε)
  have hscaled := mul_le_mul_of_nonneg_right hpoly hX
  dsimp [δ, p04_sumPerturbCoeff, C] at htotal ⊢
  exact htotal.trans (by nlinarith)

private theorem p04_roundedGenericRadixBlock_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
        model.epsilon ^ 2 * p04_sumPerturbCoeff q
          (3 + 2 * model.gamma) (2 + 10 * model.gamma)) *
        ∑ j : ZMod q, ‖x j‖ := by
  let F : ZMod q → ℂ := fun j ↦
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let G : ZMod q → ℂ := fun j ↦ ZMod.stdAddChar (j * k) * x j
  have hA : 0 ≤ 3 + 2 * model.gamma := by linarith [model.gamma_nonneg]
  have hB : 0 ≤ 2 + 10 * model.gamma := by linarith [model.gamma_nonneg]
  have hFG (j : ZMod q) : ‖F j - G j‖ ≤
      (model.epsilon * (3 + 2 * model.gamma) +
        model.epsilon ^ 2 * (2 + 10 * model.gamma)) * ‖G j‖ := by
    have h := p04_roundedRootMul_error model (j * k) (x j) hε
    have hnorm : ‖G j‖ = ‖x j‖ := by
      simp [G, norm_mul, p04_stdAddChar_norm]
    rw [hnorm]
    dsimp [F, G]
    nlinarith
  have hbound := p04_roundedComplexSum_perturb model F G
      (3 + 2 * model.gamma) (2 + 10 * model.gamma) hA hB hε hFG
  have hnorm (j : ZMod q) : ‖G j‖ = ‖x j‖ := by
    simp [G, norm_mul, p04_stdAddChar_norm]
  simpa [p04RoundedGenericRadixBlock, F, G, hnorm, add_assoc] using hbound

private theorem p04_roundedRadixTwoBlock_eq (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    p04RoundedRadixTwoBlock model x k =
      p04RoundedComplexAdd model
        (p04RadixTwoCoefficientApply (0 * k) (x 0))
        (p04RadixTwoCoefficientApply (1 * k) (x 1)) := by
  simp [p04RoundedRadixTwoBlock, p04RoundedComplexSum,
    recursiveSum, p04RoundedComplexAdd]

private theorem p04_stdAddChar_one_two :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [p04_stdAddChar_eq_rootAngle]
  norm_num [p04RootAngle, ZMod.val_one, Real.cos_pi, Real.sin_pi]
  apply Complex.ext <;> norm_num

private theorem p04_radixTwoCoefficientApply_eq
    (j : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change (if (0 : ZMod 2) = 0 then x else -x) =
        ZMod.stdAddChar (0 : ZMod 2) * x
    rw [if_pos rfl, AddChar.map_zero_eq_one]
    ring
  · change (if (1 : ZMod 2) = 0 then x else -x) =
        ZMod.stdAddChar (1 : ZMod 2) * x
    rw [if_neg (by decide : (1 : ZMod 2) ≠ 0), p04_stdAddChar_one_two]
    ring

private theorem p04_sum_zmod_two {M : Type*} [AddCommMonoid M]
    (f : ZMod 2 → M) : (∑ j : ZMod 2, f j) = f 0 + f 1 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 2).toEquiv f, Fin.sum_univ_two]
  rfl

private theorem p04_roundedRadixTwoBlock_error (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * ∑ j : ZMod 2, ‖x j‖ := by
  rw [p04_roundedRadixTwoBlock_eq, p04_sum_zmod_two]
  rw [← p04_radixTwoCoefficientApply_eq (0 * k) (x 0),
    ← p04_radixTwoCoefficientApply_eq (1 * k) (x 1)]
  have h := p04_roundedComplexAdd_error model
    (p04RadixTwoCoefficientApply (0 * k) (x 0))
    (p04RadixTwoCoefficientApply (1 * k) (x 1))
  have h0 : ‖p04RadixTwoCoefficientApply (0 * k) (x 0)‖ = ‖x 0‖ := by
    rw [p04_radixTwoCoefficientApply_eq, norm_mul, p04_stdAddChar_norm]
    ring
  have h1 : ‖p04RadixTwoCoefficientApply (1 * k) (x 1)‖ = ‖x 1‖ := by
    rw [p04_radixTwoCoefficientApply_eq, norm_mul, p04_stdAddChar_norm]
    ring
  rw [h0, h1] at h
  simpa [p04_sum_zmod_two] using h

private theorem p04_stdAddChar_one_four :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [p04_stdAddChar_eq_rootAngle]
  have hangle : p04RootAngle (1 : ZMod 4) = Real.pi / 2 := by
    letI : Fact (1 < 4) := ⟨by norm_num⟩
    unfold p04RootAngle
    norm_num [ZMod.val_one]
    ring
  rw [hangle, Real.cos_pi_div_two, Real.sin_pi_div_two]
  apply Complex.ext <;> norm_num

private theorem p04_stdAddChar_two_four :
    ZMod.stdAddChar (2 : ZMod 4) = (-1 : ℂ) := by
  have h2 : (2 : ZMod 4) = 1 + 1 := by decide
  rw [h2, AddChar.map_add_eq_mul, p04_stdAddChar_one_four]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]

private theorem p04_stdAddChar_three_four :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have h3 : (3 : ZMod 4) = 2 + 1 := by decide
  rw [h3, AddChar.map_add_eq_mul, p04_stdAddChar_two_four,
    p04_stdAddChar_one_four]
  ring

private theorem p04_radixFourCoefficientApply_eq
    (j : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply j x = ZMod.stdAddChar j * x := by
  fin_cases j
  · change (if (0 : ZMod 4) = 0 then x else
        if (0 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (0 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (0 : ZMod 4) * x
    rw [if_pos rfl, AddChar.map_zero_eq_one]
    ring
  · change (if (1 : ZMod 4) = 0 then x else
        if (1 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (1 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (1 : ZMod 4) * x
    rw [if_neg (by decide : (1 : ZMod 4) ≠ 0), if_pos rfl,
      p04_stdAddChar_one_four]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

  · change (if (2 : ZMod 4) = 0 then x else
        if (2 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (2 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (2 : ZMod 4) * x
    rw [if_neg (by decide : (2 : ZMod 4) ≠ 0),
      if_neg (by decide : (2 : ZMod 4) ≠ 1), if_pos rfl,
      p04_stdAddChar_two_four]
    ring
  · change (if (3 : ZMod 4) = 0 then x else
        if (3 : ZMod 4) = 1 then ⟨-x.im, x.re⟩ else
        if (3 : ZMod 4) = 2 then -x else ⟨x.im, -x.re⟩) =
        ZMod.stdAddChar (3 : ZMod 4) * x
    rw [if_neg (by decide : (3 : ZMod 4) ≠ 0),
      if_neg (by decide : (3 : ZMod 4) ≠ 1),
      if_neg (by decide : (3 : ZMod 4) ≠ 2),
      p04_stdAddChar_three_four]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p04_sum_zmod_four {M : Type*} [AddCommMonoid M]
    (f : ZMod 4 → M) :
    (∑ j : ZMod 4, f j) = f 0 + f 1 + f 2 + f 3 := by
  rw [← Equiv.sum_comp (ZMod.finEquiv 4).toEquiv f, Fin.sum_univ_four]
  rfl

private theorem p04_roundedAdd_four_error (model : P04WilkinsonModel)
    (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) -
        (a + b + c + d)‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  let U := a + b
  let V := c + d
  let A := ‖a‖ + ‖b‖
  let B := ‖c‖ + ‖d‖
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hu := p04_roundedComplexAdd_error model a b
  have hv := p04_roundedComplexAdd_error model c d
  have houter := p04_roundedComplexAdd_error model u v
  have hunorm : ‖u‖ ≤ (1 + model.epsilon) * A := by
    have h := norm_add_le (u - U) U
    rw [sub_add_cancel] at h
    have hU : ‖U‖ ≤ A := norm_add_le a b
    dsimp [u, U, A] at hu hU ⊢
    nlinarith
  have hvnorm : ‖v‖ ≤ (1 + model.epsilon) * B := by
    have h := norm_add_le (v - V) V
    rw [sub_add_cancel] at h
    have hV : ‖V‖ ≤ B := norm_add_le c d
    dsimp [v, V, B] at hv hV ⊢
    nlinarith
  have hsplit : p04RoundedComplexAdd model u v - (U + V) =
      (p04RoundedComplexAdd model u v - (u + v)) +
        ((u - U) + (v - V)) := by ring
  have htri := norm_add_le
    (p04RoundedComplexAdd model u v - (u + v)) ((u - U) + (v - V))
  have htri₂ := norm_add_le (u - U) (v - V)
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hunorm hvnorm) hε
  suffices htarget : ‖p04RoundedComplexAdd model u v - (U + V)‖ ≤
      model.epsilon * (2 + model.epsilon) * (A + B) by
    have hshape : p04RoundedComplexAdd model
          (p04RoundedComplexAdd model a b)
          (p04RoundedComplexAdd model c d) - (a + b + c + d) =
        p04RoundedComplexAdd model u v - (U + V) := by
      dsimp [u, v, U, V]
      ring
    have hcoeff : ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ = A + B := by
      dsimp [A, B]
      ring
    rwa [hshape, hcoeff]
  rw [hsplit]
  nlinarith

private theorem p04_roundedRadixFourBlock_error (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (2 + model.epsilon) *
        ∑ j : ZMod 4, ‖x j‖ := by
  let index : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let t : Fin 4 → ℂ := fun i ↦
    p04RadixFourCoefficientApply (index i * k) (x (index i))
  have hsum : (∑ i : Fin 4, t i) =
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j := by
    simp_rw [t, p04_radixFourCoefficientApply_eq]
    exact Equiv.sum_comp index (fun j ↦ ZMod.stdAddChar (j * k) * x j)
  have hnorm (i : Fin 4) : ‖t i‖ = ‖x (index i)‖ := by
    rw [show t i = ZMod.stdAddChar (index i * k) * x (index i) from
      p04_radixFourCoefficientApply_eq (index i * k) (x (index i))]
    rw [norm_mul, p04_stdAddChar_norm, one_mul]
  have hsumNorm : (∑ i : Fin 4, ‖t i‖) =
      ∑ j : ZMod 4, ‖x j‖ := by
    simp_rw [hnorm]
    exact Equiv.sum_comp index (fun j ↦ ‖x j‖)
  rw [Fin.sum_univ_four] at hsum hsumNorm
  have hround := p04_roundedAdd_four_error model (t 0) (t 1) (t 2) (t 3)
  rw [← hsum, ← hsumNorm]
  change ‖p04RoundedComplexAdd model
      (p04RoundedComplexAdd model (t 0) (t 1))
      (p04RoundedComplexAdd model (t 2) (t 3)) -
      (t 0 + t 1 + t 2 + t 3)‖ ≤
    model.epsilon * (2 + model.epsilon) *
      (‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖)
  exact hround

private theorem p04_l2_uniform_bound {ι : Type*} [Fintype ι]
    (x e : ι → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i, ‖e i‖ ≤ c * ∑ j, ‖x j‖) :
    ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ≤
      (Fintype.card ι : ℝ) * c *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := by
  let X : ℝ := ∑ j : ι, ‖x j‖
  have hX : 0 ≤ X := by
    dsimp [X]
    exact Finset.sum_nonneg fun j hj ↦ norm_nonneg (x j)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hCauchy : X ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j : ι, ‖x j‖ ^ 2 := by
    simpa [X] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : ι ↦ ‖x j‖))
  have hE : (∑ i : ι, ‖e i‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * (c * X) ^ 2 := by
    calc
      (∑ i : ι, ‖e i‖ ^ 2) ≤ ∑ i : ι, (c * X) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := hpoint i
        change ‖e i‖ ≤ c * X at h
        nlinarith [norm_nonneg (e i), mul_nonneg hc hX]
      _ = (Fintype.card ι : ℝ) * (c * X) ^ 2 := by simp
  have hnormE : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ^ 2 =
      ∑ i : ι, ‖e i‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq (WithLp.toLp 2 e : EuclideanSpace ℂ ι)
  have hnormX : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 =
      ∑ i : ι, ‖x i‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
  have hsc := mul_le_mul_of_nonneg_left hCauchy
    (mul_nonneg hcard (sq_nonneg c))
  have hsq : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      ((Fintype.card ι : ℝ) * c *
        ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [hnormE]
    calc
      (∑ i : ι, ‖e i‖ ^ 2) ≤ (Fintype.card ι : ℝ) * (c * X) ^ 2 := hE
      _ = (Fintype.card ι : ℝ) * c ^ 2 * X ^ 2 := by ring
      _ ≤ (Fintype.card ι : ℝ) * c ^ 2 *
          ((Fintype.card ι : ℝ) * ∑ j : ι, ‖x j‖ ^ 2) := hsc
      _ = ((Fintype.card ι : ℝ) * c *
          ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
        rw [← hnormX]
        ring
  nlinarith [hsq,
    norm_nonneg (WithLp.toLp 2 e : EuclideanSpace ℂ ι),
    mul_nonneg (mul_nonneg hcard hc)
      (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ ι))]

private theorem p04_complexNorm2_eq_euclidean {q : ℕ} [NeZero q]
    (x : ZMod q → ℂ) :
    p04ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod q))‖ := by
  rw [EuclideanSpace.norm_eq]
  rfl

private theorem p04_l2_pointwise_bound {ι : Type*} [Fintype ι]
    (x e : ι → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i, ‖e i‖ ≤ c * ‖x i‖) :
    ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ≤
      c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ := by
  have hsumsq : (∑ i : ι, ‖e i‖ ^ 2) ≤
      c ^ 2 * ∑ i : ι, ‖x i‖ ^ 2 := by
    calc
      (∑ i : ι, ‖e i‖ ^ 2) ≤ ∑ i : ι, (c * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [hpoint i, norm_nonneg (e i),
          mul_nonneg hc (norm_nonneg (x i))]
      _ = c ^ 2 * ∑ i : ι, ‖x i‖ ^ 2 := by
        rw [Finset.mul_sum]
        congr 1
        ext i
        ring
  have hnormE : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ^ 2 =
      ∑ i : ι, ‖e i‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq (WithLp.toLp 2 e : EuclideanSpace ℂ ι)
  have hnormX : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 =
      ∑ i : ι, ‖x i‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x : EuclideanSpace ℂ ι)
  have hsq : ‖(WithLp.toLp 2 e : EuclideanSpace ℂ ι)‖ ^ 2 ≤
      (c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖) ^ 2 := by
    rw [hnormE]
    convert hsumsq using 1 <;> rw [← hnormX] <;> ring
  nlinarith [hsq,
    norm_nonneg (WithLp.toLp 2 e : EuclideanSpace ℂ ι),
    mul_nonneg hc (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ ι))]

private theorem p04_roundedRadixTwoBlock_l2_error (model : P04WilkinsonModel)
    (x : ZMod 2 → ℂ) :
    p04ComplexNorm2 (fun k ↦ p04RoundedRadixTwoBlock model x k -
      ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) ≤
      2 * model.epsilon * p04ComplexNorm2 x := by
  let e : ZMod 2 → ℂ := fun k ↦ p04RoundedRadixTwoBlock model x k -
    ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j
  have h := p04_l2_uniform_bound x e model.epsilon
    (le_of_lt model.epsilon_pos)
    (fun k ↦ p04_roundedRadixTwoBlock_error model x k)
  simpa [e, p04_complexNorm2_eq_euclidean, ZMod.card] using h

private theorem p04_roundedRadixFourBlock_l2_error (model : P04WilkinsonModel)
    (x : ZMod 4 → ℂ) :
    p04ComplexNorm2 (fun k ↦ p04RoundedRadixFourBlock model x k -
      ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) ≤
      4 * (model.epsilon * (2 + model.epsilon)) * p04ComplexNorm2 x := by
  let e : ZMod 4 → ℂ := fun k ↦ p04RoundedRadixFourBlock model x k -
    ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j
  have hc : 0 ≤ model.epsilon * (2 + model.epsilon) := by
    exact mul_nonneg (le_of_lt model.epsilon_pos) (by linarith [model.epsilon_pos])
  have h := p04_l2_uniform_bound x e
    (model.epsilon * (2 + model.epsilon)) hc
    (fun k ↦ p04_roundedRadixFourBlock_error model x k)
  simpa [e, p04_complexNorm2_eq_euclidean, ZMod.card] using h

private theorem p04_roundedGenericRadixBlock_l2_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ)
    (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun k ↦ p04RoundedGenericRadixBlock model x k -
      ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j) ≤
      (q : ℝ) *
        (model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
          model.epsilon ^ 2 * p04_sumPerturbCoeff q
            (3 + 2 * model.gamma) (2 + 10 * model.gamma)) *
              p04ComplexNorm2 x := by
  let e : ZMod q → ℂ := fun k ↦ p04RoundedGenericRadixBlock model x k -
    ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j
  let c : ℝ := model.epsilon * ((q : ℝ) + 3 + 2 * model.gamma) +
    model.epsilon ^ 2 * p04_sumPerturbCoeff q
      (3 + 2 * model.gamma) (2 + 10 * model.gamma)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hA : 0 ≤ (q : ℝ) + 3 + 2 * model.gamma := by
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith [model.gamma_nonneg]
    have hC : 0 ≤ p04_sumPerturbCoeff q
        (3 + 2 * model.gamma) (2 + 10 * model.gamma) := by
      apply p04_sumPerturbCoeff_nonneg
      all_goals linarith [model.gamma_nonneg]
    exact add_nonneg
      (mul_nonneg (le_of_lt model.epsilon_pos) hA)
      (mul_nonneg (sq_nonneg model.epsilon) hC)
  have h := p04_l2_uniform_bound x e c hc
    (fun k ↦ p04_roundedGenericRadixBlock_error model x k hε)
  simpa [e, c, p04_complexNorm2_eq_euclidean, ZMod.card] using h

private theorem p04_l2_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equiv : ι ≃ κ) (x : κ → ℂ) :
    ‖(WithLp.toLp 2 (fun i ↦ x (equiv i)) : EuclideanSpace ℂ ι)‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ κ)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp equiv (fun k ↦ ‖x k‖ ^ 2)

private theorem p04_l2_block_bound {α β : Type*}
    [Fintype α] [Fintype β]
    (x e : α → β → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ a,
      ‖(WithLp.toLp 2 (e a) : EuclideanSpace ℂ β)‖ ≤
        c * ‖(WithLp.toLp 2 (x a) : EuclideanSpace ℂ β)‖) :
    ‖(WithLp.toLp 2 (fun p : α × β ↦ e p.1 p.2) :
        EuclideanSpace ℂ (α × β))‖ ≤
      c * ‖(WithLp.toLp 2 (fun p : α × β ↦ x p.1 p.2) :
        EuclideanSpace ℂ (α × β))‖ := by
  have hblockSq (a : α) : (∑ b : β, ‖e a b‖ ^ 2) ≤
      c ^ 2 * (∑ b : β, ‖x a b‖ ^ 2) := by
    have he : ‖(WithLp.toLp 2 (e a) : EuclideanSpace ℂ β)‖ ^ 2 =
        ∑ b : β, ‖e a b‖ ^ 2 := by
      simpa only [PiLp.toLp_apply] using
        EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (e a) : EuclideanSpace ℂ β)
    have hx : ‖(WithLp.toLp 2 (x a) : EuclideanSpace ℂ β)‖ ^ 2 =
        ∑ b : β, ‖x a b‖ ^ 2 := by
      simpa only [PiLp.toLp_apply] using
        EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (x a) : EuclideanSpace ℂ β)
    have h := hblock a
    nlinarith [he, hx,
      norm_nonneg (WithLp.toLp 2 (e a) : EuclideanSpace ℂ β),
      mul_nonneg hc (norm_nonneg (WithLp.toLp 2 (x a) : EuclideanSpace ℂ β))]
  have hsumSq : (∑ p : α × β, ‖e p.1 p.2‖ ^ 2) ≤
      c ^ 2 * ∑ p : α × β, ‖x p.1 p.2‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ a : α, ∑ b : β, ‖e a b‖ ^ 2) ≤
          ∑ a : α, c ^ 2 * (∑ b : β, ‖x a b‖ ^ 2) :=
            Finset.sum_le_sum fun a ha ↦ hblockSq a
      _ = c ^ 2 * ∑ a : α, ∑ b : β, ‖x a b‖ ^ 2 := by rw [Finset.mul_sum]
  have he : ‖(WithLp.toLp 2 (fun p : α × β ↦ e p.1 p.2) :
      EuclideanSpace ℂ (α × β))‖ ^ 2 =
      ∑ p : α × β, ‖e p.1 p.2‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq
        (WithLp.toLp 2 (fun p : α × β ↦ e p.1 p.2) : EuclideanSpace ℂ (α × β))
  have hx : ‖(WithLp.toLp 2 (fun p : α × β ↦ x p.1 p.2) :
      EuclideanSpace ℂ (α × β))‖ ^ 2 =
      ∑ p : α × β, ‖x p.1 p.2‖ ^ 2 := by
    simpa only [PiLp.toLp_apply] using
      EuclideanSpace.norm_sq_eq
        (WithLp.toLp 2 (fun p : α × β ↦ x p.1 p.2) : EuclideanSpace ℂ (α × β))
  nlinarith [he, hx, hsumSq,
    norm_nonneg (WithLp.toLp 2 (fun p : α × β ↦ e p.1 p.2) :
      EuclideanSpace ℂ (α × β)),
    mul_nonneg hc (norm_nonneg
      (WithLp.toLp 2 (fun p : α × β ↦ x p.1 p.2) : EuclideanSpace ℂ (α × β)))]

private noncomputable def p04_roundedRadixBlock {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q) : ℂ :=
  if h2 : q = 2 then
    p04RoundedRadixTwoBlock model
      (fun j : ZMod 2 ↦ x (h2.symm ▸ j)) (h2 ▸ k)
  else if h4 : q = 4 then
    p04RoundedRadixFourBlock model
      (fun j : ZMod 4 ↦ x (h4.symm ▸ j)) (h4 ▸ k)
  else p04RoundedGenericRadixBlock model x k

private noncomputable def p04_radixBlockSecond (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 0 else if q = 4 then 4
  else (q : ℝ) * p04_sumPerturbCoeff q (3 + 2 * γ) (2 + 10 * γ)

private theorem p04_radixBlockSecond_nonneg (q : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) : 0 ≤ p04_radixBlockSecond q γ := by
  unfold p04_radixBlockSecond
  split_ifs <;> try norm_num
  apply mul_nonneg (Nat.cast_nonneg q)
  apply p04_sumPerturbCoeff_nonneg <;> linarith

private theorem p04_roundedRadixBlock_l2_error {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (model : P04WilkinsonModel)
    (x : ZMod q → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun k ↦
      p04_roundedRadixBlock model x k - p04FourierTransform x k) ≤
      (model.epsilon * Real.sqrt (q : ℝ) *
          p04Alpha q model.gamma +
        model.epsilon ^ 2 * p04_radixBlockSecond q model.gamma) *
          p04ComplexNorm2 x := by
  by_cases h2 : q = 2
  · subst q
    have hlocal := p04_roundedRadixTwoBlock_l2_error model x
    have hsqrt : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
      rw [← pow_two, Real.sq_sqrt (by norm_num)]
    have hshape : (fun k : ZMod 2 ↦
        p04_roundedRadixBlock model x k - p04FourierTransform x k) =
        (fun k : ZMod 2 ↦ p04RoundedRadixTwoBlock model x k -
          ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) := by
      funext k
      simp [p04_roundedRadixBlock, p04FourierTransform]
    rw [hshape]
    have hbase : model.epsilon * Real.sqrt (2 : ℝ) * Real.sqrt 2 =
        2 * model.epsilon := by rw [mul_assoc, hsqrt]; ring
    simpa [p04Alpha, p04_radixBlockSecond, hbase] using hlocal
  · by_cases h4 : q = 4
    · subst q
      have hlocal := p04_roundedRadixFourBlock_l2_error model x
      simp [p04_roundedRadixBlock, p04FourierTransform,
        p04Alpha, p04_radixBlockSecond] at *
      have hε₀ : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hnorm : 0 ≤ p04ComplexNorm2 x := by
        unfold p04ComplexNorm2
        exact Real.sqrt_nonneg _
      norm_num at *
      nlinarith
    · have hlocal := p04_roundedGenericRadixBlock_l2_error model x hε
      have hq3 : 3 ≤ q := by omega
      have hqR : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      have hsqrt : Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) = (q : ℝ) := by
        rw [← pow_two, Real.sq_sqrt hqR]
      have hcoeff : (q : ℝ) * ((q : ℝ) + 3 + 2 * model.gamma) ≤
          2 * (q : ℝ) * ((q : ℝ) + model.gamma) := by
        have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
        have h := mul_nonneg hqR (show 0 ≤ (q : ℝ) - 3 by linarith)
        nlinarith
      have hε₀ : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
      have hnorm : 0 ≤ p04ComplexNorm2 x := by
        unfold p04ComplexNorm2
        exact Real.sqrt_nonneg _
      simp [p04_roundedRadixBlock, p04FourierTransform,
        p04Alpha, p04_radixBlockSecond, h2, h4] at ⊢
      have hcoeffScaled := mul_le_mul_of_nonneg_left hcoeff hε₀
      have htargetCoeff : model.epsilon * Real.sqrt (q : ℝ) *
          (2 * Real.sqrt (q : ℝ) * ((q : ℝ) + model.gamma)) +
          model.epsilon ^ 2 *
            ((q : ℝ) * p04_sumPerturbCoeff q
              (3 + 2 * model.gamma) (2 + 10 * model.gamma)) =
          model.epsilon * (2 * (q : ℝ) * ((q : ℝ) + model.gamma)) +
          model.epsilon ^ 2 *
            ((q : ℝ) * p04_sumPerturbCoeff q
              (3 + 2 * model.gamma) (2 + 10 * model.gamma)) := by
        calc
          _ = model.epsilon *
              (2 * (Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ)) *
                ((q : ℝ) + model.gamma)) +
              model.epsilon ^ 2 *
                ((q : ℝ) * p04_sumPerturbCoeff q
                  (3 + 2 * model.gamma) (2 + 10 * model.gamma)) := by ring
          _ = _ := by rw [hsqrt]
      rw [htargetCoeff]
      exact hlocal.trans (mul_le_mul_of_nonneg_right (by nlinarith) hnorm)

private theorem p04_mixedBlock_apply_reindex {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ)
    (b : Fin stage.blockCount) (k : ZMod stage.radix) :
    p04MixedRadixBlockApply stage x (stage.reindex (b, k)) =
      p04FourierTransform
        (fun j : ZMod stage.radix ↦
          x (stage.permutation (stage.reindex (b, j)))) k := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  simp [p04MixedRadixBlockApply, p04FourierTransform]

private theorem p04_roundedMixedBlock_apply_reindex {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ)
    (b : Fin stage.blockCount) (k : ZMod stage.radix) :
    p04RoundedMixedRadixBlockApply model stage x (stage.reindex (b, k)) =
      p04_roundedRadixBlock model
        (fun j : ZMod stage.radix ↦
          x (stage.permutation (stage.reindex (b, j)))) k := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  simp [p04RoundedMixedRadixBlockApply, p04_roundedRadixBlock]

private theorem p04_alpha_nonneg (q : ℕ) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04Alpha q γ := by
  unfold p04Alpha
  split_ifs <;> positivity

private theorem p04_mixedBlock_l2_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixBlockApply model stage x i -
        p04MixedRadixBlockApply stage x i) ≤
      (model.epsilon * Real.sqrt (stage.radix : ℝ) *
          p04Alpha stage.radix model.gamma +
        model.epsilon ^ 2 *
          p04_radixBlockSecond stage.radix model.gamma) *
        p04ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  let xB : Fin stage.blockCount → ZMod stage.radix → ℂ := fun b j ↦
    x (stage.permutation (stage.reindex (b, j)))
  let eB : Fin stage.blockCount → ZMod stage.radix → ℂ := fun b k ↦
    p04_roundedRadixBlock model (xB b) k - p04FourierTransform (xB b) k
  let c : ℝ := model.epsilon * Real.sqrt (stage.radix : ℝ) *
      p04Alpha stage.radix model.gamma +
    model.epsilon ^ 2 * p04_radixBlockSecond stage.radix model.gamma
  have hc : 0 ≤ c := by
    dsimp [c]
    have hα := p04_alpha_nonneg stage.radix model.gamma model.gamma_nonneg
    have hC := p04_radixBlockSecond_nonneg stage.radix model.gamma model.gamma_nonneg
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt model.epsilon_pos) (Real.sqrt_nonneg _)) hα)
      (mul_nonneg (sq_nonneg model.epsilon) hC)
  have hblock (b : Fin stage.blockCount) :
      ‖(WithLp.toLp 2 (eB b) : EuclideanSpace ℂ (ZMod stage.radix))‖ ≤
        c * ‖(WithLp.toLp 2 (xB b) : EuclideanSpace ℂ (ZMod stage.radix))‖ := by
    simpa [eB, c, p04_complexNorm2_eq_euclidean] using
      p04_roundedRadixBlock_l2_error stage.radix_two_le model (xB b) hε
  have hglobal := p04_l2_block_bound xB eB c hc hblock
  let E : ZMod n → ℂ := fun i ↦
    p04RoundedMixedRadixBlockApply model stage x i -
      p04MixedRadixBlockApply stage x i
  have hout : ‖(WithLp.toLp 2 E : EuclideanSpace ℂ (ZMod n))‖ =
      ‖(WithLp.toLp 2 (fun p : Fin stage.blockCount × ZMod stage.radix ↦
        eB p.1 p.2) : EuclideanSpace ℂ
          (Fin stage.blockCount × ZMod stage.radix))‖ := by
    have h := p04_l2_equiv stage.reindex E
    rw [← h]
    congr 1
    apply congrArg (WithLp.toLp 2)
    funext p
    rcases p with ⟨b, k⟩
    simp [E, eB, xB, p04_mixedBlock_apply_reindex,
      p04_roundedMixedBlock_apply_reindex]
  have hin : ‖(WithLp.toLp 2 (fun p : Fin stage.blockCount × ZMod stage.radix ↦
      xB p.1 p.2) : EuclideanSpace ℂ
        (Fin stage.blockCount × ZMod stage.radix))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
    simpa [xB] using p04_l2_equiv
      (stage.reindex.trans stage.permutation) x
  rw [p04_complexNorm2_eq_euclidean, p04_complexNorm2_eq_euclidean]
  change ‖(WithLp.toLp 2 E : EuclideanSpace ℂ (ZMod n))‖ ≤
    c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖
  rw [hout, ← hin]
  exact hglobal

private theorem p04_complexNorm2_add_le {n : ℕ} [NeZero n]
    (x y : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i ↦ x i + y i) ≤
      p04ComplexNorm2 x + p04ComplexNorm2 y := by
  rw [p04_complexNorm2_eq_euclidean,
    p04_complexNorm2_eq_euclidean,
    p04_complexNorm2_eq_euclidean]
  change ‖(WithLp.toLp 2 (x + y) : EuclideanSpace ℂ (ZMod n))‖ ≤
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ +
      ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (ZMod n))‖
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private theorem p04_exactTwiddle_isometry {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) =
      p04ComplexNorm2 x := by
  rw [p04_complexNorm2_eq_euclidean,
    p04_complexNorm2_eq_euclidean,
    EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, norm_mul, p04_stdAddChar_norm]
  · simp [p04MixedRadixTwiddleApply, h]

private theorem p04_exactTwiddle_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    (fun i ↦ p04MixedRadixTwiddleApply stage x i -
      p04MixedRadixTwiddleApply stage y i) =
        p04MixedRadixTwiddleApply stage (fun i ↦ x i - y i) := by
  funext i
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, mul_sub]
  · simp [p04MixedRadixTwiddleApply, h]

private theorem p04_roundedTwiddle_l2_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) ≤
      (model.epsilon * (3 + 2 * model.gamma) +
        model.epsilon ^ 2 * (2 + 10 * model.gamma)) *
          p04ComplexNorm2 x := by
  let e : ZMod n → ℂ := fun i ↦
    p04RoundedMixedRadixTwiddleApply model stage x i -
      p04MixedRadixTwiddleApply stage x i
  let c : ℝ := model.epsilon * (3 + 2 * model.gamma) +
    model.epsilon ^ 2 * (2 + 10 * model.gamma)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hA : 0 ≤ 3 + 2 * model.gamma := by linarith [model.gamma_nonneg]
    have hB : 0 ≤ 2 + 10 * model.gamma := by linarith [model.gamma_nonneg]
    exact add_nonneg
      (mul_nonneg (le_of_lt model.epsilon_pos) hA)
      (mul_nonneg (sq_nonneg model.epsilon) hB)
  have hpoint (i : ZMod n) : ‖e i‖ ≤ c * ‖x i‖ := by
    by_cases h : stage.useTwiddle
    · simpa [e, c, p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, h, add_mul] using
        p04_roundedRootMul_error model (stage.twiddleExponent i) (x i) hε
    · have hzero : ‖e i‖ = 0 := by
        simp [e, p04RoundedMixedRadixTwiddleApply,
          p04MixedRadixTwiddleApply, h]
      rw [hzero]
      exact mul_nonneg hc (norm_nonneg (x i))
  have h := p04_l2_pointwise_bound x e c hc hpoint
  simpa [e, c, p04_complexNorm2_eq_euclidean] using h

private noncomputable def p04_twiddleFirst {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 3 + 2 * γ else 0

private noncomputable def p04_twiddleSecond {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 2 + 10 * γ else 0

private theorem p04_twiddleFirst_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_twiddleFirst stage γ := by
  unfold p04_twiddleFirst
  split_ifs <;> linarith

private theorem p04_twiddleSecond_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_twiddleSecond stage γ := by
  unfold p04_twiddleSecond
  split_ifs <;> linarith

private theorem p04_roundedTwiddle_l2_error_conditional {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) ≤
      (model.epsilon * p04_twiddleFirst stage model.gamma +
        model.epsilon ^ 2 * p04_twiddleSecond stage model.gamma) *
          p04ComplexNorm2 x := by
  by_cases h : stage.useTwiddle
  · simpa [p04_twiddleFirst, p04_twiddleSecond, h] using
      p04_roundedTwiddle_l2_error model stage x hε
  · have heq : (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage x i -
          p04MixedRadixTwiddleApply stage x i) =
        (fun _ : ZMod n ↦ (0 : ℂ)) := by
      funext i
      simp [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, h]
    rw [heq]
    simp [p04_twiddleFirst, p04_twiddleSecond, h,
      p04ComplexNorm2, p04ComplexNorm2Sq]

private theorem p04_error_compose_second
    (ε s A B T D : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 0 ≤ T) (hD : 0 ≤ D) :
    (ε * T + ε ^ 2 * D) * (s + (ε * A + ε ^ 2 * B)) +
        (ε * A + ε ^ 2 * B) ≤
      ε * (s * T + A) +
        ε ^ 2 * (s * D + T * A + B + T * B + D * A + D * B) := by
  have h3 : ε ^ 3 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε₁)]
  have h4 : ε ^ 4 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr
      (by nlinarith [sq_nonneg (1 - ε)] : ε ^ 2 ≤ 1))]
  have hTB := mul_le_mul_of_nonneg_left h3 (mul_nonneg hT hB)
  have hDA := mul_le_mul_of_nonneg_left h3 (mul_nonneg hD hA)
  have hDB := mul_le_mul_of_nonneg_left h4 (mul_nonneg hD hB)
  nlinarith

private noncomputable def p04_stageSecond {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  let s := Real.sqrt (stage.radix : ℝ)
  let A := s * p04Alpha stage.radix γ
  let B := p04_radixBlockSecond stage.radix γ
  let T := p04_twiddleFirst stage γ
  let D := p04_twiddleSecond stage γ
  s * D + T * A + B + T * B + D * A + D * B

private theorem p04_stageSecond_nonneg {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04_stageSecond stage γ := by
  unfold p04_stageSecond
  have hA := p04_alpha_nonneg stage.radix γ hγ
  have hB := p04_radixBlockSecond_nonneg stage.radix γ hγ
  have hT := p04_twiddleFirst_nonneg stage γ hγ
  have hD := p04_twiddleSecond_nonneg stage γ hγ
  positivity

private theorem p04_roundedStage_l2_error {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (stage : P04MixedRadixStage n)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x)
    (x : ZMod n → ℂ) (hε : model.epsilon ≤ 1) :
    p04ComplexNorm2 (fun i ↦
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) ≤
      (model.epsilon * Real.sqrt (stage.radix : ℝ) *
          (p04Alpha stage.radix model.gamma +
            p04_twiddleFirst stage model.gamma) +
        model.epsilon ^ 2 * p04_stageSecond stage model.gamma) *
          p04ComplexNorm2 x := by
  let RB := p04RoundedMixedRadixBlockApply model stage x
  let EB := p04MixedRadixBlockApply stage x
  let s := Real.sqrt (stage.radix : ℝ)
  let A := s * p04Alpha stage.radix model.gamma
  let B := p04_radixBlockSecond stage.radix model.gamma
  let T := p04_twiddleFirst stage model.gamma
  let D := p04_twiddleSecond stage model.gamma
  let δB := model.epsilon * A + model.epsilon ^ 2 * B
  let δT := model.epsilon * T + model.epsilon ^ 2 * D
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hA : 0 ≤ A :=
    mul_nonneg hs (p04_alpha_nonneg stage.radix model.gamma model.gamma_nonneg)
  have hB := p04_radixBlockSecond_nonneg stage.radix model.gamma model.gamma_nonneg
  have hT := p04_twiddleFirst_nonneg stage model.gamma model.gamma_nonneg
  have hD := p04_twiddleSecond_nonneg stage model.gamma model.gamma_nonneg
  have hδT : 0 ≤ δT := by
    dsimp [δT]
    exact add_nonneg
      (mul_nonneg (le_of_lt model.epsilon_pos) hT)
      (mul_nonneg (sq_nonneg model.epsilon) hD)
  have hX : 0 ≤ p04ComplexNorm2 x := by
    unfold p04ComplexNorm2
    exact Real.sqrt_nonneg _
  have hblock := p04_mixedBlock_l2_error model stage x hε
  have hcoeffB : model.epsilon * Real.sqrt (stage.radix : ℝ) *
      p04Alpha stage.radix model.gamma +
      model.epsilon ^ 2 * p04_radixBlockSecond stage.radix model.gamma = δB := by
    dsimp [δB, A, B, s]
    ring
  rw [hcoeffB] at hblock
  change p04ComplexNorm2 (fun i ↦ RB i - EB i) ≤
    δB * p04ComplexNorm2 x at hblock
  have hEB : p04ComplexNorm2 EB = s * p04ComplexNorm2 x := by
    have h := hscale x
    simpa [p04MixedRadixStageApply, EB, s,
      p04_exactTwiddle_isometry] using h
  have hRB : p04ComplexNorm2 RB ≤
      (s + δB) * p04ComplexNorm2 x := by
    have hsplit : RB = fun i ↦ (RB i - EB i) + EB i := by
      funext i
      ring
    calc
      p04ComplexNorm2 RB =
          p04ComplexNorm2 (fun i ↦ (RB i - EB i) + EB i) :=
            congrArg p04ComplexNorm2 hsplit
      _ ≤ p04ComplexNorm2 (fun i ↦ RB i - EB i) +
          p04ComplexNorm2 EB := p04_complexNorm2_add_le _ _
      _ ≤ δB * p04ComplexNorm2 x + s * p04ComplexNorm2 x := by
        dsimp [RB, EB, δB, A, B] at hblock ⊢
        linarith [hEB]
      _ = (s + δB) * p04ComplexNorm2 x := by ring
  have htw := p04_roundedTwiddle_l2_error_conditional model stage RB hε
  have hsplit : (fun i ↦
      p04RoundedMixedRadixStageApply model stage x i -
        p04MixedRadixStageApply stage x i) =
      (fun i ↦
        (p04RoundedMixedRadixTwiddleApply model stage RB i -
          p04MixedRadixTwiddleApply stage RB i) +
          p04MixedRadixTwiddleApply stage (fun i ↦ RB i - EB i) i) := by
    funext i
    by_cases h : stage.useTwiddle
    · simp [p04RoundedMixedRadixStageApply, p04MixedRadixStageApply,
        p04MixedRadixTwiddleApply, RB, EB, h, mul_sub]
    · simp [p04RoundedMixedRadixStageApply, p04MixedRadixStageApply,
        p04MixedRadixTwiddleApply, RB, EB, h]
  rw [hsplit]
  have htri := p04_complexNorm2_add_le
    (fun i ↦ p04RoundedMixedRadixTwiddleApply model stage RB i -
      p04MixedRadixTwiddleApply stage RB i)
    (p04MixedRadixTwiddleApply stage (fun i ↦ RB i - EB i))
  have htwScaled := mul_le_mul_of_nonneg_left hRB hδT
  have hnorm := p04_exactTwiddle_isometry stage (fun i ↦ RB i - EB i)
  have hcompose := p04_error_compose_second model.epsilon s A B T D
    (le_of_lt model.epsilon_pos) hε hs hA hB hT hD
  have hcomposeScaled := mul_le_mul_of_nonneg_right hcompose hX
  have htargetCoeff : model.epsilon * s *
      (p04Alpha stage.radix model.gamma + T) +
      model.epsilon ^ 2 * p04_stageSecond stage model.gamma =
      model.epsilon * (s * T + A) +
      model.epsilon ^ 2 * (s * D + T * A + B + T * B + D * A + D * B) := by
    dsimp [p04_stageSecond, A, B, T, D, s]
    ring
  change p04ComplexNorm2 (fun i ↦
      (p04RoundedMixedRadixTwiddleApply model stage RB i -
        p04MixedRadixTwiddleApply stage RB i) +
        p04MixedRadixTwiddleApply stage (fun i ↦ RB i - EB i) i) ≤
      (model.epsilon * s *
        (p04Alpha stage.radix model.gamma + T) +
        model.epsilon ^ 2 * p04_stageSecond stage model.gamma) *
          p04ComplexNorm2 x
  rw [htargetCoeff]
  calc
    _ ≤ p04ComplexNorm2 (fun i ↦
        p04RoundedMixedRadixTwiddleApply model stage RB i -
          p04MixedRadixTwiddleApply stage RB i) +
        p04ComplexNorm2 (p04MixedRadixTwiddleApply stage
          (fun i ↦ RB i - EB i)) := htri
    _ ≤ δT * p04ComplexNorm2 RB + δB * p04ComplexNorm2 x := by
      rw [hnorm]
      exact add_le_add htw hblock
    _ ≤ δT * ((s + δB) * p04ComplexNorm2 x) +
        δB * p04ComplexNorm2 x := by
      exact add_le_add (mul_le_mul_of_nonneg_left hRB hδT) le_rfl
    _ ≤ (model.epsilon * (s * T + A) +
        model.epsilon ^ 2 *
          (s * D + T * A + B + T * B + D * A + D * B)) *
            p04ComplexNorm2 x := by
      dsimp [δT, δB]
      nlinarith [hcomposeScaled]

private theorem p04_exactBlock_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixBlockApply stage (fun i ↦ x i - y i) =
      (fun i ↦ p04MixedRadixBlockApply stage x i -
        p04MixedRadixBlockApply stage y i) := by
  funext i
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  simp [p04MixedRadixBlockApply, mul_sub, ← Finset.sum_sub_distrib]

private theorem p04_exactStage_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x y : ZMod n → ℂ) :
    p04MixedRadixStageApply stage (fun i ↦ x i - y i) =
      (fun i ↦ p04MixedRadixStageApply stage x i -
        p04MixedRadixStageApply stage y i) := by
  rw [p04MixedRadixStageApply, p04_exactBlock_sub]
  exact (p04_exactTwiddle_sub stage
    (p04MixedRadixBlockApply stage x)
    (p04MixedRadixBlockApply stage y)).symm

private noncomputable def p04_exactStageList {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (l : List (Fin plan.stageCount))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state i ↦ p04MixedRadixStageApply (plan.stage i) state) x

private noncomputable def p04_roundedStageList {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (l : List (Fin plan.stageCount))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state i ↦
    p04RoundedMixedRadixStageApply model (plan.stage i) state) x

private noncomputable def p04_stageListScale {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (l : List (Fin plan.stageCount)) : ℝ :=
  (l.map fun i ↦ Real.sqrt ((plan.stage i).radix : ℝ)).prod

private noncomputable def p04_stageListFirst {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ)
    (l : List (Fin plan.stageCount)) : ℝ :=
  (l.map fun i ↦ p04Alpha (plan.stage i).radix γ +
    p04_twiddleFirst (plan.stage i) γ).sum

private theorem p04_stageListScale_nonneg {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n)
    (l : List (Fin plan.stageCount)) :
    0 ≤ p04_stageListScale plan l := by
  unfold p04_stageListScale
  apply List.prod_nonneg
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact Real.sqrt_nonneg _

private theorem p04_stageListFirst_nonneg {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (l : List (Fin plan.stageCount)) :
    0 ≤ p04_stageListFirst plan γ l := by
  unfold p04_stageListFirst
  apply List.sum_nonneg
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  exact add_nonneg
    (p04_alpha_nonneg (plan.stage i).radix γ hγ)
    (p04_twiddleFirst_nonneg (plan.stage i) γ hγ)

private theorem p04_exactStageList_norm {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n)
    (l : List (Fin plan.stageCount)) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04_exactStageList plan l x) =
      p04_stageListScale plan l * p04ComplexNorm2 x := by
  induction l using List.reverseRecOn with
  | nil =>
      simp [p04_exactStageList, p04_stageListScale]
  | append_singleton l i ih =>
      simp only [p04_exactStageList, List.foldl_append, List.foldl_cons,
        List.foldl_nil, p04_stageListScale, List.map_append,
        List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil]
      rw [plan.stage_norm_scaling i]
      have ih' : p04ComplexNorm2
          (List.foldl (fun state j ↦ p04MixedRadixStageApply (plan.stage j) state) x l) =
            (List.map (fun j ↦ Real.sqrt ((plan.stage j).radix : ℝ)) l).prod *
              p04ComplexNorm2 x := by
        simpa [p04_exactStageList, p04_stageListScale] using ih
      rw [ih']
      ring

private theorem p04_error_compose_scaled
    (ε P A B s T D : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (hT : 0 ≤ T) (hD : 0 ≤ D) :
    (ε * T + ε ^ 2 * D) * (P + (ε * A + ε ^ 2 * B)) +
        s * (ε * A + ε ^ 2 * B) ≤
      ε * (P * T + s * A) +
        ε ^ 2 * (P * D + T * A + s * B + T * B + D * A + D * B) := by
  have h3 : ε ^ 3 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε₁)]
  have h4 : ε ^ 4 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr
      (by nlinarith [sq_nonneg (1 - ε)] : ε ^ 2 ≤ 1))]
  have hTB := mul_le_mul_of_nonneg_left h3 (mul_nonneg hT hB)
  have hDA := mul_le_mul_of_nonneg_left h3 (mul_nonneg hD hA)
  have hDB := mul_le_mul_of_nonneg_left h4 (mul_nonneg hD hB)
  nlinarith

private theorem p04_stageList_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ)
    (l : List (Fin plan.stageCount)) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ model : P04WilkinsonModel, model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2 (fun j ↦
            p04_roundedStageList plan model l x j -
              p04_exactStageList plan l x j) ≤
            (model.epsilon * p04_stageListScale plan l *
                p04_stageListFirst plan γ l +
              model.epsilon ^ 2 * C₂) * p04ComplexNorm2 x := by
  induction l using List.reverseRecOn with
  | nil =>
      refine ⟨0, le_refl _, ?_⟩
      intro model hmodel hε x
      simp [p04_roundedStageList, p04_exactStageList,
        p04_stageListScale, p04_stageListFirst,
        p04ComplexNorm2, p04ComplexNorm2Sq]
  | append_singleton l i ih =>
      obtain ⟨B, hB, hprev⟩ := ih
      let P := p04_stageListScale plan l
      let K := p04_stageListFirst plan γ l
      let s := Real.sqrt ((plan.stage i).radix : ℝ)
      let t := s * (p04Alpha (plan.stage i).radix γ +
        p04_twiddleFirst (plan.stage i) γ)
      let D := p04_stageSecond (plan.stage i) γ
      let A := P * K
      let C₂ := P * D + t * A + s * B + t * B + D * A + D * B
      have hP : 0 ≤ P := p04_stageListScale_nonneg plan l
      have hK : 0 ≤ K := p04_stageListFirst_nonneg plan γ hγ l
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have ht : 0 ≤ t := by
        dsimp [t]
        exact mul_nonneg hs (add_nonneg
          (p04_alpha_nonneg _ γ hγ)
          (p04_twiddleFirst_nonneg _ γ hγ))
      have hD : 0 ≤ D := p04_stageSecond_nonneg _ γ hγ
      have hA : 0 ≤ A := mul_nonneg hP hK
      have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
      refine ⟨C₂, hC₂, ?_⟩
      intro model hmodel hε x
      let R0 := p04_roundedStageList plan model l x
      let E0 := p04_exactStageList plan l x
      let δ := model.epsilon * A + model.epsilon ^ 2 * B
      let τ := model.epsilon * t + model.epsilon ^ 2 * D
      have hδ : 0 ≤ δ := by
        dsimp [δ]
        exact add_nonneg
          (mul_nonneg (le_of_lt model.epsilon_pos) hA)
          (mul_nonneg (sq_nonneg model.epsilon) hB)
      have hτ : 0 ≤ τ := by
        dsimp [τ]
        exact add_nonneg
          (mul_nonneg (le_of_lt model.epsilon_pos) ht)
          (mul_nonneg (sq_nonneg model.epsilon) hD)
      have hX : 0 ≤ p04ComplexNorm2 x := by
        unfold p04ComplexNorm2
        exact Real.sqrt_nonneg _
      have hprev' := hprev model hmodel hε x
      have hcoeffPrev : model.epsilon * P * K + model.epsilon ^ 2 * B = δ := by
        dsimp [δ, A]
        ring
      rw [hcoeffPrev] at hprev'
      change p04ComplexNorm2 (fun j ↦ R0 j - E0 j) ≤
        δ * p04ComplexNorm2 x at hprev'
      have hE0 : p04ComplexNorm2 E0 = P * p04ComplexNorm2 x :=
        p04_exactStageList_norm plan l x
      have hR0 : p04ComplexNorm2 R0 ≤
          (P + δ) * p04ComplexNorm2 x := by
        have hsplit : R0 = fun j ↦ (R0 j - E0 j) + E0 j := by
          funext j
          ring
        calc
          p04ComplexNorm2 R0 =
              p04ComplexNorm2 (fun j ↦ (R0 j - E0 j) + E0 j) :=
                congrArg p04ComplexNorm2 hsplit
          _ ≤ p04ComplexNorm2 (fun j ↦ R0 j - E0 j) +
              p04ComplexNorm2 E0 := p04_complexNorm2_add_le _ _
          _ ≤ δ * p04ComplexNorm2 x + P * p04ComplexNorm2 x := by
            rw [hE0]
            linarith
          _ = (P + δ) * p04ComplexNorm2 x := by ring
      have hstage := p04_roundedStage_l2_error model (plan.stage i)
        (plan.stage_norm_scaling i) R0 hε
      rw [hmodel] at hstage
      have hcoeffStage : model.epsilon * s *
          (p04Alpha (plan.stage i).radix γ +
            p04_twiddleFirst (plan.stage i) γ) +
          model.epsilon ^ 2 * p04_stageSecond (plan.stage i) γ = τ := by
        dsimp [τ, t, D]
        ring
      rw [hcoeffStage] at hstage
      have hstage' : p04ComplexNorm2 (fun j ↦
          p04RoundedMixedRadixStageApply model (plan.stage i) R0 j -
            p04MixedRadixStageApply (plan.stage i) R0 j) ≤
          τ * p04ComplexNorm2 R0 := hstage
      have hRlist : p04_roundedStageList plan model (l ++ [i]) x =
          p04RoundedMixedRadixStageApply model (plan.stage i) R0 := by
        simp [p04_roundedStageList, R0, List.foldl_append]
      have hElist : p04_exactStageList plan (l ++ [i]) x =
          p04MixedRadixStageApply (plan.stage i) E0 := by
        simp [p04_exactStageList, E0, List.foldl_append]
      have hscale := plan.stage_norm_scaling i (fun j ↦ R0 j - E0 j)
      have hsplit : (fun j ↦
          p04_roundedStageList plan model (l ++ [i]) x j -
            p04_exactStageList plan (l ++ [i]) x j) =
          (fun j ↦
            (p04RoundedMixedRadixStageApply model (plan.stage i) R0 j -
              p04MixedRadixStageApply (plan.stage i) R0 j) +
            p04MixedRadixStageApply (plan.stage i)
              (fun j ↦ R0 j - E0 j) j) := by
        rw [hRlist, hElist, p04_exactStage_sub]
        funext j
        ring
      rw [hsplit]
      have htri := p04_complexNorm2_add_le
        (fun j ↦ p04RoundedMixedRadixStageApply model (plan.stage i) R0 j -
          p04MixedRadixStageApply (plan.stage i) R0 j)
        (p04MixedRadixStageApply (plan.stage i)
          (fun j ↦ R0 j - E0 j))
      have hτScaled := mul_le_mul_of_nonneg_left hR0 hτ
      have hscalePrev := mul_le_mul_of_nonneg_left hprev' hs
      have hcompose := p04_error_compose_scaled model.epsilon P A B s t D
        (le_of_lt model.epsilon_pos) hε hP hA hB hs ht hD
      have hcomposeScaled := mul_le_mul_of_nonneg_right hcompose hX
      have hcoeffFinal :
          model.epsilon * p04_stageListScale plan (l ++ [i]) *
              p04_stageListFirst plan γ (l ++ [i]) +
            model.epsilon ^ 2 * C₂ =
          model.epsilon * (P * t + s * A) + model.epsilon ^ 2 * C₂ := by
        simp [p04_stageListScale, p04_stageListFirst,
          List.map_append, List.prod_append, List.sum_append,
          P, K, A, t, s]
        ring
      rw [hcoeffFinal]
      calc
        _ ≤ p04ComplexNorm2 (fun j ↦
            p04RoundedMixedRadixStageApply model (plan.stage i) R0 j -
              p04MixedRadixStageApply (plan.stage i) R0 j) +
            p04ComplexNorm2 (p04MixedRadixStageApply (plan.stage i)
              (fun j ↦ R0 j - E0 j)) := htri
        _ ≤ τ * p04ComplexNorm2 R0 +
            s * p04ComplexNorm2 (fun j ↦ R0 j - E0 j) := by
          rw [hscale]
          exact add_le_add hstage' le_rfl
        _ ≤ τ * ((P + δ) * p04ComplexNorm2 x) +
            s * (δ * p04ComplexNorm2 x) := by
          exact add_le_add hτScaled hscalePrev
        _ ≤ (model.epsilon * (P * t + s * A) +
            model.epsilon ^ 2 * C₂) * p04ComplexNorm2 x := by
          dsimp [δ, τ, C₂]
          nlinarith [hcomposeScaled]

private theorem p04_sum_twiddle_indices (r : ℕ) (c : ℝ) :
    (∑ i : Fin r, if i.val + 1 < r then c else 0) =
      (r - 1 : ℕ) * c := by
  cases r with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_castSucc]
      have hcast (i : Fin n) : i.val + 1 < n + 1 := by omega
      simp [hcast, Finset.sum_const]

private theorem p04_stageListFirst_all {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    p04_stageListFirst plan γ
        (List.ofFn (fun i : Fin plan.stageCount ↦ i)) =
      p04K plan γ := by
  have htw : (∑ i : Fin plan.stageCount,
      p04_twiddleFirst (plan.stage i) γ) =
      (plan.stageCount - 1 : ℕ) * (3 + 2 * γ) := by
    calc
      (∑ i : Fin plan.stageCount,
          p04_twiddleFirst (plan.stage i) γ) =
          ∑ i : Fin plan.stageCount,
            if i.val + 1 < plan.stageCount then 3 + 2 * γ else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [p04_twiddleFirst, plan.twiddle_pattern i]
      _ = _ := p04_sum_twiddle_indices plan.stageCount (3 + 2 * γ)
  have hcast : ((plan.stageCount - 1 : ℕ) : ℝ) =
      (plan.stageCount : ℝ) - 1 := Nat.cast_pred plan.stageCount_pos
  simp only [p04_stageListFirst, List.map_ofFn, List.sum_ofFn]
  change (∑ i : Fin plan.stageCount,
      (p04Alpha (plan.stage i).radix γ +
        p04_twiddleFirst (plan.stage i) γ)) = p04K plan γ
  rw [Finset.sum_add_distrib, htw, hcast]
  rfl

private theorem p04_stageListScale_all {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) :
    p04_stageListScale plan
        (List.ofFn (fun i : Fin plan.stageCount ↦ i)) =
      Real.sqrt (n : ℝ) := by
  have hcast : (∏ i : Fin plan.stageCount,
      ((plan.stage i).radix : ℝ)) = (n : ℝ) := by
    exact_mod_cast plan.order_factorization
  have hsqrt := Real.sqrt_prod (s := Finset.univ)
    (x := fun i : Fin plan.stageCount ↦ ((plan.stage i).radix : ℝ))
    (by intro i hi; exact Nat.cast_nonneg _)
  simp only [p04_stageListScale, List.map_ofFn, List.prod_ofFn]
  change (∏ i : Fin plan.stageCount,
      Real.sqrt ((plan.stage i).radix : ℝ)) = Real.sqrt (n : ℝ)
  rw [← hsqrt, hcast]

private theorem p04_exactStageList_all {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (x : ZMod n → ℂ) :
    p04_exactStageList plan
        (List.ofFn (fun i : Fin plan.stageCount ↦ i)) x =
      p04ApplyMixedRadixStages plan.stage x := by
  have hlist : List.ofFn plan.stage =
      (List.ofFn (fun i : Fin plan.stageCount ↦ i)).map plan.stage := by
    rw [List.map_ofFn]
    rfl
  change (List.ofFn (fun i : Fin plan.stageCount ↦ i)).foldl
      (fun state i ↦ p04MixedRadixStageApply (plan.stage i) state) x =
    (List.ofFn plan.stage).foldl
      (fun state stage ↦ p04MixedRadixStageApply stage state) x
  rw [hlist, List.foldl_map]

private theorem p04_roundedStageList_all {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (model : P04WilkinsonModel)
    (x : ZMod n → ℂ) :
    p04_roundedStageList plan model
        (List.ofFn (fun i : Fin plan.stageCount ↦ i)) x =
      p04ApplyRoundedMixedRadixStages model plan.stage x := by
  have hlist : List.ofFn plan.stage =
      (List.ofFn (fun i : Fin plan.stageCount ↦ i)).map plan.stage := by
    rw [List.map_ofFn]
    rfl
  change (List.ofFn (fun i : Fin plan.stageCount ↦ i)).foldl
      (fun state i ↦ p04RoundedMixedRadixStageApply model (plan.stage i) state) x =
    (List.ofFn plan.stage).foldl
      (fun state stage ↦ p04RoundedMixedRadixStageApply model stage state) x
  rw [hlist, List.foldl_map]

private theorem p04_roundedFft_l2_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ model : P04WilkinsonModel, model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : ZMod n → ℂ,
          p04ComplexNorm2 (fun i ↦
            p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
          (model.epsilon * Real.sqrt (n : ℝ) * p04K plan γ +
            model.epsilon ^ 2 * C₂) * p04ComplexNorm2 x := by
  let l : List (Fin plan.stageCount) := List.ofFn (fun i ↦ i)
  obtain ⟨C₂, hC₂, hbound⟩ := p04_stageList_error plan γ hγ l
  refine ⟨C₂, hC₂, ?_⟩
  intro model hmodel hε x
  let R := p04_roundedStageList plan model l x
  let E := p04_exactStageList plan l x
  have hR : p04RoundedFftApply plan model x =
      fun i ↦ R (plan.finalPermutation i) := by
    change p04Permute plan.finalPermutation
      (p04ApplyRoundedMixedRadixStages model plan.stage x) =
        fun i ↦ R (plan.finalPermutation i)
    rw [← p04_roundedStageList_all plan model x]
    rfl
  have hE : p04FourierTransform x =
      fun i ↦ E (plan.finalPermutation i) := by
    rw [← plan.exact_factorization x,
      ← p04_exactStageList_all plan x]
    rfl
  have hperm : p04ComplexNorm2 (fun i ↦
        R (plan.finalPermutation i) - E (plan.finalPermutation i)) =
      p04ComplexNorm2 (fun i ↦ R i - E i) := by
    rw [p04_complexNorm2_eq_euclidean, p04_complexNorm2_eq_euclidean]
    exact p04_l2_equiv plan.finalPermutation (fun i ↦ R i - E i)
  rw [hR, hE, hperm]
  have h := hbound model hmodel hε x
  rw [p04_stageListScale_all, p04_stageListFirst_all] at h
  exact h

private noncomputable def p04_axisSplitEquiv {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    P04MultiIndex axis ≃
      ((j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order) ×
        ZMod (axis i).order :=
  (Equiv.piSplitAt i (fun j ↦ ZMod (axis j).order)).trans
    (Equiv.prodComm _ _)

private theorem p04_axisSplit_update {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (v : P04MultiIndex axis) (j : ZMod (axis i).order) :
    p04_axisSplitEquiv axis i (Function.update v i j) =
      ((p04_axisSplitEquiv axis i v).1, j) := by
  classical
  apply Prod.ext
  · funext k
    have hk : k.1 ≠ i := k.2
    simp [p04_axisSplitEquiv, Equiv.piSplitAt_apply,
      Function.update_apply, hk]
  · simp [p04_axisSplitEquiv, Equiv.piSplitAt_apply,
      Function.update_apply]

private theorem p04_axisSplit_symm_update {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : (j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order)
    (k j : ZMod (axis i).order) :
    Function.update ((p04_axisSplitEquiv axis i).symm (r, k)) i j =
      (p04_axisSplitEquiv axis i).symm (r, j) := by
  apply (p04_axisSplitEquiv axis i).injective
  rw [p04_axisSplit_update]
  simp

private theorem p04_axisSplit_symm_coord {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (r : (j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order)
    (k : ZMod (axis i).order) :
    ((p04_axisSplitEquiv axis i).symm (r, k)) i = k := by
  have h := (p04_axisSplitEquiv axis i).apply_symm_apply (r, k)
  have h₂ := congrArg Prod.snd h
  simpa [p04_axisSplitEquiv, Equiv.piSplitAt_apply] using h₂

private theorem p04_coordinate_apply_split {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis)
    (r : (j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order)
    (k : ZMod (axis i).order) :
    p04CoordinateTransform axis i x
        ((p04_axisSplitEquiv axis i).symm (r, k)) =
      p04FourierTransform
        (fun j ↦ x ((p04_axisSplitEquiv axis i).symm (r, j))) k := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp [p04CoordinateTransform, p04FourierTransform,
    p04_axisSplit_symm_update, p04_axisSplit_symm_coord]

private theorem p04_roundedCoordinate_apply_split {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (model : P04WilkinsonModel) (x : P04MultiArray axis)
    (r : (j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order)
    (k : ZMod (axis i).order) :
    p04RoundedCoordinateTransform axis i model x
        ((p04_axisSplitEquiv axis i).symm (r, k)) =
      p04RoundedFftApply (axis i).plan model
        (fun j ↦ x ((p04_axisSplitEquiv axis i).symm (r, j))) k := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  simp [p04RoundedCoordinateTransform,
    p04_axisSplit_symm_update, p04_axisSplit_symm_coord]

private theorem p04_axisK_nonneg (axis : P04FftAxis)
    (γ : ℝ) (hγ : 0 ≤ γ) : 0 ≤ p04AxisK axis γ := by
  change 0 ≤ p04K axis.plan γ
  rw [← p04_stageListFirst_all axis.plan γ]
  exact p04_stageListFirst_nonneg axis.plan γ hγ _

private theorem p04_coordinate_l2_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ model : P04WilkinsonModel, model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : P04MultiArray axis,
          p04MultiNorm2 (fun index ↦
            p04RoundedCoordinateTransform axis i model x index -
              p04CoordinateTransform axis i x index) ≤
            (model.epsilon * Real.sqrt ((axis i).order : ℝ) *
                p04AxisK (axis i) γ +
              model.epsilon ^ 2 * C₂) * p04MultiNorm2 x := by
  letI (j : Fin m) : NeZero (axis j).order :=
    ⟨Nat.ne_of_gt (axis j).order_pos⟩
  letI : Fintype (P04MultiIndex axis) := p04MultiIndexFintype axis
  letI (j : {j : Fin m // j ≠ i}) : NeZero (axis j.1).order :=
    ⟨Nat.ne_of_gt (axis j.1).order_pos⟩
  let rest := (j : {j : Fin m // j ≠ i}) → ZMod (axis j.1).order
  letI : Fintype rest := inferInstance
  let split := p04_axisSplitEquiv axis i
  obtain ⟨C₂, hC₂, hFFT⟩ :=
    p04_roundedFft_l2_error (axis i).plan γ hγ
  refine ⟨C₂, hC₂, ?_⟩
  intro model hmodel hε x
  let xB : rest → ZMod (axis i).order → ℂ :=
    fun r k ↦ x (split.symm (r, k))
  let eB : rest → ZMod (axis i).order → ℂ :=
    fun r k ↦ p04RoundedFftApply (axis i).plan model (xB r) k -
      p04FourierTransform (xB r) k
  let c := model.epsilon * Real.sqrt ((axis i).order : ℝ) *
      p04AxisK (axis i) γ + model.epsilon ^ 2 * C₂
  have hc : 0 ≤ c := by
    dsimp [c]
    have hK := p04_axisK_nonneg (axis i) γ hγ
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt model.epsilon_pos) (Real.sqrt_nonneg _)) hK)
      (mul_nonneg (sq_nonneg model.epsilon) hC₂)
  have hblock (r : rest) :
      ‖(WithLp.toLp 2 (eB r) : EuclideanSpace ℂ (ZMod (axis i).order))‖ ≤
        c * ‖(WithLp.toLp 2 (xB r) :
          EuclideanSpace ℂ (ZMod (axis i).order))‖ := by
    have h := hFFT model hmodel hε (xB r)
    simpa [eB, c, p04AxisK, p04_complexNorm2_eq_euclidean] using h
  have hglobal := p04_l2_block_bound xB eB c hc hblock
  let E : P04MultiArray axis := fun index ↦
    p04RoundedCoordinateTransform axis i model x index -
      p04CoordinateTransform axis i x index
  have hout : ‖(WithLp.toLp 2 E :
      EuclideanSpace ℂ (P04MultiIndex axis))‖ =
      ‖(WithLp.toLp 2 (fun p : rest × ZMod (axis i).order ↦
        eB p.1 p.2) :
          EuclideanSpace ℂ (rest × ZMod (axis i).order))‖ := by
    have h := p04_l2_equiv split.symm E
    rw [← h]
    congr 1
    apply congrArg (WithLp.toLp 2)
    funext p
    rcases p with ⟨r, k⟩
    simp [E, eB, xB, split, p04_coordinate_apply_split,
      p04_roundedCoordinate_apply_split]
  have hin : ‖(WithLp.toLp 2 (fun p : rest × ZMod (axis i).order ↦
      xB p.1 p.2) : EuclideanSpace ℂ
        (rest × ZMod (axis i).order))‖ =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))‖ := by
    simpa [xB, split] using p04_l2_equiv split.symm x
  change ‖(WithLp.toLp 2 E : EuclideanSpace ℂ
      (P04MultiIndex axis))‖ ≤
    c * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ
      (P04MultiIndex axis))‖
  rw [hout, ← hin]
  exact hglobal

private theorem p04_multiCardinality_pos {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    0 < p04MultiCardinality axis := by
  unfold p04MultiCardinality
  exact Finset.prod_pos fun i hi ↦ (axis i).order_pos

private theorem p04_multiRms_den_pos {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    0 < Real.sqrt (p04MultiCardinality axis : ℝ) := by
  apply Real.sqrt_pos.2
  exact_mod_cast p04_multiCardinality_pos axis

private theorem p04_multiRms_nonneg {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    0 ≤ p04MultiRms x := by
  unfold p04MultiRms p04MultiNorm2
  positivity

private theorem p04_multiRms_add_le {m : ℕ}
    {axis : Fin m → P04FftAxis}
    (x y : P04MultiArray axis) :
    p04MultiRms (fun index ↦ x index + y index) ≤
      p04MultiRms x + p04MultiRms y := by
  letI : Fintype (P04MultiIndex axis) := p04MultiIndexFintype axis
  have hnorm : p04MultiNorm2 (fun index ↦ x index + y index) ≤
      p04MultiNorm2 x + p04MultiNorm2 y := by
    unfold p04MultiNorm2
    change ‖(WithLp.toLp 2 (x + y) :
        EuclideanSpace ℂ (P04MultiIndex axis))‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (P04MultiIndex axis))‖ +
        ‖(WithLp.toLp 2 y : EuclideanSpace ℂ (P04MultiIndex axis))‖
    rw [WithLp.toLp_add]
    exact norm_add_le _ _
  unfold p04MultiRms
  have h := div_le_div_of_nonneg_right hnorm
    (le_of_lt (p04_multiRms_den_pos axis))
  simpa [add_div] using h

private theorem p04_coordinate_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x y : P04MultiArray axis) :
    p04CoordinateTransform axis i (fun index ↦ x index - y index) =
      (fun index ↦ p04CoordinateTransform axis i x index -
        p04CoordinateTransform axis i y index) := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  funext index
  simp [p04CoordinateTransform, mul_sub, ← Finset.sum_sub_distrib]

private theorem p04_coordinateNat_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : ℕ)
    (x y : P04MultiArray axis) :
    p04CoordinateTransformNat axis i (fun index ↦ x index - y index) =
      (fun index ↦ p04CoordinateTransformNat axis i x index -
        p04CoordinateTransformNat axis i y index) := by
  unfold p04CoordinateTransformNat
  split_ifs with h
  · exact p04_coordinate_sub axis ⟨i, h⟩ x y
  · rfl

private theorem p04_prefix_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ)
    (x y : P04MultiArray axis) :
    p04ApplyCoordinatePrefix axis k (fun index ↦ x index - y index) =
      (fun index ↦ p04ApplyCoordinatePrefix axis k x index -
        p04ApplyCoordinatePrefix axis k y index) := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
      simp only [p04ApplyCoordinatePrefix]
      rw [p04_coordinateNat_sub]
      exact ih _ _

private theorem p04_prefixProduct_succ {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    p04PrefixOrderProduct axis (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
      p04PrefixOrderProduct axis i.val (Nat.le_of_lt i.isLt) *
        (axis i).order := by
  unfold p04PrefixOrderProduct
  rw [Fin.prod_univ_castSucc]
  congr 1

private theorem p04_prefixSqrt_succ {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    Real.sqrt (p04PrefixOrderProduct axis (i.val + 1)
      (Nat.succ_le_of_lt i.isLt) : ℝ) =
      Real.sqrt (p04PrefixOrderProduct axis i.val
        (Nat.le_of_lt i.isLt) : ℝ) *
        Real.sqrt ((axis i).order : ℝ) := by
  rw [p04_prefixProduct_succ]
  push_cast
  exact Real.sqrt_mul (Nat.cast_nonneg _) _

private theorem p04_coordinate_rms_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ model : P04WilkinsonModel, model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : P04MultiArray axis,
          p04MultiRms (fun index ↦
            p04RoundedCoordinateTransform axis i model x index -
              p04CoordinateTransform axis i x index) ≤
            Real.sqrt ((axis i).order : ℝ) *
              (model.epsilon * p04AxisK (axis i) γ +
                model.epsilon ^ 2 * C₂) * p04MultiRms x := by
  obtain ⟨C₂, hC₂, hnorm⟩ := p04_coordinate_l2_error axis i γ hγ
  refine ⟨C₂, hC₂, ?_⟩
  intro model hmodel hε x
  let e : P04MultiArray axis := fun index ↦
    p04RoundedCoordinateTransform axis i model x index -
      p04CoordinateTransform axis i x index
  let s := Real.sqrt ((axis i).order : ℝ)
  let a := model.epsilon * s * p04AxisK (axis i) γ +
    model.epsilon ^ 2 * C₂
  let b := s * (model.epsilon * p04AxisK (axis i) γ +
    model.epsilon ^ 2 * C₂)
  have hnorm' : p04MultiNorm2 e ≤ a * p04MultiNorm2 x :=
    hnorm model hmodel hε x
  have hsmall : p04MultiRms e ≤ a * p04MultiRms x := by
    unfold p04MultiRms
    calc
      p04MultiNorm2 e / Real.sqrt (p04MultiCardinality axis : ℝ) ≤
          (a * p04MultiNorm2 x) /
            Real.sqrt (p04MultiCardinality axis : ℝ) :=
        div_le_div_of_nonneg_right hnorm'
          (le_of_lt (p04_multiRms_den_pos axis))
      _ = a * (p04MultiNorm2 x /
          Real.sqrt (p04MultiCardinality axis : ℝ)) := by ring
  have hq1 : 1 ≤ (axis i).order := by
    have hp := (axis i).order_pos
    omega
  have hs1 : (1 : ℝ) ≤ s := by
    dsimp [s]
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hq1
  have hab : a ≤ b := by
    dsimp [a, b]
    have h := mul_nonneg (show 0 ≤ s - 1 by linarith)
      (mul_nonneg (sq_nonneg model.epsilon) hC₂)
    nlinarith
  have h := mul_le_mul_of_nonneg_right hab (p04_multiRms_nonneg x)
  exact hsmall.trans h

private theorem p04_propagated_coordinate_rms_error {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (i : Fin m) (model : P04WilkinsonModel)
    (x : P04MultiArray plan.axis) (C₂ : ℝ)
    (hcoord : p04MultiRms (fun index ↦
      p04RoundedCoordinateTransform plan.axis i model x index -
        p04CoordinateTransform plan.axis i x index) ≤
      Real.sqrt ((plan.axis i).order : ℝ) *
        (model.epsilon * p04AxisK (plan.axis i) γ +
          model.epsilon ^ 2 * C₂) * p04MultiRms x) :
    p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val
      (fun index ↦
        p04RoundedCoordinateTransform plan.axis i model x index -
          p04CoordinateTransform plan.axis i x index)) ≤
      (model.epsilon * p04AxisK (plan.axis i) γ +
        model.epsilon ^ 2 * C₂) *
        p04MultiRms (p04ApplyCoordinatePrefix plan.axis (i.val + 1) x) := by
  let coeff := model.epsilon * p04AxisK (plan.axis i) γ +
    model.epsilon ^ 2 * C₂
  let e : P04MultiArray plan.axis := fun index ↦
    p04RoundedCoordinateTransform plan.axis i model x index -
      p04CoordinateTransform plan.axis i x index
  have hpre := plan.prefix_rms_scaling i.val (Nat.le_of_lt i.isLt) e
  have hnext := plan.prefix_rms_scaling (i.val + 1)
    (Nat.succ_le_of_lt i.isLt) x
  have hscaled := mul_le_mul_of_nonneg_left hcoord
    (Real.sqrt_nonneg (p04PrefixOrderProduct plan.axis i.val
      (Nat.le_of_lt i.isLt) : ℝ))
  change p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val e) ≤
    coeff * p04MultiRms (p04ApplyCoordinatePrefix plan.axis (i.val + 1) x)
  rw [hpre, hnext]
  rw [p04_prefixSqrt_succ]
  dsimp [coeff]
  nlinarith

private noncomputable def p04_suffixAxisK {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (j : Fin (m + 1)) : ℝ :=
  ∑ i : Fin m, if j.val ≤ i.val then p04AxisK (plan.axis i) γ else 0

private theorem p04_suffixAxisK_nonneg {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (hγ : 0 ≤ γ) (j : Fin (m + 1)) :
    0 ≤ p04_suffixAxisK plan γ j := by
  unfold p04_suffixAxisK
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact p04_axisK_nonneg (plan.axis i) γ hγ
  · exact le_refl _

private theorem p04_suffixAxisK_last {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ) :
    p04_suffixAxisK plan γ (Fin.last m) = 0 := by
  unfold p04_suffixAxisK
  apply Finset.sum_eq_zero
  intro i hi
  simp [Fin.isLt]

private theorem p04_suffixAxisK_step {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (i : Fin m) :
    p04_suffixAxisK plan γ i.castSucc =
      p04AxisK (plan.axis i) γ +
        p04_suffixAxisK plan γ i.succ := by
  unfold p04_suffixAxisK
  calc
    (∑ j : Fin m,
        if i.castSucc.val ≤ j.val then p04AxisK (plan.axis j) γ else 0) =
      ∑ j : Fin m,
        ((if j = i then p04AxisK (plan.axis j) γ else 0) +
          (if i.succ.val ≤ j.val then p04AxisK (plan.axis j) γ else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [Fin.val_castSucc, Fin.val_succ]
            by_cases hji : j = i
            · subst j
              simp
            · have hval : j.val ≠ i.val := by
                intro h
                exact hji (Fin.ext h)
              by_cases hlt : i.val < j.val
              · have hsucc : i.val + 1 ≤ j.val := by omega
                simp only [if_pos hlt.le, if_neg hji, if_pos hsucc,
                  zero_add]
              · have hless : ¬ i.val ≤ j.val := by omega
                have hsucc : ¬ i.val + 1 ≤ j.val := by omega
                simp only [if_neg hless, if_neg hji, if_neg hsucc,
                  add_zero]
    _ = p04AxisK (plan.axis i) γ +
        ∑ j : Fin m,
          (if i.succ.val ≤ j.val then p04AxisK (plan.axis j) γ else 0) := by
      rw [Finset.sum_add_distrib]
      simp

private theorem p04_suffixAxisK_zero {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ) :
    p04_suffixAxisK plan γ (0 : Fin (m + 1)) =
      ∑ i : Fin m, p04AxisK (plan.axis i) γ := by
  simp [p04_suffixAxisK]

private theorem p04_prefix_succ_coord {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04ApplyCoordinatePrefix axis (i.val + 1) x =
      p04ApplyCoordinatePrefix axis i.val
        (p04CoordinateTransform axis i x) := by
  simp [p04ApplyCoordinatePrefix, p04CoordinateTransformNat, i.isLt]

private noncomputable def p04_familyPrefixErrorRms {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) (j : Fin (m + 1)) : ℝ :=
  p04MultiRms (fun index ↦
    p04ApplyCoordinatePrefix plan.axis j.val
      ((family.run ε).computedState j) index -
        p04FamilyMultiExactOutput family index)

private theorem p04_familyPrefixErrorRms_nonneg {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) (j : Fin (m + 1)) :
    0 ≤ p04_familyPrefixErrorRms family ε j :=
  p04_multiRms_nonneg _

private theorem p04_familyPrefixErrorRms_last {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) :
    p04_familyPrefixErrorRms family ε (Fin.last m) = 0 := by
  have hinput : (family.run ε).computedState (Fin.last m) = family.input := by
    rw [(family.run ε).computed_input, family.run_input]
  unfold p04_familyPrefixErrorRms
  rw [hinput]
  simp only [Fin.val_last]
  have heq : (fun index ↦
      p04ApplyCoordinatePrefix plan.axis m family.input index -
        p04FamilyMultiExactOutput family index) =
      (0 : P04MultiArray plan.axis) := by
    funext index
    simp [p04FamilyMultiExactOutput]
  rw [heq]
  simp [p04MultiRms, p04MultiNorm2]

private theorem p04_familyPrefixErrorRms_step {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) (i : Fin m) :
    p04_familyPrefixErrorRms family ε i.castSucc ≤
      p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val
        (fun index ↦
          p04RoundedCoordinateTransform plan.axis i (family.model ε)
              ((family.run ε).computedState i.succ) index -
            p04CoordinateTransform plan.axis i
              ((family.run ε).computedState i.succ) index)) +
        p04_familyPrefixErrorRms family ε i.succ := by
  let x := (family.run ε).computedState i.succ
  let R := p04RoundedCoordinateTransform plan.axis i (family.model ε) x
  let E := p04CoordinateTransform plan.axis i x
  let Y := p04FamilyMultiExactOutput family
  have hstate := (family.run ε).stage_step i
  have hsub := p04_prefix_sub plan.axis i.val R E
  have hnext := p04_prefix_succ_coord plan.axis i x
  have hident : (fun index ↦
      p04ApplyCoordinatePrefix plan.axis i.val
        ((family.run ε).computedState i.castSucc) index - Y index) =
      (fun index ↦
        p04ApplyCoordinatePrefix plan.axis i.val
          (fun index ↦ R index - E index) index +
        (p04ApplyCoordinatePrefix plan.axis (i.val + 1) x index - Y index)) := by
    funext index
    rw [hstate]
    have hsub' := congrFun hsub index
    have hnext' := congrFun hnext index
    rw [hsub', hnext']
    ring
  unfold p04_familyPrefixErrorRms
  change p04MultiRms (fun index ↦
      p04ApplyCoordinatePrefix plan.axis i.val
        ((family.run ε).computedState i.castSucc) index - Y index) ≤
    p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val
      (fun index ↦ R index - E index)) +
    p04MultiRms (fun index ↦
      p04ApplyCoordinatePrefix plan.axis (i.val + 1) x index - Y index)
  rw [hident]
  exact p04_multiRms_add_le _ _

private theorem p04_familyPrefixInput_le {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {γ : ℝ}
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (ε : P04PositiveEpsilon) (i : Fin m) :
    p04MultiRms (p04ApplyCoordinatePrefix plan.axis (i.val + 1)
      ((family.run ε).computedState i.succ)) ≤
      p04MultiRms (p04FamilyMultiExactOutput family) +
        p04_familyPrefixErrorRms family ε i.succ := by
  let X := p04ApplyCoordinatePrefix plan.axis (i.val + 1)
    ((family.run ε).computedState i.succ)
  let Y := p04FamilyMultiExactOutput family
  have hsplit : X = fun index ↦ (X index - Y index) + Y index := by
    funext index
    ring
  change p04MultiRms X ≤ p04MultiRms Y +
    p04MultiRms (fun index ↦ X index - Y index)
  have h := p04_multiRms_add_le (fun index ↦ X index - Y index) Y
  have heq := congrArg p04MultiRms hsplit
  linarith [h]

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
  let C : Fin m → ℝ := fun i ↦
    Classical.choose (p04_coordinate_rms_error plan.axis i γ family.gamma_nonneg)
  have hC (i : Fin m) : 0 ≤ C i :=
    (Classical.choose_spec
      (p04_coordinate_rms_error plan.axis i γ family.gamma_nonneg)).1
  have hcoord (i : Fin m) :
      ∀ model : P04WilkinsonModel, model.gamma = γ →
        model.epsilon ≤ 1 → ∀ x : P04MultiArray plan.axis,
          p04MultiRms (fun index ↦
            p04RoundedCoordinateTransform plan.axis i model x index -
              p04CoordinateTransform plan.axis i x index) ≤
            Real.sqrt ((plan.axis i).order : ℝ) *
              (model.epsilon * p04AxisK (plan.axis i) γ +
                model.epsilon ^ 2 * C i) * p04MultiRms x :=
    (Classical.choose_spec
      (p04_coordinate_rms_error plan.axis i γ family.gamma_nonneg)).2
  let Y := p04MultiRms (p04FamilyMultiExactOutput family)
  have hY : 0 ≤ Y := le_of_lt hexactOutput
  have hmain (j : Fin (m + 1)) :
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ ε : P04PositiveEpsilon, ε.1 ≤ 1 →
          p04_familyPrefixErrorRms family ε j ≤
            (ε.1 * p04_suffixAxisK plan γ j + D * ε.1 ^ 2) * Y := by
    induction j using Fin.reverseInduction with
    | last =>
        refine ⟨0, le_refl _, ?_⟩
        intro ε hε
        rw [p04_familyPrefixErrorRms_last, p04_suffixAxisK_last]
        simp
    | cast i ih =>
        obtain ⟨B, hB, hprev⟩ := ih
        let S := p04_suffixAxisK plan γ i.succ
        let K := p04AxisK (plan.axis i) γ
        let T := C i
        let D := T + K * S + B + K * B + T * S + T * B
        have hS : 0 ≤ S := p04_suffixAxisK_nonneg plan γ family.gamma_nonneg i.succ
        have hK : 0 ≤ K := p04_axisK_nonneg (plan.axis i) γ family.gamma_nonneg
        have hT : 0 ≤ T := hC i
        have hD : 0 ≤ D := by dsimp [D]; positivity
        refine ⟨D, hD, ?_⟩
        intro ε hε
        let x := (family.run ε).computedState i.succ
        let c := ε.1 * K + ε.1 ^ 2 * T
        let b := ε.1 * S + ε.1 ^ 2 * B
        have hc : 0 ≤ c := by
          dsimp [c]
          exact add_nonneg (mul_nonneg ε.property.le hK)
            (mul_nonneg (sq_nonneg ε.1) hT)
        have hmodel := family.model_gamma ε
        have hmodelε := family.model_epsilon ε
        have hlocal := hcoord i (family.model ε) hmodel
          (by simpa [hmodelε] using hε) x
        have hprop := p04_propagated_coordinate_rms_error
          plan γ i (family.model ε) x T hlocal
        rw [hmodelε] at hprop
        have hstep := p04_familyPrefixErrorRms_step family ε i
        have hinput := p04_familyPrefixInput_le family ε i
        have hprev' := hprev ε hε
        have hloc : p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val
            (fun index ↦
              p04RoundedCoordinateTransform plan.axis i (family.model ε) x index -
                p04CoordinateTransform plan.axis i x index)) ≤
            c * (Y + p04_familyPrefixErrorRms family ε i.succ) := by
          have hscaled := mul_le_mul_of_nonneg_left hinput hc
          change p04MultiRms (p04ApplyCoordinatePrefix plan.axis i.val
            (fun index ↦
              p04RoundedCoordinateTransform plan.axis i (family.model ε) x index -
                p04CoordinateTransform plan.axis i x index)) ≤
            c * p04MultiRms
              (p04ApplyCoordinatePrefix plan.axis (i.val + 1) x) at hprop
          exact hprop.trans hscaled
        have hprevBound : p04_familyPrefixErrorRms family ε i.succ ≤ b * Y :=
          by dsimp [b, S]; nlinarith [hprev']
        have hscaledPrev := mul_le_mul_of_nonneg_left hprevBound hc
        have hrough : p04_familyPrefixErrorRms family ε i.castSucc ≤
            (c * (1 + b) + b) * Y := by
          dsimp [c, b] at hscaledPrev ⊢
          nlinarith [hstep, hloc, hprevBound]
        have hcompose := p04_error_compose_second ε.1 1 S B K T
          ε.property.le hε (by norm_num) hS hB hK hT
        have hcomposeScaled := mul_le_mul_of_nonneg_right hcompose hY
        have hSstep := p04_suffixAxisK_step plan γ i
        change p04_familyPrefixErrorRms family ε i.castSucc ≤
          (ε.1 * p04_suffixAxisK plan γ i.castSucc + D * ε.1 ^ 2) * Y
        rw [hSstep]
        dsimp [c, b, D, K, S, T] at hrough hcomposeScaled ⊢
        nlinarith
  obtain ⟨D, hD, hbound⟩ := hmain (0 : Fin (m + 1))
  refine ⟨D, hD, 1, by norm_num, ?_⟩
  intro ε hε
  have h := hbound ε hε
  rw [p04_suffixAxisK_zero] at h
  have herror : p04_familyPrefixErrorRms family ε (0 : Fin (m + 1)) =
      p04MultiRms (p04FamilyMultiFftRoundoffError family ε) := by
    rfl
  rw [herror] at h
  apply (div_le_iff₀ hexactOutput).2
  simpa [Y, mul_comm, mul_left_comm, mul_assoc] using h

end VSCLReuse

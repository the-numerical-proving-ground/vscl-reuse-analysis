import VSCLReuse.P04.Definitions

namespace VSCLReuse






private theorem p04_stdAddChar_two_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : ℂ) := by
  rw [← Int.cast_one, ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 1
  · congr 1
    push_cast
    ring

private theorem p04_stdAddChar_four_one :
    ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [← Int.cast_one, ZMod.stdAddChar_coe]
  convert Complex.exp_pi_div_two_mul_I using 1
  · congr 1
    push_cast
    ring

private theorem p04_radixTwoCoefficient_eq (t : ZMod 2) (x : ℂ) :
    p04RadixTwoCoefficientApply t x = ZMod.stdAddChar t * x := by
  fin_cases t
  · change x = ZMod.stdAddChar (0 : ZMod 2) * x
    simp
  · change -x = ZMod.stdAddChar (1 : ZMod 2) * x
    rw [p04_stdAddChar_two_one]
    ring

private theorem p04_stdAddChar_four_two :
    ZMod.stdAddChar (2 : ZMod 4) = (-1 : ℂ) := by
  have ht : (2 : ZMod 4) = 1 + 1 := by norm_num
  rw [ht, AddChar.map_add_eq_mul, p04_stdAddChar_four_one]
  simp

private theorem p04_stdAddChar_four_three :
    ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  have ht : (3 : ZMod 4) = 2 + 1 := by norm_num
  rw [ht, AddChar.map_add_eq_mul, p04_stdAddChar_four_two, p04_stdAddChar_four_one]
  ring

private theorem p04_radixFourCoefficient_eq (t : ZMod 4) (x : ℂ) :
    p04RadixFourCoefficientApply t x = ZMod.stdAddChar t * x := by
  fin_cases t
  · change x = ZMod.stdAddChar (0 : ZMod 4) * x
    simp
  · change (⟨-x.im, x.re⟩ : ℂ) = ZMod.stdAddChar (1 : ZMod 4) * x
    rw [p04_stdAddChar_four_one]
    apply Complex.ext <;> simp [Complex.I_mul]
  · change -x = ZMod.stdAddChar (2 : ZMod 4) * x
    rw [p04_stdAddChar_four_two]
    ring
  · change (⟨x.im, -x.re⟩ : ℂ) = ZMod.stdAddChar (3 : ZMod 4) * x
    rw [p04_stdAddChar_four_three]
    apply Complex.ext <;> simp [Complex.I_mul]

private theorem p04_flAdd_abs_error (model : P04WilkinsonModel)
    (a b : ℝ) :
    |model.flAdd a b - (a + b)| ≤
      model.epsilon * (|a| + |b|) := by
  obtain ⟨θa, θb, hθa, hθb, hfl⟩ := model.add_model a b
  rw [hfl]
  have ha : |a * θa| ≤ |a| := by
    rw [abs_mul]
    nlinarith [abs_nonneg a]
  have hb : |b * θb| ≤ |b| := by
    rw [abs_mul]
    nlinarith [abs_nonneg b]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * (1 + θa * model.epsilon) +
        b * (1 + θb * model.epsilon) - (a + b)| =
        |a * θa * model.epsilon + b * θb * model.epsilon| := by ring
    _ ≤ |a * θa * model.epsilon| + |b * θb * model.epsilon| := abs_add_le _ _
    _ = (|a * θa| + |b * θb|) * model.epsilon := by
      simp only [abs_mul, abs_of_nonneg hε]
      ring
    _ ≤ model.epsilon * (|a| + |b|) := by
      have h := add_le_add ha hb
      exact (mul_le_mul_of_nonneg_right h hε).trans_eq (mul_comm _ _)

private theorem p04_flMul_abs_error (model : P04WilkinsonModel)
    (a b : ℝ) :
    |model.flMul a b - a * b| ≤ model.epsilon * |a * b| := by
  obtain ⟨θ, hθ, hfl⟩ := model.mul_model a b
  rw [hfl]
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  calc
    |a * b * (1 + θ * model.epsilon) - a * b| =
        |a * b| * |θ| * model.epsilon := by
      ring_nf
      simp only [abs_mul, abs_of_nonneg hε]
      ring
    _ ≤ model.epsilon * |a * b| := by
      calc
        |a * b| * |θ| * model.epsilon ≤ |a * b| * 1 * model.epsilon := by
          gcongr
        _ = model.epsilon * |a * b| := by ring

private def p04DiagScale (z : ℂ) (a b : ℝ) : ℂ :=
  ⟨z.re * a, z.im * b⟩

private theorem p04_diagScale_norm_le (z : ℂ) {a b : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖p04DiagScale z a b‖ ≤ ‖z‖ := by
  have ha' : a ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := a) (b := (1 : ℝ))).2 (by simpa using ha)
  have hb' : b ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := b) (b := (1 : ℝ))).2 (by simpa using hb)
  have hsq : Complex.normSq (p04DiagScale z a b) ≤ Complex.normSq z := by
    simp only [Complex.normSq_apply, p04DiagScale]
    have hr := mul_le_mul_of_nonneg_left ha' (sq_nonneg z.re)
    have hi := mul_le_mul_of_nonneg_left hb' (sq_nonneg z.im)
    nlinarith [hr, hi]
  simpa only [Complex.norm_def] using Real.sqrt_le_sqrt hsq

private theorem p04_roundedComplexAdd_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexAdd model x y - (x + y)‖ ≤
      model.epsilon * (‖x‖ + ‖y‖) := by
  obtain ⟨θxr, θyr, hxr, hyr, hfr⟩ := model.add_model x.re y.re
  obtain ⟨θxi, θyi, hxi, hyi, hfi⟩ := model.add_model x.im y.im
  have hid :
      p04RoundedComplexAdd model x y - (x + y) =
        (model.epsilon : ℂ) *
          (p04DiagScale x θxr θxi + p04DiagScale y θyr θyi) := by
    apply Complex.ext
    · simp [p04RoundedComplexAdd, hfr, p04DiagScale]
      ring
    · simp [p04RoundedComplexAdd, hfi, p04DiagScale]
      ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  exact mul_le_mul_of_nonneg_left
    ((norm_add_le _ _).trans
      (add_le_add (p04_diagScale_norm_le x hxr hxi)
        (p04_diagScale_norm_le y hyr hyi)))
    (le_of_lt model.epsilon_pos)

private def p04PairMul (model : P04WilkinsonModel) (a : ℝ) (y : ℂ) : ℂ :=
  ⟨model.flMul a y.re, model.flMul a y.im⟩

private theorem p04_pairMul_error (model : P04WilkinsonModel)
    (a : ℝ) (y : ℂ) :
    ‖p04PairMul model a y - (a : ℂ) * y‖ ≤
      model.epsilon * |a| * ‖y‖ := by
  obtain ⟨θr, hθr, hfr⟩ := model.mul_model a y.re
  obtain ⟨θi, hθi, hfi⟩ := model.mul_model a y.im
  have hid : p04PairMul model a y - (a : ℂ) * y =
      (model.epsilon : ℂ) * p04DiagScale ((a : ℂ) * y) θr θi := by
    apply Complex.ext
    · simp [p04PairMul, p04DiagScale, hfr, Complex.mul_re]
      ring
    · simp [p04PairMul, p04DiagScale, hfi, Complex.mul_im]
      ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos model.epsilon_pos]
  calc
    model.epsilon * ‖p04DiagScale ((a : ℂ) * y) θr θi‖ ≤
        model.epsilon * ‖(a : ℂ) * y‖ :=
      mul_le_mul_of_nonneg_left
        (p04_diagScale_norm_le _ hθr hθi) (le_of_lt model.epsilon_pos)
    _ = model.epsilon * |a| * ‖y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      ring

private theorem p04_pairMul_norm (model : P04WilkinsonModel)
    (a : ℝ) (y : ℂ) :
    ‖p04PairMul model a y‖ ≤
      (1 + model.epsilon) * |a| * ‖y‖ := by
  have h := p04_pairMul_error model a y
  have htri := norm_add_le
    (p04PairMul model a y - (a : ℂ) * y) ((a : ℂ) * y)
  have heq : p04PairMul model a y - (a : ℂ) * y + (a : ℂ) * y =
      p04PairMul model a y := by ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs] at htri
  nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg y)]

private theorem p04_abs_re_add_abs_im_le (z : ℂ) :
    |z.re| + |z.im| ≤ Real.sqrt 2 * ‖z‖ := by
  have hn : 0 ≤ ‖z‖ := norm_nonneg z
  have hs : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have h2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [pow_two, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
    ring
  have hsq : (|z.re| + |z.im|) ^ 2 ≤
      (Real.sqrt 2 * ‖z‖) ^ 2 := by
    nlinarith [sq_nonneg (|z.re| - |z.im|), sq_abs z.re, sq_abs z.im]
  exact (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg hs hn)).mp hsq

private theorem p04_roundedComplexMul_error (model : P04WilkinsonModel)
    (x y : ℂ) :
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
      (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
  let u := p04PairMul model x.re y
  let v := Complex.I * p04PairMul model x.im y
  let u₀ := (x.re : ℂ) * y
  let v₀ := Complex.I * (x.im : ℂ) * y
  have hrounded : p04RoundedComplexMul model x y =
      p04RoundedComplexAdd model u v := by
    apply Complex.ext <;>
      simp [p04RoundedComplexMul, p04RoundedComplexAdd, u, v,
        p04PairMul, Complex.I_mul]
  have hexact : x * y = u₀ + v₀ := by
    apply Complex.ext <;>
      simp [u₀, v₀, Complex.mul_re, Complex.mul_im, Complex.I_mul] <;> ring
  have hvnorm : ‖v‖ = ‖p04PairMul model x.im y‖ := by
    simp [v]
  have hve : ‖v - v₀‖ ≤ model.epsilon * |x.im| * ‖y‖ := by
    have heq : v - v₀ = Complex.I *
        (p04PairMul model x.im y - (x.im : ℂ) * y) := by
      dsimp [v, v₀]
      ring
    rw [heq, norm_mul, Complex.norm_I, one_mul]
    exact p04_pairMul_error model x.im y
  have hunorm := p04_pairMul_norm model x.re y
  have hvnorm' := p04_pairMul_norm model x.im y
  have hue := p04_pairMul_error model x.re y
  have hadd := p04_roundedComplexAdd_error model u v
  have htri₁ := norm_add_le
    (p04RoundedComplexAdd model u v - (u + v))
    ((u + v) - (u₀ + v₀))
  have htri₂ := norm_add_le (u - u₀) (v - v₀)
  have hdiff : (u + v) - (u₀ + v₀) = (u - u₀) + (v - v₀) := by ring
  have hmain : ‖p04RoundedComplexMul model x y - x * y‖ ≤
      model.epsilon * (2 + model.epsilon) *
        (|x.re| + |x.im|) * ‖y‖ := by
    rw [hrounded, hexact]
    have heq : p04RoundedComplexAdd model u v - (u₀ + v₀) =
        (p04RoundedComplexAdd model u v - (u + v)) +
          ((u + v) - (u₀ + v₀)) := by ring
    rw [heq]
    calc
      ‖(p04RoundedComplexAdd model u v - (u + v)) +
          ((u + v) - (u₀ + v₀))‖ ≤
          ‖p04RoundedComplexAdd model u v - (u + v)‖ +
          ‖(u + v) - (u₀ + v₀)‖ := htri₁
      _ ≤ model.epsilon * (‖u‖ + ‖v‖) +
          (‖u - u₀‖ + ‖v - v₀‖) := by
        rw [hdiff]
        exact add_le_add hadd htri₂
      _ ≤ model.epsilon *
          ((1 + model.epsilon) * |x.re| * ‖y‖ +
            (1 + model.epsilon) * |x.im| * ‖y‖) +
          (model.epsilon * |x.re| * ‖y‖ +
            model.epsilon * |x.im| * ‖y‖) := by
        rw [hvnorm]
        gcongr
        exact le_of_lt model.epsilon_pos
      _ = model.epsilon * (2 + model.epsilon) *
          (|x.re| + |x.im|) * ‖y‖ := by ring
  have hsqrt : Real.sqrt (2 : ℝ) ≤ 3 / 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hε : 0 ≤ model.epsilon := le_of_lt model.epsilon_pos
  have hcoeff : model.epsilon * (2 + model.epsilon) * Real.sqrt 2 ≤
      3 * model.epsilon + 2 * model.epsilon ^ 2 := by
    have ht : model.epsilon * (2 + model.epsilon) * Real.sqrt 2 ≤
        model.epsilon * (2 + model.epsilon) * (3 / 2) := by
      gcongr
    nlinarith
  calc
    ‖p04RoundedComplexMul model x y - x * y‖ ≤
        model.epsilon * (2 + model.epsilon) *
          (|x.re| + |x.im|) * ‖y‖ := hmain
    _ ≤ model.epsilon * (2 + model.epsilon) *
          (Real.sqrt 2 * ‖x‖) * ‖y‖ := by
      gcongr
      exact p04_abs_re_add_abs_im_le x
    _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
      calc
        model.epsilon * (2 + model.epsilon) *
            (Real.sqrt 2 * ‖x‖) * ‖y‖ =
            (model.epsilon * (2 + model.epsilon) * Real.sqrt 2) *
              ‖x‖ * ‖y‖ := by ring
        _ ≤ (3 * model.epsilon + 2 * model.epsilon ^ 2) * ‖x‖ * ‖y‖ := by
          gcongr

private theorem p04_stdAddChar_eq_trig {q : ℕ} [NeZero q]
    (j : ZMod q) :
    ZMod.stdAddChar j =
      (⟨Real.cos (p04RootAngle j), Real.sin (p04RootAngle j)⟩ : ℂ) := by
  rw [p04StdAddChar_positive_exp]
  have harg :
      (2 * Real.pi * Complex.I * (j.val : ℂ) / (q : ℂ)) =
        (p04RootAngle j : ℂ) * Complex.I := by
    simp only [p04RootAngle]
    push_cast
    ring
  rw [harg, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, zero_add,
    add_zero, sub_zero]

private theorem p04_stdAddChar_norm {q : ℕ} [NeZero q]
    (j : ZMod q) : ‖ZMod.stdAddChar j‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem p04_roundedRoot_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤
      Real.sqrt 2 * model.gamma * model.epsilon := by
  obtain ⟨θc, hθc, hcos⟩ := model.cos_model (p04RootAngle j)
  obtain ⟨θs, hθs, hsin⟩ := model.sin_model (p04RootAngle j)
  have hsc : θc ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := θc) (b := (1 : ℝ))).2 (by simpa using hθc)
  have hss : θs ^ 2 ≤ 1 := by
    simpa using (sq_le_sq (a := θs) (b := (1 : ℝ))).2 (by simpa using hθs)
  have hnorm : ‖(⟨θc, θs⟩ : ℂ)‖ ≤ Real.sqrt 2 := by
    rw [Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply]
    nlinarith
  have hid : p04RoundedRoot model j - ZMod.stdAddChar j =
      ((model.gamma * model.epsilon : ℝ) : ℂ) * ⟨θc, θs⟩ := by
    rw [p04_stdAddChar_eq_trig]
    apply Complex.ext
    · simp [p04RoundedRoot, hcos]
      ring
    · simp [p04RoundedRoot, hsin]
      ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hge : 0 ≤ model.gamma * model.epsilon :=
    mul_nonneg model.gamma_nonneg (le_of_lt model.epsilon_pos)
  rw [abs_of_nonneg hge]
  have h := mul_le_mul_of_nonneg_left hnorm hge
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

private theorem p04_roundedRoot_norm {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) :
    ‖p04RoundedRoot model j‖ ≤
      1 + Real.sqrt 2 * model.gamma * model.epsilon := by
  have htri := norm_add_le
    (p04RoundedRoot model j - ZMod.stdAddChar j) (ZMod.stdAddChar j)
  have heq : p04RoundedRoot model j - ZMod.stdAddChar j +
      ZMod.stdAddChar j = p04RoundedRoot model j := by ring
  rw [heq, p04_stdAddChar_norm] at htri
  linarith [p04_roundedRoot_error model j]

private theorem p04_recursiveSum_bounds (model : P04WilkinsonModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum model.flAdd n v - ∑ i, v i| ≤
          ((1 + model.epsilon) ^ n - 1) * (∑ i, |v i|) ∧
      |recursiveSum model.flAdd n v| ≤
          (1 + model.epsilon) ^ n * (∑ i, |v i|) := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum]
        constructor
        · exact mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg _)
        · nlinarith [mul_nonneg (le_of_lt model.epsilon_pos) (abs_nonneg (v 0))]
      · let w : Fin n → ℝ := fun i => v i.castSucc
        let t := v (Fin.last n)
        have hsum : (∑ i : Fin (n + 1), v i) =
            (∑ i : Fin n, w i) + t := by
          simpa [w, t] using (Fin.sum_univ_castSucc (f := v))
        have habs : (∑ i : Fin (n + 1), |v i|) =
            (∑ i : Fin n, |w i|) + |t| := by
          simpa [w, t] using
            (Fin.sum_univ_castSucc (f := fun i : Fin (n + 1) => |v i|))
        have hrec : recursiveSum model.flAdd (n + 1) v =
            model.flAdd (recursiveSum model.flAdd n w) t := by
          simp [recursiveSum, hn, w, t]
        obtain ⟨herr, hnorm⟩ := ih w
        let r := recursiveSum model.flAdd n w
        let s := ∑ i : Fin n, w i
        let S := ∑ i : Fin n, |w i|
        let E := model.epsilon
        let P := (1 + E) ^ n
        have hE : 0 ≤ E := le_of_lt model.epsilon_pos
        have hP : 1 ≤ P := by
          dsimp [P]
          exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + E)
        have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have hfl := p04_flAdd_abs_error model r t
        change |r - s| ≤ (P - 1) * S at herr
        change |r| ≤ P * S at hnorm
        change |model.flAdd r t - (r + t)| ≤ E * (|r| + |t|) at hfl
        have hflnorm : |model.flAdd r t| ≤ (1 + E) * (|r| + |t|) := by
          have htri := abs_add_le (model.flAdd r t - (r + t)) (r + t)
          have heq : model.flAdd r t - (r + t) + (r + t) =
              model.flAdd r t := by ring
          rw [heq] at htri
          have htri' := abs_add_le r t
          dsimp [E] at hE ⊢
          nlinarith
        have herr' : |model.flAdd r t - (s + t)| ≤
            |model.flAdd r t - (r + t)| + |r - s| := by
          have heq : model.flAdd r t - (s + t) =
              (model.flAdd r t - (r + t)) + (r - s) := by ring
          rw [heq]
          exact abs_add_le _ _
        constructor
        · rw [hrec, hsum, habs]
          have hpow : (1 + E) ^ (n + 1) = (1 + E) * P := by
            simp [P, pow_succ, mul_comm]
          rw [hpow]
          have hstep :
              |model.flAdd r t - (r + t)| + |r - s| ≤
                E * (P * S + |t|) + (P - 1) * S := by
              have hfirst : E * (|r| + |t|) ≤ E * (P * S + |t|) := by
                gcongr
              exact (add_le_add hfl herr).trans (add_le_add hfirst le_rfl)
          have hlast :
              E * (P * S + |t|) + (P - 1) * S ≤
                ((1 + E) * P - 1) * (S + |t|) := by
              nlinarith [mul_nonneg (by linarith : 0 ≤ P - 1) (abs_nonneg t)]
          exact herr'.trans (hstep.trans hlast)
        · rw [hrec, habs]
          have hpow : (1 + E) ^ (n + 1) = (1 + E) * P := by
            simp [P, pow_succ, mul_comm]
          rw [hpow]
          have hstep : (1 + E) * (|r| + |t|) ≤
              (1 + E) * (P * S + |t|) := by gcongr
          have hlast : (1 + E) * (P * S + |t|) ≤
              (1 + E) * P * (S + |t|) := by
            nlinarith [mul_nonneg (by linarith : 0 ≤ P - 1) (abs_nonneg t)]
          exact hflnorm.trans (hstep.trans hlast)

private theorem p04_complex_norm_le_of_components
    (z : ℂ) (R I c : ℝ) (hR : 0 ≤ R) (hI : 0 ≤ I) (hc : 0 ≤ c)
    (hre : |z.re| ≤ c * R) (him : |z.im| ≤ c * I) :
    ‖z‖ ≤ c * ‖(⟨R, I⟩ : ℂ)‖ := by
  have hcr : 0 ≤ c * R := mul_nonneg hc hR
  have hci : 0 ≤ c * I := mul_nonneg hc hI
  have hsre : z.re ^ 2 ≤ (c * R) ^ 2 := by
    exact (sq_le_sq).2 (by simpa [abs_of_nonneg hcr] using hre)
  have hsim : z.im ^ 2 ≤ (c * I) ^ 2 := by
    exact (sq_le_sq).2 (by simpa [abs_of_nonneg hci] using him)
  have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [pow_two, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
    ring
  have hri : ‖(⟨R, I⟩ : ℂ)‖ ^ 2 = R ^ 2 + I ^ 2 := by
    rw [pow_two, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
    ring
  have hsq : ‖z‖ ^ 2 ≤ (c * ‖(⟨R, I⟩ : ℂ)‖) ^ 2 := by
    calc
      ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := hzn
      _ ≤ (c * R) ^ 2 + (c * I) ^ 2 := add_le_add hsre hsim
      _ = (c * ‖(⟨R, I⟩ : ℂ)‖) ^ 2 := by
        simp only [mul_pow]
        rw [hri]
        ring
  exact (sq_le_sq₀ (norm_nonneg z)
    (mul_nonneg hc (norm_nonneg _))).mp hsq

private noncomputable def p04ComplexRecursiveSum (model : P04WilkinsonModel)
    {n : ℕ} (v : Fin n → ℂ) : ℂ :=
  ⟨recursiveSum model.flAdd n (fun i => (v i).re),
    recursiveSum model.flAdd n (fun i => (v i).im)⟩

private theorem p04_complexAbsComponents_norm (z : ℂ) :
    ‖(⟨|z.re|, |z.im|⟩ : ℂ)‖ = ‖z‖ := by
  simp only [Complex.norm_def, Complex.normSq_apply]
  congr 1
  nlinarith [sq_abs z.re, sq_abs z.im]

private theorem p04_complexRecursiveSum_error (model : P04WilkinsonModel)
    {n : ℕ} (v : Fin n → ℂ) :
    ‖p04ComplexRecursiveSum model v - ∑ i, v i‖ ≤
      ((1 + model.epsilon) ^ n - 1) * (∑ i, ‖v i‖) := by
  let c := (1 + model.epsilon) ^ n - 1
  let R := ∑ i : Fin n, |(v i).re|
  let I := ∑ i : Fin n, |(v i).im|
  let z := p04ComplexRecursiveSum model v - ∑ i, v i
  have hc : 0 ≤ c := by
    dsimp [c]
    exact sub_nonneg.mpr
      (one_le_pow₀ (by linarith [model.epsilon_pos] : (1 : ℝ) ≤ 1 + model.epsilon))
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hI : 0 ≤ I := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hre : |z.re| ≤ c * R := by
    simpa [z, c, R, p04ComplexRecursiveSum] using
      (p04_recursiveSum_bounds model n (fun i => (v i).re)).1
  have him : |z.im| ≤ c * I := by
    simpa [z, c, I, p04ComplexRecursiveSum] using
      (p04_recursiveSum_bounds model n (fun i => (v i).im)).1
  have hmajor : ‖(⟨R, I⟩ : ℂ)‖ ≤ ∑ i, ‖v i‖ := by
    have heq : (⟨R, I⟩ : ℂ) =
        ∑ i : Fin n, (⟨|(v i).re|, |(v i).im|⟩ : ℂ) := by
      apply Complex.ext <;> simp [R, I]
    rw [heq]
    calc
      ‖∑ i : Fin n, (⟨|(v i).re|, |(v i).im|⟩ : ℂ)‖ ≤
          ∑ i : Fin n, ‖(⟨|(v i).re|, |(v i).im|⟩ : ℂ)‖ :=
        norm_sum_le _ _
      _ = ∑ i : Fin n, ‖v i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        exact p04_complexAbsComponents_norm (v i)
  have hcomp := p04_complex_norm_le_of_components z R I c hR hI hc hre him
  exact hcomp.trans (mul_le_mul_of_nonneg_left hmajor hc)

private theorem p04_roundedComplexSum_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (term : ZMod q → ℂ) :
    ‖p04RoundedComplexSum model term - ∑ j : ZMod q, term j‖ ≤
      ((1 + model.epsilon) ^ q - 1) * (∑ j : ZMod q, ‖term j‖) := by
  let index : Fin q ≃ ZMod q := (ZMod.finEquiv q).toEquiv
  have hdef : p04RoundedComplexSum model term =
      p04ComplexRecursiveSum model (fun i => term (index i)) := by
    rfl
  rw [hdef, ← Equiv.sum_comp index term,
    ← Equiv.sum_comp index (fun j : ZMod q => ‖term j‖)]
  exact p04_complexRecursiveSum_error model (fun i => term (index i))

private theorem p04_roundedTerm_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (j : ZMod q) (x : ℂ)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
      ((3 + Real.sqrt 2 * model.gamma) * model.epsilon +
        (2 + 5 * Real.sqrt 2 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
  let E := model.epsilon
  let G := Real.sqrt 2 * model.gamma
  have hE : 0 ≤ E := le_of_lt model.epsilon_pos
  have hG : 0 ≤ G := mul_nonneg (Real.sqrt_nonneg _) model.gamma_nonneg
  have hroot := p04_roundedRoot_error model j
  have hrootnorm := p04_roundedRoot_norm model j
  have hmul := p04_roundedComplexMul_error model (p04RoundedRoot model j) x
  have htri := norm_add_le
    (p04RoundedComplexMul model (p04RoundedRoot model j) x -
      p04RoundedRoot model j * x)
    ((p04RoundedRoot model j - ZMod.stdAddChar j) * x)
  have heq : p04RoundedComplexMul model (p04RoundedRoot model j) x -
      p04RoundedRoot model j * x +
      (p04RoundedRoot model j - ZMod.stdAddChar j) * x =
      p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x := by ring
  rw [heq, norm_mul] at htri
  have he3 : E ^ 3 ≤ E ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hε)]
  have hcoeff : (3 * E + 2 * E ^ 2) * (1 + G * E) + G * E ≤
      (3 + G) * E + (2 + 5 * G) * E ^ 2 := by
    have hge := mul_le_mul_of_nonneg_left he3 hG
    nlinarith
  change ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ ≤ G * E at hroot
  change ‖p04RoundedRoot model j‖ ≤ 1 + G * E at hrootnorm
  change ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
      p04RoundedRoot model j * x‖ ≤
        (3 * E + 2 * E ^ 2) * ‖p04RoundedRoot model j‖ * ‖x‖ at hmul
  calc
    ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
        ZMod.stdAddChar j * x‖ ≤
        ‖p04RoundedComplexMul model (p04RoundedRoot model j) x -
          p04RoundedRoot model j * x‖ +
          ‖p04RoundedRoot model j - ZMod.stdAddChar j‖ * ‖x‖ := htri
    _ ≤ ((3 * E + 2 * E ^ 2) * (1 + G * E) + G * E) * ‖x‖ := by
      have hfirst := mul_le_mul_of_nonneg_right hrootnorm
        (mul_nonneg (by positivity : 0 ≤ 3 * E + 2 * E ^ 2) (norm_nonneg x))
      have hsecond := mul_le_mul_of_nonneg_right hroot (norm_nonneg x)
      nlinarith [hmul]
    _ ≤ ((3 + G) * E + (2 + 5 * G) * E ^ 2) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg x)
    _ = ((3 + Real.sqrt 2 * model.gamma) * model.epsilon +
          (2 + 5 * Real.sqrt 2 * model.gamma) * model.epsilon ^ 2) * ‖x‖ := by
      dsimp [E, G]
      ring

private theorem p04_roundedGenericBlock_error {q : ℕ} [NeZero q]
    (model : P04WilkinsonModel) (x : ZMod q → ℂ) (k : ZMod q)
    (hε : model.epsilon ≤ 1) :
    ‖p04RoundedGenericRadixBlock model x k -
        ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
      (((1 + model.epsilon) ^ q - 1) *
          (1 + (3 + Real.sqrt 2 * model.gamma) * model.epsilon +
            (2 + 5 * Real.sqrt 2 * model.gamma) * model.epsilon ^ 2) +
        (3 + Real.sqrt 2 * model.gamma) * model.epsilon +
        (2 + 5 * Real.sqrt 2 * model.gamma) * model.epsilon ^ 2) *
          (∑ j : ZMod q, ‖x j‖) := by
  let E := model.epsilon
  let C := 3 + Real.sqrt 2 * model.gamma
  let D := 2 + 5 * Real.sqrt 2 * model.gamma
  let A := C * E + D * E ^ 2
  let B := (1 + E) ^ q - 1
  let S := ∑ j : ZMod q, ‖x j‖
  let t : ZMod q → ℂ := fun j =>
    p04RoundedComplexMul model (p04RoundedRoot model (j * k)) (x j)
  let t₀ : ZMod q → ℂ := fun j => ZMod.stdAddChar (j * k) * x j
  have hE : 0 ≤ E := le_of_lt model.epsilon_pos
  have hG : 0 ≤ Real.sqrt 2 * model.gamma :=
    mul_nonneg (Real.sqrt_nonneg _) model.gamma_nonneg
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  have hD : 0 ≤ D := by
    dsimp [D]
    nlinarith
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact sub_nonneg.mpr
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + E))
  have ht (j : ZMod q) : ‖t j - t₀ j‖ ≤ A * ‖x j‖ := by
    simpa [t, t₀, A, C, D, E] using
      p04_roundedTerm_error model (j * k) (x j) hε
  have htnorm (j : ZMod q) : ‖t j‖ ≤ (1 + A) * ‖x j‖ := by
    have htri := norm_add_le (t j - t₀ j) (t₀ j)
    have heq : t j - t₀ j + t₀ j = t j := by ring
    rw [heq] at htri
    have hn₀ : ‖t₀ j‖ = ‖x j‖ := by
      simp [t₀, norm_mul, p04_stdAddChar_norm]
    rw [hn₀] at htri
    nlinarith [ht j]
  have htsum : ∑ j : ZMod q, ‖t j‖ ≤ (1 + A) * S := by
    calc
      ∑ j : ZMod q, ‖t j‖ ≤ ∑ j : ZMod q, (1 + A) * ‖x j‖ :=
        Finset.sum_le_sum fun j _ => htnorm j
      _ = (1 + A) * S := by simp [S, Finset.mul_sum]
  have hdiffsum : ‖(∑ j : ZMod q, t j) - ∑ j : ZMod q, t₀ j‖ ≤ A * S := by
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ j : ZMod q, (t j - t₀ j)‖ ≤
          ∑ j : ZMod q, ‖t j - t₀ j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod q, A * ‖x j‖ := Finset.sum_le_sum fun j _ => ht j
      _ = A * S := by simp [S, Finset.mul_sum]
  have hround : ‖p04RoundedComplexSum model t - ∑ j : ZMod q, t j‖ ≤
      B * (∑ j : ZMod q, ‖t j‖) := by
    simpa [B, E] using p04_roundedComplexSum_error model t
  have htri := norm_add_le
    (p04RoundedComplexSum model t - ∑ j : ZMod q, t j)
    ((∑ j : ZMod q, t j) - ∑ j : ZMod q, t₀ j)
  have heq : p04RoundedComplexSum model t - (∑ j : ZMod q, t j) +
      ((∑ j : ZMod q, t j) - ∑ j : ZMod q, t₀ j) =
      p04RoundedComplexSum model t - ∑ j : ZMod q, t₀ j := by ring
  rw [heq] at htri
  have hgoal : ‖p04RoundedComplexSum model t - ∑ j : ZMod q, t₀ j‖ ≤
      (B * (1 + A) + A) * S := by
    calc
      ‖p04RoundedComplexSum model t - ∑ j : ZMod q, t₀ j‖ ≤
          ‖p04RoundedComplexSum model t - ∑ j : ZMod q, t j‖ +
            ‖(∑ j : ZMod q, t j) - ∑ j : ZMod q, t₀ j‖ := htri
      _ ≤ B * (∑ j : ZMod q, ‖t j‖) + A * S :=
        add_le_add hround hdiffsum
      _ ≤ B * ((1 + A) * S) + A * S := by
        gcongr
      _ = (B * (1 + A) + A) * S := by ring
  convert hgoal using 1
  dsimp [B, A, C, D, E, S]
  ring

private theorem p04_roundedComplexSum_two (model : P04WilkinsonModel)
    (term : ZMod 2 → ℂ) :
    p04RoundedComplexSum model term =
      p04RoundedComplexAdd model (term 0) (term 1) := by
  apply Complex.ext <;>
    simp [p04RoundedComplexSum, p04RoundedComplexAdd, recursiveSum]

private theorem p04_sum_zmod_two {α : Type*} [AddCommMonoid α]
    (f : ZMod 2 → α) :
    (∑ j : ZMod 2, f j) = f 0 + f 1 := by
  let e : Fin 2 ≃ ZMod 2 := (ZMod.finEquiv 2).toEquiv
  rw [← Equiv.sum_comp e f, Fin.sum_univ_two]
  rfl

private theorem p04_roundedRadixTwoBlock_error
    (model : P04WilkinsonModel) (x : ZMod 2 → ℂ) (k : ZMod 2) :
    ‖p04RoundedRadixTwoBlock model x k -
        ∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j‖ ≤
      model.epsilon * (‖x 0‖ + ‖x 1‖) := by
  have hround : p04RoundedRadixTwoBlock model x k =
      p04RoundedComplexAdd model (x 0)
        (p04RadixTwoCoefficientApply k (x 1)) := by
    rw [p04RoundedRadixTwoBlock, p04_roundedComplexSum_two]
    simp [p04RadixTwoCoefficientApply]
  have hexact : (∑ j : ZMod 2, ZMod.stdAddChar (j * k) * x j) =
      x 0 + p04RadixTwoCoefficientApply k (x 1) := by
    rw [p04_sum_zmod_two]
    simp [← p04_radixTwoCoefficient_eq]
  have hnorm : ‖p04RadixTwoCoefficientApply k (x 1)‖ = ‖x 1‖ := by
    simp only [p04RadixTwoCoefficientApply]
    split_ifs <;> simp
  rw [hround, hexact, ← hnorm]
  exact p04_roundedComplexAdd_error model (x 0)
    (p04RadixTwoCoefficientApply k (x 1))

private theorem p04_sum_zmod_four {α : Type*} [AddCommMonoid α]
    (f : ZMod 4 → α) :
    (∑ j : ZMod 4, f j) = f 0 + f 1 + f 2 + f 3 := by
  let e : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  rw [← Equiv.sum_comp e f, Fin.sum_univ_four]
  rfl

private theorem p04_balancedFourAdd_error (model : P04WilkinsonModel)
    (a b c d : ℂ) :
    ‖p04RoundedComplexAdd model
        (p04RoundedComplexAdd model a b)
        (p04RoundedComplexAdd model c d) - ((a + b) + (c + d))‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        (‖a‖ + ‖b‖ + ‖c‖ + ‖d‖) := by
  let u := p04RoundedComplexAdd model a b
  let v := p04RoundedComplexAdd model c d
  let E := model.epsilon
  let A := ‖a‖ + ‖b‖
  let B := ‖c‖ + ‖d‖
  have hE : 0 ≤ E := le_of_lt model.epsilon_pos
  have hA : 0 ≤ A := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hu := p04_roundedComplexAdd_error model a b
  have hv := p04_roundedComplexAdd_error model c d
  have htop := p04_roundedComplexAdd_error model u v
  change ‖u - (a + b)‖ ≤ E * A at hu
  change ‖v - (c + d)‖ ≤ E * B at hv
  change ‖p04RoundedComplexAdd model u v - (u + v)‖ ≤
    E * (‖u‖ + ‖v‖) at htop
  have hunorm : ‖u‖ ≤ (1 + E) * A := by
    have htri := norm_add_le (u - (a + b)) (a + b)
    have heq : u - (a + b) + (a + b) = u := by ring
    rw [heq] at htri
    nlinarith [norm_add_le a b]
  have hvnorm : ‖v‖ ≤ (1 + E) * B := by
    have htri := norm_add_le (v - (c + d)) (c + d)
    have heq : v - (c + d) + (c + d) = v := by ring
    rw [heq] at htri
    nlinarith [norm_add_le c d]
  have htri := norm_add_le
    (p04RoundedComplexAdd model u v - (u + v))
    ((u - (a + b)) + (v - (c + d)))
  have heq : p04RoundedComplexAdd model u v - (u + v) +
      ((u - (a + b)) + (v - (c + d))) =
      p04RoundedComplexAdd model u v - ((a + b) + (c + d)) := by ring
  rw [heq] at htri
  have htri₂ := norm_add_le (u - (a + b)) (v - (c + d))
  have hgoal : ‖p04RoundedComplexAdd model u v - ((a + b) + (c + d))‖ ≤
      (2 * E + E ^ 2) * (A + B) := by
    calc
      ‖p04RoundedComplexAdd model u v - ((a + b) + (c + d))‖ ≤
          ‖p04RoundedComplexAdd model u v - (u + v)‖ +
            ‖(u - (a + b)) + (v - (c + d))‖ := htri
      _ ≤ E * (‖u‖ + ‖v‖) + (‖u - (a + b)‖ + ‖v - (c + d)‖) :=
        add_le_add htop htri₂
      _ ≤ E * ((1 + E) * A + (1 + E) * B) + (E * A + E * B) := by
        gcongr
      _ = (2 * E + E ^ 2) * (A + B) := by ring
  convert hgoal using 1
  dsimp [E, A, B]
  ring

private theorem p04_roundedRadixFourBlock_error
    (model : P04WilkinsonModel) (x : ZMod 4 → ℂ) (k : ZMod 4) :
    ‖p04RoundedRadixFourBlock model x k -
        ∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j‖ ≤
      (2 * model.epsilon + model.epsilon ^ 2) *
        (∑ j : ZMod 4, ‖x j‖) := by
  let e : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
  let t : Fin 4 → ℂ := fun i =>
    p04RadixFourCoefficientApply (e i * k) (x (e i))
  have ht (i : Fin 4) :
      t i = ZMod.stdAddChar (e i * k) * x (e i) := by
    exact p04_radixFourCoefficient_eq (e i * k) (x (e i))
  have hround : p04RoundedRadixFourBlock model x k =
      p04RoundedComplexAdd model
        (p04RoundedComplexAdd model (t 0) (t 1))
        (p04RoundedComplexAdd model (t 2) (t 3)) := by
    rfl
  have hexact : (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
      (t 0 + t 1) + (t 2 + t 3) := by
    calc
      (∑ j : ZMod 4, ZMod.stdAddChar (j * k) * x j) =
          ∑ i : Fin 4, ZMod.stdAddChar (e i * k) * x (e i) := by
        exact (Equiv.sum_comp e (fun j => ZMod.stdAddChar (j * k) * x j)).symm
      _ = ∑ i : Fin 4, t i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (ht i).symm
      _ = (t 0 + t 1) + (t 2 + t 3) := by
        rw [Fin.sum_univ_four]
        ring
  have hnorms : ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖ =
      ∑ j : ZMod 4, ‖x j‖ := by
    calc
      ‖t 0‖ + ‖t 1‖ + ‖t 2‖ + ‖t 3‖ =
          ∑ i : Fin 4, ‖t i‖ := by rw [Fin.sum_univ_four]
      _ = ∑ i : Fin 4, ‖x (e i)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [ht i, norm_mul, p04_stdAddChar_norm, one_mul]
      _ = ∑ j : ZMod 4, ‖x j‖ := Equiv.sum_comp e (fun j => ‖x j‖)
  rw [hround, hexact, ← hnorms]
  exact p04_balancedFourAdd_error model (t 0) (t 1) (t 2) (t 3)

private theorem p04_pow_one_add_second_order (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ E : ℝ, 0 ≤ E → E ≤ 1 →
        (1 + E) ^ n - 1 ≤ (n : ℝ) * E + D * E ^ 2 := by
  induction n with
  | zero =>
      refine ⟨0, le_refl 0, ?_⟩
      intro E _ _
      simp
  | succ n ih =>
      obtain ⟨D, hD, hbound⟩ := ih
      refine ⟨2 * D + n, by positivity, ?_⟩
      intro E hE hE1
      have hmain := hbound E hE hE1
      have hE3 : E ^ 3 ≤ E ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg E) (sub_nonneg.mpr hE1)]
      have hD3 := mul_le_mul_of_nonneg_left hE3 hD
      have hP : 0 ≤ 1 + E := by linarith
      have hmul := mul_le_mul_of_nonneg_right hmain hP
      have hpowsucc : (1 + E) ^ (n + 1) - 1 =
          ((1 + E) ^ n - 1) * (1 + E) + E := by
        rw [pow_succ]
        ring
      rw [hpowsucc]
      push_cast
      nlinarith

private theorem p04_genericBlock_coefficient_second_order
    (q : ℕ) (hq : 3 ≤ q) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ E : ℝ, 0 ≤ E → E ≤ 1 →
      ((1 + E) ^ q - 1) *
          (1 + (3 + Real.sqrt 2 * γ) * E +
            (2 + 5 * Real.sqrt 2 * γ) * E ^ 2) +
        (3 + Real.sqrt 2 * γ) * E +
        (2 + 5 * Real.sqrt 2 * γ) * E ^ 2 ≤
          2 * (q + γ) * E + D * E ^ 2 := by
  obtain ⟨M, hM, hpow⟩ := p04_pow_one_add_second_order q
  let C := 3 + Real.sqrt 2 * γ
  let F := 2 + 5 * Real.sqrt 2 * γ
  let D := M + F + ((q : ℝ) + M) * (C + F)
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hγ]
  have hF : 0 ≤ F := by
    dsimp [F]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hγ]
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro E hE hE1
  let A := C * E + F * E ^ 2
  let B := (1 + E) ^ q - 1
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact sub_nonneg.mpr
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + E))
  have hE2 : E ^ 2 ≤ E := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hE1)]
  have hAsmall : A ≤ (C + F) * E := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hE2 hF]
  have hBsmall : B ≤ ((q : ℝ) + M) * E := by
    have h := hpow E hE hE1
    dsimp [B]
    nlinarith [mul_le_mul_of_nonneg_left hE2 hM]
  have hBA : B * A ≤ ((q : ℝ) + M) * (C + F) * E ^ 2 := by
    have hqM : 0 ≤ (q : ℝ) + M := by positivity
    calc
      B * A ≤ (((q : ℝ) + M) * E) * A :=
        mul_le_mul_of_nonneg_right hBsmall hA
      _ ≤ (((q : ℝ) + M) * E) * ((C + F) * E) := by
        exact mul_le_mul_of_nonneg_left hAsmall (mul_nonneg hqM hE)
      _ = ((q : ℝ) + M) * (C + F) * E ^ 2 := by ring
  have hraw : B * (1 + A) + A ≤
      ((q : ℝ) + C) * E + D * E ^ 2 := by
    have h := hpow E hE hE1
    dsimp [B, A, D] at *
    nlinarith [hBA]
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    norm_num
  have hgamma : Real.sqrt 2 * γ ≤ 2 * γ :=
    mul_le_mul_of_nonneg_right hsqrt2 hγ
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hfirst : ((q : ℝ) + C) * E ≤
      (2 * (q + γ)) * E := by
    apply mul_le_mul_of_nonneg_right _ hE
    dsimp [C]
    nlinarith [hgamma]
  have hgoal : B * (1 + A) + A ≤
      (2 * (q + γ)) * E + D * E ^ 2 := by
    linarith
  convert hgoal using 1
  dsimp [B, A, C, F]
  ring

private theorem p04_roundedGenericBlock_second_order {q : ℕ} [NeZero q]
    (hq : 3 ≤ q) (model : P04WilkinsonModel) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (x : ZMod q → ℂ) (k : ZMod q),
      model.epsilon ≤ 1 →
      ‖p04RoundedGenericRadixBlock model x k -
          ∑ j : ZMod q, ZMod.stdAddChar (j * k) * x j‖ ≤
        (2 * (q + model.gamma) * model.epsilon +
          D * model.epsilon ^ 2) *
            (∑ j : ZMod q, ‖x j‖) := by
  obtain ⟨D, hD, hbound⟩ :=
    p04_genericBlock_coefficient_second_order q hq model.gamma model.gamma_nonneg
  refine ⟨D, hD, ?_⟩
  intro x k hε
  have hbase := p04_roundedGenericBlock_error model x k hε
  have hcoeff := hbound model.epsilon (le_of_lt model.epsilon_pos) hε
  have hsum : 0 ≤ ∑ j : ZMod q, ‖x j‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff hsum)

private theorem p04_uniformBlock_sumSq_bound {q : ℕ} [NeZero q]
    (x e : ZMod q → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ k : ZMod q, ‖e k‖ ≤ c * (∑ j : ZMod q, ‖x j‖)) :
    (∑ k : ZMod q, ‖e k‖ ^ 2) ≤
      ((q : ℝ) * c) ^ 2 * (∑ j : ZMod q, ‖x j‖ ^ 2) := by
  let S := ∑ j : ZMod q, ‖x j‖
  let X := ∑ j : ZMod q, ‖x j‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hcs : S ^ 2 ≤ (q : ℝ) * X := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
      (fun j => ‖x j‖) (fun _ => (1 : ℝ))
    simpa [S, X, mul_comm] using h
  have hsquare (k : ZMod q) : ‖e k‖ ^ 2 ≤ (c * S) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hS)).2 (hpoint k)
  calc
    (∑ k : ZMod q, ‖e k‖ ^ 2) ≤
        ∑ k : ZMod q, (c * S) ^ 2 :=
      Finset.sum_le_sum fun k _ => hsquare k
    _ = (q : ℝ) * (c * S) ^ 2 := by simp
    _ = ((q : ℝ) * c ^ 2) * S ^ 2 := by ring
    _ ≤ ((q : ℝ) * c ^ 2) * ((q : ℝ) * X) := by
      exact mul_le_mul_of_nonneg_left hcs (mul_nonneg hq (sq_nonneg c))
    _ = ((q : ℝ) * c) ^ 2 * X := by ring

private theorem p04_uniformBlocks_sumSq_bound
    {B : Type*} [Fintype B] {q : ℕ} [NeZero q]
    (x e : B × ZMod q → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ b k, ‖e (b, k)‖ ≤
      c * (∑ j : ZMod q, ‖x (b, j)‖)) :
    (∑ p : B × ZMod q, ‖e p‖ ^ 2) ≤
      ((q : ℝ) * c) ^ 2 * (∑ p : B × ZMod q, ‖x p‖ ^ 2) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc
    (∑ b : B, ∑ k : ZMod q, ‖e (b, k)‖ ^ 2) ≤
        ∑ b : B, ((q : ℝ) * c) ^ 2 *
          (∑ j : ZMod q, ‖x (b, j)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro b _
      exact p04_uniformBlock_sumSq_bound
        (fun j => x (b, j)) (fun k => e (b, k)) c hc (hpoint b)
    _ = ((q : ℝ) * c) ^ 2 *
        (∑ b : B, ∑ j : ZMod q, ‖x (b, j)‖ ^ 2) := by
      rw [Finset.mul_sum]

private theorem p04_sqrt_sumSq_le
    {ι : Type*} [Fintype ι] (x e : ι → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : (∑ i, ‖e i‖ ^ 2) ≤ c ^ 2 * (∑ i, ‖x i‖ ^ 2)) :
    Real.sqrt (∑ i, ‖e i‖ ^ 2) ≤
      c * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
  calc
    Real.sqrt (∑ i, ‖e i‖ ^ 2) ≤
        Real.sqrt (c ^ 2 * (∑ i, ‖x i‖ ^ 2)) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (∑ i, ‖x i‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private noncomputable def p04BlockFirstCoeff (q : ℕ) (γ : ℝ) : ℝ :=
  if q = 2 then 1 else if q = 4 then 2 else 2 * (q + γ)

private theorem p04_stageBlock_pointwise {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : ZMod n → ℂ) (i : ZMod n),
        ‖p04RoundedMixedRadixBlockApply model stage x i -
          p04MixedRadixBlockApply stage x i‖ ≤
          (p04BlockFirstCoeff stage.radix γ * model.epsilon +
            D * model.epsilon ^ 2) *
          (∑ j : ZMod stage.radix,
            ‖x (stage.permutation
              (stage.reindex ((stage.reindex.symm i).1, j)))‖) := by
  rcases stage with ⟨radix, hrad, hnz, blockCount, hbc, heq,
    reindex, permutation, useTwiddle, twiddleExponent⟩
  let stage : P04MixedRadixStage n :=
    ⟨radix, hrad, hnz, blockCount, hbc, heq,
      reindex, permutation, useTwiddle, twiddleExponent⟩
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  by_cases h2 : stage.radix = 2
  · cases h2
    refine ⟨0, le_refl 0, ?_⟩
    intro model hmodel hε x i
    let bi := stage.reindex.symm i
    let x₂ : ZMod 2 → ℂ := fun j =>
      x (stage.permutation (stage.reindex (bi.1, j)))
    let k₂ : ZMod 2 := bi.2
    have hblock := p04_roundedRadixTwoBlock_error model x₂ k₂
    simpa [stage, p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
      p04BlockFirstCoeff, p04_sum_zmod_two, bi, x₂, k₂] using hblock
  · by_cases h4 : stage.radix = 4
    · cases h4
      refine ⟨1, by norm_num, ?_⟩
      intro model hmodel hε x i
      let bi := stage.reindex.symm i
      let x₄ : ZMod 4 → ℂ := fun j =>
        x (stage.permutation (stage.reindex (bi.1, j)))
      let k₄ : ZMod 4 := bi.2
      have hblock := p04_roundedRadixFourBlock_error model x₄ k₄
      simpa [stage, p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
        p04BlockFirstCoeff, h2, bi, x₄, k₄] using hblock
    · have hq : 3 ≤ stage.radix := by
        have hrad := stage.radix_two_le
        omega
      obtain ⟨D, hD, hbound⟩ :=
        p04_genericBlock_coefficient_second_order stage.radix hq γ hγ
      refine ⟨D, hD, ?_⟩
      intro model hmodel hε x i
      let bi := stage.reindex.symm i
      let xq : ZMod stage.radix → ℂ := fun j =>
        x (stage.permutation (stage.reindex (bi.1, j)))
      have hblock := p04_roundedGenericBlock_error model xq bi.2 hε
      have hcoeff := hbound model.epsilon (le_of_lt model.epsilon_pos) hε
      rw [← hmodel] at hcoeff
      have hS : 0 ≤ ∑ j : ZMod stage.radix, ‖xq j‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hbound' := hblock.trans
        (mul_le_mul_of_nonneg_right hcoeff hS)
      simpa [stage, p04RoundedMixedRadixBlockApply, p04MixedRadixBlockApply,
        p04BlockFirstCoeff, h2, h4, bi, xq, hmodel] using hbound'

private theorem p04BlockFirstCoeff_nonneg (q : ℕ) (γ : ℝ)
    (hγ : 0 ≤ γ) : 0 ≤ p04BlockFirstCoeff q γ := by
  unfold p04BlockFirstCoeff
  split_ifs <;> positivity

private theorem p04_stageBlock_norm_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i =>
          p04RoundedMixedRadixBlockApply model stage x i -
            p04MixedRadixBlockApply stage x i) ≤
          ((stage.radix : ℝ) *
            (p04BlockFirstCoeff stage.radix γ * model.epsilon +
              D * model.epsilon ^ 2)) * p04ComplexNorm2 x := by
  letI : NeZero stage.radix := ⟨stage.radix_ne_zero⟩
  obtain ⟨D, hD, hpoint⟩ := p04_stageBlock_pointwise stage γ hγ
  refine ⟨D, hD, ?_⟩
  intro model hmodel hε x
  let c := p04BlockFirstCoeff stage.radix γ * model.epsilon +
    D * model.epsilon ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg
      (mul_nonneg (p04BlockFirstCoeff_nonneg _ γ hγ)
        (le_of_lt model.epsilon_pos))
      (mul_nonneg hD (sq_nonneg _))
  let r : ZMod n → ℂ := fun i =>
    p04RoundedMixedRadixBlockApply model stage x i -
      p04MixedRadixBlockApply stage x i
  let u : Fin stage.blockCount × ZMod stage.radix → ℂ := fun p =>
    x (stage.permutation (stage.reindex p))
  let v : Fin stage.blockCount × ZMod stage.radix → ℂ := fun p =>
    r (stage.reindex p)
  have hpoint' (b : Fin stage.blockCount) (k : ZMod stage.radix) :
      ‖v (b, k)‖ ≤ c * (∑ j : ZMod stage.radix, ‖u (b, j)‖) := by
    simpa [v, u, r, c] using
      hpoint model hmodel hε x (stage.reindex (b, k))
  have hblocks := p04_uniformBlocks_sumSq_bound u v c hc hpoint'
  have hsumv : (∑ p : Fin stage.blockCount × ZMod stage.radix,
        ‖v p‖ ^ 2) = (∑ i : ZMod n, ‖r i‖ ^ 2) := by
    simpa [v] using
      (Equiv.sum_comp stage.reindex (fun i : ZMod n => ‖r i‖ ^ 2))
  have hsumu : (∑ p : Fin stage.blockCount × ZMod stage.radix,
        ‖u p‖ ^ 2) = (∑ i : ZMod n, ‖x i‖ ^ 2) := by
    calc
      (∑ p : Fin stage.blockCount × ZMod stage.radix, ‖u p‖ ^ 2) =
          ∑ i : ZMod n, ‖x (stage.permutation i)‖ ^ 2 := by
        simpa [u] using
          (Equiv.sum_comp stage.reindex
            (fun i : ZMod n => ‖x (stage.permutation i)‖ ^ 2))
      _ = ∑ i : ZMod n, ‖x i‖ ^ 2 := by
        exact Equiv.sum_comp stage.permutation (fun i : ZMod n => ‖x i‖ ^ 2)
  rw [hsumv, hsumu] at hblocks
  have hnorm := p04_sqrt_sumSq_le x r ((stage.radix : ℝ) * c)
    (mul_nonneg (by positivity) hc) hblocks
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq, r, c] using hnorm

private theorem p04_blockFirstCoeff_le_alpha (q : ℕ) (γ : ℝ) :
    (q : ℝ) * p04BlockFirstCoeff q γ ≤
      Real.sqrt q * p04Alpha q γ := by
  by_cases h2 : q = 2
  · subst q
    simp [p04BlockFirstCoeff, p04Alpha]
  · by_cases h4 : q = 4
    · subst q
      simp [p04BlockFirstCoeff, p04Alpha]
      norm_num
    · have hs : Real.sqrt (q : ℝ) ^ 2 = q := by
        rw [Real.sq_sqrt]
        positivity
      simp only [p04BlockFirstCoeff, p04Alpha, if_neg h2, if_neg h4]
      apply le_of_eq
      calc
        (q : ℝ) * (2 * (q + γ)) =
            2 * (Real.sqrt q) ^ 2 * (q + γ) := by rw [hs]; ring
        _ = Real.sqrt q * (2 * Real.sqrt q * (q + γ)) := by ring

private theorem p04_diagonal_norm_bound {n : ℕ} [NeZero n]
    (x e : ZMod n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ i, ‖e i‖ ≤ c * ‖x i‖) :
    p04ComplexNorm2 e ≤ c * p04ComplexNorm2 x := by
  have hsq : (∑ i : ZMod n, ‖e i‖ ^ 2) ≤
      c ^ 2 * (∑ i : ZMod n, ‖x i‖ ^ 2) := by
    calc
      (∑ i : ZMod n, ‖e i‖ ^ 2) ≤
          ∑ i : ZMod n, (c * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).2
          (hpoint i)
      _ = c ^ 2 * (∑ i : ZMod n, ‖x i‖ ^ 2) := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
  simpa [p04ComplexNorm2, p04ComplexNorm2Sq] using
    (p04_sqrt_sumSq_le x e c hc hsq)

private theorem p04_exactTwiddle_norm {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04MixedRadixTwiddleApply stage x) = p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, norm_mul, p04_stdAddChar_norm]
  · simp [p04MixedRadixTwiddleApply, h]

private theorem p04ComplexNorm2_eq_euclidean {n : ℕ} [NeZero n]
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 x =
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (ZMod n))‖ := by
  simp [p04ComplexNorm2, p04ComplexNorm2Sq, EuclideanSpace.norm_eq]

private theorem p04_complexNorm2_add_le {n : ℕ} [NeZero n]
    (a b : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i => a i + b i) ≤
      p04ComplexNorm2 a + p04ComplexNorm2 b := by
  let A : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 a
  let B : EuclideanSpace ℂ (ZMod n) := WithLp.toLp 2 b
  have heq : (WithLp.toLp 2 (fun i => a i + b i) :
      EuclideanSpace ℂ (ZMod n)) = A + B := by
    ext i
    rfl
  rw [p04ComplexNorm2_eq_euclidean,
    p04ComplexNorm2_eq_euclidean, p04ComplexNorm2_eq_euclidean, heq]
  exact norm_add_le A B

private theorem p04_exactTwiddle_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (a b : ZMod n → ℂ) :
    p04MixedRadixTwiddleApply stage (fun i => a i - b i) =
      fun i => p04MixedRadixTwiddleApply stage a i -
        p04MixedRadixTwiddleApply stage b i := by
  funext i
  by_cases h : stage.useTwiddle
  · simp [p04MixedRadixTwiddleApply, h, mul_sub]
  · simp [p04MixedRadixTwiddleApply, h]

private noncomputable def p04TwiddleFirstCoeff {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) : ℝ :=
  if stage.useTwiddle then 3 + 2 * γ else 0

private theorem p04_roundedTwiddle_norm_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ)
    (model : P04WilkinsonModel) (hmodel : model.gamma = γ)
    (hε : model.epsilon ≤ 1) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (fun i =>
      p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) ≤
      (p04TwiddleFirstCoeff stage γ * model.epsilon +
        (2 + 5 * Real.sqrt 2 * γ) * model.epsilon ^ 2) *
          p04ComplexNorm2 x := by
  let c := p04TwiddleFirstCoeff stage γ * model.epsilon +
    (2 + 5 * Real.sqrt 2 * γ) * model.epsilon ^ 2
  have hc : 0 ≤ c := by
    have hfirst : 0 ≤ p04TwiddleFirstCoeff stage γ := by
      unfold p04TwiddleFirstCoeff
      split_ifs <;> nlinarith
    have hsecond : 0 ≤ 2 + 5 * Real.sqrt 2 * γ := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hγ]
    exact add_nonneg
      (mul_nonneg hfirst (le_of_lt model.epsilon_pos))
      (mul_nonneg hsecond (sq_nonneg _))
  apply p04_diagonal_norm_bound x _ c hc
  intro i
  by_cases htw : stage.useTwiddle
  · have hterm := p04_roundedTerm_error model (stage.twiddleExponent i) (x i) hε
    rw [hmodel] at hterm
    have hsqrt : Real.sqrt (2 : ℝ) ≤ 2 := by
      apply (Real.sqrt_le_iff).2
      norm_num
    have hγ' := mul_le_mul_of_nonneg_right hsqrt hγ
    have hcoef :
        ((3 + Real.sqrt 2 * γ) * model.epsilon +
            (2 + 5 * Real.sqrt 2 * γ) * model.epsilon ^ 2) ≤ c := by
      dsimp [c, p04TwiddleFirstCoeff]
      rw [if_pos htw]
      nlinarith [mul_le_mul_of_nonneg_right hγ'
        (le_of_lt model.epsilon_pos)]
    simpa [p04RoundedMixedRadixTwiddleApply,
      p04MixedRadixTwiddleApply, htw] using
      hterm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x i)))
  · have hz : (p04RoundedMixedRadixTwiddleApply model stage x i -
        p04MixedRadixTwiddleApply stage x i) = 0 := by
      simp [p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, htw]
    rw [hz, norm_zero]
    exact mul_nonneg hc (norm_nonneg _)

private theorem p04_combine_stage_coeff
    (E S A B₀ B₁ T₀ T₁ : ℝ)
    (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hT₀ : 0 ≤ T₀) (hT₁ : 0 ≤ T₁)
    (hbase : B₀ ≤ S * A) :
    (T₀ * E + T₁ * E ^ 2) *
        (S + B₀ * E + B₁ * E ^ 2) +
      (B₀ * E + B₁ * E ^ 2) ≤
        S * (A + T₀) * E +
          (B₁ + T₁ * S + (T₀ + T₁) * (B₀ + B₁)) * E ^ 2 := by
  have hE2 : E ^ 2 ≤ E := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hE1)]
  have htb : T₀ * E + T₁ * E ^ 2 ≤ (T₀ + T₁) * E := by
    nlinarith [mul_le_mul_of_nonneg_left hE2 hT₁]
  have hbb : B₀ * E + B₁ * E ^ 2 ≤ (B₀ + B₁) * E := by
    nlinarith [mul_le_mul_of_nonneg_left hE2 hB₁]
  have htb0 : 0 ≤ T₀ * E + T₁ * E ^ 2 := by positivity
  have hbb0 : 0 ≤ B₀ * E + B₁ * E ^ 2 := by positivity
  have hprod :
      (T₀ * E + T₁ * E ^ 2) * (B₀ * E + B₁ * E ^ 2) ≤
        (T₀ + T₁) * (B₀ + B₁) * E ^ 2 := by
    calc
      (T₀ * E + T₁ * E ^ 2) * (B₀ * E + B₁ * E ^ 2) ≤
          ((T₀ + T₁) * E) * (B₀ * E + B₁ * E ^ 2) :=
        mul_le_mul_of_nonneg_right htb hbb0
      _ ≤ ((T₀ + T₁) * E) * ((B₀ + B₁) * E) := by
        exact mul_le_mul_of_nonneg_left hbb
          (mul_nonneg (add_nonneg hT₀ hT₁) hE)
      _ = (T₀ + T₁) * (B₀ + B₁) * E ^ 2 := by ring
  have hbase' := mul_le_mul_of_nonneg_right hbase hE
  nlinarith [hprod]

private theorem p04_stage_norm_error {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ)
    (hscale : ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply stage x) =
        Real.sqrt (stage.radix : ℝ) * p04ComplexNorm2 x) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i =>
          p04RoundedMixedRadixStageApply model stage x i -
            p04MixedRadixStageApply stage x i) ≤
          (Real.sqrt (stage.radix : ℝ) *
            (p04Alpha stage.radix γ + p04TwiddleFirstCoeff stage γ) *
              model.epsilon + D * model.epsilon ^ 2) *
            p04ComplexNorm2 x := by
  obtain ⟨D₀, hD₀, hblockAll⟩ := p04_stageBlock_norm_error stage γ hγ
  let S := Real.sqrt (stage.radix : ℝ)
  let A := p04Alpha stage.radix γ
  let B₀ := (stage.radix : ℝ) * p04BlockFirstCoeff stage.radix γ
  let B₁ := (stage.radix : ℝ) * D₀
  let T₀ := p04TwiddleFirstCoeff stage γ
  let T₁ := 2 + 5 * Real.sqrt 2 * γ
  let D := B₁ + T₁ * S + (T₀ + T₁) * (B₀ + B₁)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hA : 0 ≤ A := by
    dsimp [A, p04Alpha]
    split_ifs <;> positivity
  have hB₀ : 0 ≤ B₀ :=
    mul_nonneg (by positivity) (p04BlockFirstCoeff_nonneg _ γ hγ)
  have hB₁ : 0 ≤ B₁ := mul_nonneg (by positivity) hD₀
  have hT₀ : 0 ≤ T₀ := by
    dsimp [T₀, p04TwiddleFirstCoeff]
    split_ifs <;> nlinarith
  have hT₁ : 0 ≤ T₁ := by
    dsimp [T₁]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) hγ]
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hbase : B₀ ≤ S * A := p04_blockFirstCoeff_le_alpha stage.radix γ
  refine ⟨D, hD, ?_⟩
  intro model hmodel hε x
  let E := model.epsilon
  let cB := B₀ * E + B₁ * E ^ 2
  let cT := T₀ * E + T₁ * E ^ 2
  let rb := p04RoundedMixedRadixBlockApply model stage x
  let b := p04MixedRadixBlockApply stage x
  let eB : ZMod n → ℂ := fun i => rb i - b i
  let eT : ZMod n → ℂ := fun i =>
    p04RoundedMixedRadixTwiddleApply model stage rb i -
      p04MixedRadixTwiddleApply stage rb i
  let eS : ZMod n → ℂ := fun i =>
    p04RoundedMixedRadixStageApply model stage x i -
      p04MixedRadixStageApply stage x i
  have hcT : 0 ≤ cT := by
    dsimp [cT]
    exact add_nonneg
      (mul_nonneg hT₀ (le_of_lt model.epsilon_pos))
      (mul_nonneg hT₁ (sq_nonneg _))
  have hbnd : p04ComplexNorm2 eB ≤ cB * p04ComplexNorm2 x := by
    have h := hblockAll model hmodel hε x
    convert h using 1
    dsimp [cB, B₀, B₁, E]
    ring
  have hbNorm : p04ComplexNorm2 b = S * p04ComplexNorm2 x := by
    have ht := p04_exactTwiddle_norm stage b
    have hs := hscale x
    simpa [p04MixedRadixStageApply, b, S] using ht.symm.trans hs
  have hrb : p04ComplexNorm2 rb ≤
      (S * p04ComplexNorm2 x) + p04ComplexNorm2 eB := by
    have htri := p04_complexNorm2_add_le eB b
    have heq : (fun i => eB i + b i) = rb := by
      funext i
      dsimp [eB]
      ring
    rw [heq, hbNorm] at htri
    linarith
  have htw : p04ComplexNorm2 eT ≤ cT * p04ComplexNorm2 rb := by
    have h := p04_roundedTwiddle_norm_error stage γ hγ model hmodel hε rb
    convert h using 1
  have hdecomp : eS =
      fun i => eT i + p04MixedRadixTwiddleApply stage eB i := by
    funext i
    by_cases htw : stage.useTwiddle
    · simp [eS, eT, eB, rb, b, p04RoundedMixedRadixStageApply,
        p04MixedRadixStageApply, p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, htw, mul_sub]
    · simp [eS, eT, eB, rb, b, p04RoundedMixedRadixStageApply,
        p04MixedRadixStageApply, p04RoundedMixedRadixTwiddleApply,
        p04MixedRadixTwiddleApply, htw]
  have htri : p04ComplexNorm2 eS ≤
      p04ComplexNorm2 eT + p04ComplexNorm2 eB := by
    rw [hdecomp]
    calc
      p04ComplexNorm2 (fun i => eT i + p04MixedRadixTwiddleApply stage eB i) ≤
          p04ComplexNorm2 eT +
            p04ComplexNorm2 (p04MixedRadixTwiddleApply stage eB) :=
        p04_complexNorm2_add_le _ _
      _ = p04ComplexNorm2 eT + p04ComplexNorm2 eB := by
        rw [p04_exactTwiddle_norm]
  have hnormx : 0 ≤ p04ComplexNorm2 x := by
    unfold p04ComplexNorm2
    exact Real.sqrt_nonneg _
  have hraw : p04ComplexNorm2 eS ≤
      (cT * (S + cB) + cB) * p04ComplexNorm2 x := by
    have hrb' : p04ComplexNorm2 rb ≤ (S + cB) * p04ComplexNorm2 x := by
      nlinarith [hbnd, hrb]
    have htw' := mul_le_mul_of_nonneg_left hrb' hcT
    nlinarith [htri, htw, hbnd]
  have hcoef := p04_combine_stage_coeff E S A B₀ B₁ T₀ T₁
    (le_of_lt model.epsilon_pos) hε hS hA hB₀ hB₁ hT₀ hT₁ hbase
  have hgoal : p04ComplexNorm2 eS ≤
      (S * (A + T₀) * E + D * E ^ 2) * p04ComplexNorm2 x := by
    apply hraw.trans
    apply mul_le_mul_of_nonneg_right _ hnormx
    simpa [cT, cB, D, add_assoc] using hcoef
  convert hgoal using 1

private theorem p04_exactBlock_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (a b : ZMod n → ℂ) :
    p04MixedRadixBlockApply stage (fun i => a i - b i) =
      fun i => p04MixedRadixBlockApply stage a i -
        p04MixedRadixBlockApply stage b i := by
  funext i
  simp only [p04MixedRadixBlockApply]
  simp_rw [mul_sub, ← Finset.sum_sub_distrib]

private theorem p04_exactStage_sub {n : ℕ} [NeZero n]
    (stage : P04MixedRadixStage n) (a b : ZMod n → ℂ) :
    p04MixedRadixStageApply stage (fun i => a i - b i) =
      fun i => p04MixedRadixStageApply stage a i -
        p04MixedRadixStageApply stage b i := by
  unfold p04MixedRadixStageApply
  rw [p04_exactBlock_sub, p04_exactTwiddle_sub]

private noncomputable def p04ListExact {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state stage => p04MixedRadixStageApply stage state) x

private noncomputable def p04ListRounded {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (l : List (P04MixedRadixStage n))
    (x : ZMod n → ℂ) : ZMod n → ℂ :=
  l.foldl (fun state stage => p04RoundedMixedRadixStageApply model stage state) x

private noncomputable def p04ListScale {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) : ℝ :=
  (l.map fun stage => Real.sqrt (stage.radix : ℝ)).prod

private noncomputable def p04ListCoeff {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (γ : ℝ) : ℝ :=
  (l.map fun stage => p04Alpha stage.radix γ +
    p04TwiddleFirstCoeff stage γ).sum

private theorem p04ListExact_append {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (s : P04MixedRadixStage n)
    (x : ZMod n → ℂ) :
    p04ListExact (l ++ [s]) x = p04MixedRadixStageApply s (p04ListExact l x) := by
  simp [p04ListExact, List.foldl_append]

private theorem p04ListRounded_append {n : ℕ} [NeZero n]
    (model : P04WilkinsonModel) (l : List (P04MixedRadixStage n))
    (s : P04MixedRadixStage n) (x : ZMod n → ℂ) :
    p04ListRounded model (l ++ [s]) x =
      p04RoundedMixedRadixStageApply model s (p04ListRounded model l x) := by
  simp [p04ListRounded, List.foldl_append]

private theorem p04ListScale_append {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (s : P04MixedRadixStage n) :
    p04ListScale (l ++ [s]) =
      p04ListScale l * Real.sqrt (s.radix : ℝ) := by
  simp [p04ListScale]

private theorem p04ListCoeff_append {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (s : P04MixedRadixStage n) (γ : ℝ) :
    p04ListCoeff (l ++ [s]) γ = p04ListCoeff l γ +
      (p04Alpha s.radix γ + p04TwiddleFirstCoeff s γ) := by
  simp [p04ListCoeff]

private theorem p04ListScale_nonneg {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) : 0 ≤ p04ListScale l := by
  induction l using List.reverseRecOn with
  | nil => simp [p04ListScale]
  | append_singleton l s ih =>
      rw [p04ListScale_append]
      exact mul_nonneg ih (Real.sqrt_nonneg _)

private theorem p04StageCoeff_nonneg {n : ℕ} [NeZero n]
    (s : P04MixedRadixStage n) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04Alpha s.radix γ + p04TwiddleFirstCoeff s γ := by
  have ha : 0 ≤ p04Alpha s.radix γ := by
    unfold p04Alpha
    split_ifs <;> positivity
  have ht : 0 ≤ p04TwiddleFirstCoeff s γ := by
    unfold p04TwiddleFirstCoeff
    split_ifs <;> nlinarith
  exact add_nonneg ha ht

private theorem p04ListCoeff_nonneg {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n)) (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04ListCoeff l γ := by
  induction l using List.reverseRecOn with
  | nil => simp [p04ListCoeff]
  | append_singleton l s ih =>
      rw [p04ListCoeff_append]
      exact add_nonneg ih (p04StageCoeff_nonneg s γ hγ)

private theorem p04ListExact_norm_scaling {n : ℕ} [NeZero n]
    (l : List (P04MixedRadixStage n))
    (hscale : ∀ s ∈ l, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 x)
    (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04ListExact l x) =
      p04ListScale l * p04ComplexNorm2 x := by
  induction l using List.reverseRecOn with
  | nil => simp [p04ListExact, p04ListScale]
  | append_singleton l s ih =>
      have hs : ∀ y : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply s y) =
            Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 y := by
        exact hscale s (by simp)
      have hl : ∀ t ∈ l, ∀ y : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply t y) =
            Real.sqrt (t.radix : ℝ) * p04ComplexNorm2 y := by
        intro t ht y
        exact hscale t (by simp [ht]) y
      rw [p04ListExact_append, hs, ih hl, p04ListScale_append]
      ring

private theorem p04_compose_scaled_coeff
    (E P S K a Dp Ds : ℝ)
    (hE : 0 ≤ E) (hE1 : E ≤ 1)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hK : 0 ≤ K) (ha : 0 ≤ a)
    (hDp : 0 ≤ Dp) (hDs : 0 ≤ Ds) :
    (S * a * E + Ds * E ^ 2) *
        (P + (P * K * E + Dp * E ^ 2)) +
      S * (P * K * E + Dp * E ^ 2) ≤
        (P * S) * (K + a) * E +
          (Ds * P + S * Dp +
            (S * a + Ds) * (P * K + Dp)) * E ^ 2 := by
  have hE2 : E ^ 2 ≤ E := by
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hE1)]
  have hloc : S * a * E + Ds * E ^ 2 ≤ (S * a + Ds) * E := by
    nlinarith [mul_le_mul_of_nonneg_left hE2 hDs]
  have hprev : P * K * E + Dp * E ^ 2 ≤ (P * K + Dp) * E := by
    nlinarith [mul_le_mul_of_nonneg_left hE2 hDp]
  have hloc0 : 0 ≤ S * a * E + Ds * E ^ 2 := by positivity
  have hprev0 : 0 ≤ P * K * E + Dp * E ^ 2 := by positivity
  have hprod :
      (S * a * E + Ds * E ^ 2) * (P * K * E + Dp * E ^ 2) ≤
        (S * a + Ds) * (P * K + Dp) * E ^ 2 := by
    calc
      (S * a * E + Ds * E ^ 2) * (P * K * E + Dp * E ^ 2) ≤
          ((S * a + Ds) * E) * (P * K * E + Dp * E ^ 2) :=
        mul_le_mul_of_nonneg_right hloc hprev0
      _ ≤ ((S * a + Ds) * E) * ((P * K + Dp) * E) := by
        exact mul_le_mul_of_nonneg_left hprev (by positivity)
      _ = (S * a + Ds) * (P * K + Dp) * E ^ 2 := by ring
  nlinarith [hprod]

private theorem p04List_error {n : ℕ} [NeZero n]
    (γ : ℝ) (hγ : 0 ≤ γ)
    (l : List (P04MixedRadixStage n))
    (hscale : ∀ s ∈ l, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 x) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i =>
          p04ListRounded model l x i - p04ListExact l x i) ≤
          (p04ListScale l * p04ListCoeff l γ * model.epsilon +
            D * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  induction l using List.reverseRecOn with
  | nil =>
      refine ⟨0, le_refl 0, ?_⟩
      intro model hmodel hε x
      simp [p04ListRounded, p04ListExact, p04ListCoeff,
        p04ComplexNorm2, p04ComplexNorm2Sq]
  | append_singleton l s ih =>
      have hl : ∀ t ∈ l, ∀ y : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply t y) =
            Real.sqrt (t.radix : ℝ) * p04ComplexNorm2 y := by
        intro t ht y
        exact hscale t (by simp [ht]) y
      have hs : ∀ y : ZMod n → ℂ,
          p04ComplexNorm2 (p04MixedRadixStageApply s y) =
            Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 y :=
        hscale s (by simp)
      obtain ⟨Dp, hDp, hprevAll⟩ := ih hl
      obtain ⟨Ds, hDs, hstageAll⟩ := p04_stage_norm_error s γ hγ hs
      let P := p04ListScale l
      let S := Real.sqrt (s.radix : ℝ)
      let K := p04ListCoeff l γ
      let a := p04Alpha s.radix γ + p04TwiddleFirstCoeff s γ
      let D := Ds * P + S * Dp + (S * a + Ds) * (P * K + Dp)
      have hP : 0 ≤ P := p04ListScale_nonneg l
      have hS : 0 ≤ S := Real.sqrt_nonneg _
      have hK : 0 ≤ K := p04ListCoeff_nonneg l γ hγ
      have ha : 0 ≤ a := p04StageCoeff_nonneg s γ hγ
      have hD : 0 ≤ D := by
        dsimp [D]
        positivity
      refine ⟨D, hD, ?_⟩
      intro model hmodel hε x
      let E := model.epsilon
      let cPrev := P * K * E + Dp * E ^ 2
      let cLoc := S * a * E + Ds * E ^ 2
      let rp := p04ListRounded model l x
      let ep := p04ListExact l x
      let ePrev : ZMod n → ℂ := fun i => rp i - ep i
      let eLoc : ZMod n → ℂ := fun i =>
        p04RoundedMixedRadixStageApply model s rp i -
          p04MixedRadixStageApply s rp i
      let eFinal : ZMod n → ℂ := fun i =>
        p04ListRounded model (l ++ [s]) x i -
          p04ListExact (l ++ [s]) x i
      have hcLoc : 0 ≤ cLoc := by
        dsimp [cLoc]
        exact add_nonneg
          (mul_nonneg (mul_nonneg hS ha) (le_of_lt model.epsilon_pos))
          (mul_nonneg hDs (sq_nonneg _))
      have hprev : p04ComplexNorm2 ePrev ≤
          cPrev * p04ComplexNorm2 x := by
        have h := hprevAll model hmodel hε x
        convert h using 1
      have hepnorm : p04ComplexNorm2 ep = P * p04ComplexNorm2 x :=
        p04ListExact_norm_scaling l hl x
      have hrp : p04ComplexNorm2 rp ≤
          (P + cPrev) * p04ComplexNorm2 x := by
        have htri := p04_complexNorm2_add_le ePrev ep
        have heq : (fun i => ePrev i + ep i) = rp := by
          funext i
          dsimp [ePrev]
          ring
        rw [heq, hepnorm] at htri
        nlinarith [hprev]
      have hloc : p04ComplexNorm2 eLoc ≤
          cLoc * p04ComplexNorm2 rp := by
        have h := hstageAll model hmodel hε rp
        convert h using 1
      have hdecomp : eFinal =
          fun i => eLoc i + p04MixedRadixStageApply s ePrev i := by
        funext i
        rw [p04_exactStage_sub]
        simp [eFinal, eLoc, ePrev, rp, ep,
          p04ListRounded_append, p04ListExact_append]
      have htri : p04ComplexNorm2 eFinal ≤
          p04ComplexNorm2 eLoc + S * p04ComplexNorm2 ePrev := by
        rw [hdecomp]
        have h := p04_complexNorm2_add_le eLoc
          (p04MixedRadixStageApply s ePrev)
        rw [hs] at h
        exact h
      have hnormx : 0 ≤ p04ComplexNorm2 x := by
        unfold p04ComplexNorm2
        exact Real.sqrt_nonneg _
      have hraw : p04ComplexNorm2 eFinal ≤
          (cLoc * (P + cPrev) + S * cPrev) * p04ComplexNorm2 x := by
        have hmul := mul_le_mul_of_nonneg_left hrp hcLoc
        have hprev' := mul_le_mul_of_nonneg_left hprev hS
        nlinarith [htri, hloc]
      have hcoef := p04_compose_scaled_coeff E P S K a Dp Ds
        (le_of_lt model.epsilon_pos) hε hP hS hK ha hDp hDs
      have hgoal : p04ComplexNorm2 eFinal ≤
          ((P * S) * (K + a) * E + D * E ^ 2) *
            p04ComplexNorm2 x := by
        apply hraw.trans
        apply mul_le_mul_of_nonneg_right _ hnormx
        simpa [cLoc, cPrev, D] using hcoef
      convert hgoal using 1
      simp only [p04ListScale_append, p04ListCoeff_append]
      dsimp [P, S, K, a, E]

private theorem p04_planListScale {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) :
    p04ListScale (List.ofFn plan.stage) = Real.sqrt (n : ℝ) := by
  unfold p04ListScale
  simp only [List.map_ofFn, List.prod_ofFn]
  calc
    (∏ i : Fin plan.stageCount, Real.sqrt ((plan.stage i).radix : ℝ)) =
        Real.sqrt (∏ i : Fin plan.stageCount, ((plan.stage i).radix : ℝ)) := by
      rw [Real.sqrt_prod]
      intro i _
      positivity
    _ = Real.sqrt (n : ℝ) := by
      norm_cast
      rw [plan.order_factorization]

private theorem p04_twiddleCoeff_sum {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    (∑ i : Fin plan.stageCount,
      p04TwiddleFirstCoeff (plan.stage i) γ) =
        ((plan.stageCount : ℝ) - 1) * (3 + 2 * γ) := by
  rcases plan with ⟨stageCount, hpos, stage, orderfac, twpattern,
    finalPermutation, variant, exactfac, stagenorm, fsurj, frms⟩
  cases stageCount with
  | zero => omega
  | succ r =>
  rw [Fin.sum_univ_castSucc]
  have hfirst : (∑ i : Fin r,
      p04TwiddleFirstCoeff (stage i.castSucc) γ) =
      (r : ℝ) * (3 + 2 * γ) := by
    simp [p04TwiddleFirstCoeff, twpattern, Fin.val_castSucc]
    ring
  rw [hfirst]
  have hlast : p04TwiddleFirstCoeff (stage (Fin.last r)) γ = 0 := by
    simp [p04TwiddleFirstCoeff, twpattern]
  rw [hlast]
  push_cast
  ring

private theorem p04_planListCoeff {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) :
    p04ListCoeff (List.ofFn plan.stage) γ = p04K plan γ := by
  unfold p04ListCoeff p04K
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [Finset.sum_add_distrib]
  rw [p04_twiddleCoeff_sum]

private theorem p04_permute_norm {n : ℕ} [NeZero n]
    (perm : ZMod n ≃ ZMod n) (x : ZMod n → ℂ) :
    p04ComplexNorm2 (p04Permute perm x) = p04ComplexNorm2 x := by
  unfold p04ComplexNorm2 p04ComplexNorm2Sq p04Permute
  congr 1
  exact Equiv.sum_comp perm (fun i : ZMod n => ‖x i‖ ^ 2)

private theorem p04_fft_norm_error {n : ℕ} [NeZero n]
    (plan : P04MixedRadixFftPlan n) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : ZMod n → ℂ),
        p04ComplexNorm2 (fun i =>
          p04RoundedFftApply plan model x i - p04FourierTransform x i) ≤
          (Real.sqrt (n : ℝ) * p04K plan γ * model.epsilon +
            D * model.epsilon ^ 2) * p04ComplexNorm2 x := by
  let l := List.ofFn plan.stage
  have hscale : ∀ s ∈ l, ∀ x : ZMod n → ℂ,
      p04ComplexNorm2 (p04MixedRadixStageApply s x) =
        Real.sqrt (s.radix : ℝ) * p04ComplexNorm2 x := by
    intro s hs x
    obtain ⟨i, hi⟩ := (List.mem_ofFn.mp hs)
    subst s
    exact plan.stage_norm_scaling i x
  obtain ⟨D, hD, hbound⟩ := p04List_error γ hγ l hscale
  refine ⟨D, hD, ?_⟩
  intro model hmodel hε x
  have herr : (fun i => p04RoundedFftApply plan model x i -
      p04FourierTransform x i) =
        p04Permute plan.finalPermutation
          (fun i => p04ListRounded model l x i - p04ListExact l x i) := by
    rw [← plan.exact_factorization x]
    funext i
    simp [p04RoundedFftApply, p04Permute, l, p04ListRounded,
      p04ListExact, p04ApplyRoundedMixedRadixStages,
      p04ApplyMixedRadixStages]
  rw [herr, p04_permute_norm]
  have h := hbound model hmodel hε x
  simpa [p04_planListScale, p04_planListCoeff, l] using h

private abbrev P04AxisBase {m : ℕ} (axis : Fin m → P04FftAxis)
    (i : Fin m) :=
  {index : P04MultiIndex axis // index i = 0}

private noncomputable def p04_axisFiberEquiv {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m) :
    P04AxisBase axis i × ZMod (axis i).order ≃ P04MultiIndex axis where
  toFun p := Function.update p.1.1 i p.2
  invFun index :=
    (⟨Function.update index i 0, by simp⟩, index i)
  left_inv := by
    intro p
    rcases p with ⟨⟨base, hbase⟩, k⟩
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hj : j = i
      · subst j
        simp [hbase]
      · simp [Function.update, hj, Ne.symm hj]
    · simp
  right_inv := by
    intro index
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update, hj, Ne.symm hj]

private theorem p04_fiber_norm_bound
    {B : Type*} [Fintype B] {q : ℕ} [NeZero q]
    (x e : B × ZMod q → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hpoint : ∀ b : B,
      Real.sqrt (∑ k : ZMod q, ‖e (b, k)‖ ^ 2) ≤
        c * Real.sqrt (∑ k : ZMod q, ‖x (b, k)‖ ^ 2)) :
    Real.sqrt (∑ p : B × ZMod q, ‖e p‖ ^ 2) ≤
      c * Real.sqrt (∑ p : B × ZMod q, ‖x p‖ ^ 2) := by
  have hsq : (∑ p : B × ZMod q, ‖e p‖ ^ 2) ≤
      c ^ 2 * (∑ p : B × ZMod q, ‖x p‖ ^ 2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    calc
      (∑ b : B, ∑ k : ZMod q, ‖e (b, k)‖ ^ 2) ≤
          ∑ b : B, c ^ 2 * (∑ k : ZMod q, ‖x (b, k)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro b _
        have hb := hpoint b
        have hsqe : 0 ≤ ∑ k : ZMod q, ‖e (b, k)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hsqx : 0 ≤ ∑ k : ZMod q, ‖x (b, k)‖ ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hs := (sq_le_sq₀ (Real.sqrt_nonneg _)
          (mul_nonneg hc (Real.sqrt_nonneg _))).2 hb
        nlinarith [Real.sq_sqrt hsqe, Real.sq_sqrt hsqx]
      _ = c ^ 2 * (∑ b : B, ∑ k : ZMod q, ‖x (b, k)‖ ^ 2) := by
        rw [Finset.mul_sum]
  exact p04_sqrt_sumSq_le x e c hc hsq

private theorem p04MultiNorm2_eq_sqrtSum {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    p04MultiNorm2 x = Real.sqrt (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
  unfold p04MultiNorm2
  simp [EuclideanSpace.norm_eq]

private theorem p04MultiNorm2_nonneg {m : ℕ}
    {axis : Fin m → P04FftAxis} (x : P04MultiArray axis) :
    0 ≤ p04MultiNorm2 x := by
  rw [p04MultiNorm2_eq_sqrtSum]
  exact Real.sqrt_nonneg _

private theorem p04MultiNorm2_add_le {m : ℕ}
    {axis : Fin m → P04FftAxis} (x y : P04MultiArray axis) :
    p04MultiNorm2 (fun index => x index + y index) ≤
      p04MultiNorm2 x + p04MultiNorm2 y := by
  let X : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℂ (P04MultiIndex axis) := WithLp.toLp 2 y
  have heq : (WithLp.toLp 2 (fun index => x index + y index) :
      EuclideanSpace ℂ (P04MultiIndex axis)) = X + Y := by
    ext index
    rfl
  unfold p04MultiNorm2
  simpa [X, Y, heq] using norm_add_le X Y

private theorem p04_coord_exact_slice {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (base : P04AxisBase axis i) (k : ZMod (axis i).order)
    (x : P04MultiArray axis) :
    p04CoordinateTransform axis i x (Function.update base.1 i k) =
      p04FourierTransform
        (fun j => x (Function.update base.1 i j)) k := by
  simp [p04CoordinateTransform, p04FourierTransform,
    Function.update]

private theorem p04_coord_rounded_slice {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (base : P04AxisBase axis i) (k : ZMod (axis i).order)
    (model : P04WilkinsonModel) (x : P04MultiArray axis) :
    p04RoundedCoordinateTransform axis i model x
        (Function.update base.1 i k) =
      p04RoundedFftApply (axis i).plan model
        (fun j => x (Function.update base.1 i j)) k := by
  simp [p04RoundedCoordinateTransform, Function.update]

private theorem p04AxisK_nonneg (axis : P04FftAxis) (γ : ℝ)
    (hγ : 0 ≤ γ) : 0 ≤ p04AxisK axis γ := by
  unfold p04AxisK
  rw [← p04_planListCoeff]
  exact p04ListCoeff_nonneg (List.ofFn axis.plan.stage) γ hγ

private theorem p04_coordinate_norm_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : P04MultiArray axis),
        p04MultiNorm2 (fun index =>
          p04RoundedCoordinateTransform axis i model x index -
            p04CoordinateTransform axis i x index) ≤
          (Real.sqrt ((axis i).order : ℝ) * p04AxisK (axis i) γ *
              model.epsilon + D * model.epsilon ^ 2) * p04MultiNorm2 x := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  obtain ⟨D, hD, hOne⟩ := p04_fft_norm_error (axis i).plan γ hγ
  refine ⟨D, hD, ?_⟩
  intro model hmodel hε x
  let c := Real.sqrt ((axis i).order : ℝ) * p04AxisK (axis i) γ *
    model.epsilon + D * model.epsilon ^ 2
  have hc : 0 ≤ c := by
    dsimp [c]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (p04AxisK_nonneg (axis i) γ hγ))
        (le_of_lt model.epsilon_pos))
      (mul_nonneg hD (sq_nonneg _))
  let e : P04MultiArray axis := fun index =>
    p04RoundedCoordinateTransform axis i model x index -
      p04CoordinateTransform axis i x index
  let f := p04_axisFiberEquiv axis i
  let u : P04AxisBase axis i × ZMod (axis i).order → ℂ := fun p => x (f p)
  let v : P04AxisBase axis i × ZMod (axis i).order → ℂ := fun p => e (f p)
  have hpoint (base : P04AxisBase axis i) :
      Real.sqrt (∑ k : ZMod (axis i).order, ‖v (base, k)‖ ^ 2) ≤
        c * Real.sqrt (∑ k : ZMod (axis i).order, ‖u (base, k)‖ ^ 2) := by
    have h := hOne model hmodel hε
      (fun j => x (Function.update base.1 i j))
    simpa [p04ComplexNorm2, p04ComplexNorm2Sq,
      p04AxisK, c, v, u, e, f, p04_axisFiberEquiv,
      p04_coord_exact_slice, p04_coord_rounded_slice] using h
  have hfiber := p04_fiber_norm_bound u v c hc hpoint
  have hsumv : (∑ p : P04AxisBase axis i × ZMod (axis i).order,
      ‖v p‖ ^ 2) = (∑ index : P04MultiIndex axis, ‖e index‖ ^ 2) := by
    simpa [v] using (Equiv.sum_comp f (fun index => ‖e index‖ ^ 2))
  have hsumu : (∑ p : P04AxisBase axis i × ZMod (axis i).order,
      ‖u p‖ ^ 2) = (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
    simpa [u] using (Equiv.sum_comp f (fun index => ‖x index‖ ^ 2))
  rw [hsumv, hsumu] at hfiber
  simpa [p04MultiNorm2_eq_sqrtSum, e, c] using hfiber

private theorem p04_coordinate_norm_scaling {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (x : P04MultiArray axis) :
    p04MultiNorm2 (p04CoordinateTransform axis i x) =
      Real.sqrt ((axis i).order : ℝ) * p04MultiNorm2 x := by
  letI : NeZero (axis i).order := ⟨Nat.ne_of_gt (axis i).order_pos⟩
  let S := Real.sqrt ((axis i).order : ℝ)
  have hS : 0 < S := Real.sqrt_pos.2 (by exact_mod_cast (axis i).order_pos)
  let f := p04_axisFiberEquiv axis i
  let u : P04AxisBase axis i × ZMod (axis i).order → ℂ := fun p => x (f p)
  let v : P04AxisBase axis i × ZMod (axis i).order → ℂ :=
    fun p => p04CoordinateTransform axis i x (f p)
  have hfiber (base : P04AxisBase axis i) :
      Real.sqrt (∑ k : ZMod (axis i).order, ‖v (base, k)‖ ^ 2) =
        S * Real.sqrt (∑ k : ZMod (axis i).order, ‖u (base, k)‖ ^ 2) := by
    have h := (axis i).plan.fourier_rms_scaling
      (fun j => x (Function.update base.1 i j))
    unfold p04ComplexRms at h
    have hs' : S ≠ 0 := ne_of_gt hS
    have h' : p04ComplexNorm2
        (p04FourierTransform (fun j => x (Function.update base.1 i j))) =
          S * p04ComplexNorm2 (fun j => x (Function.update base.1 i j)) := by
      dsimp [S] at h ⊢
      apply (div_eq_iff hs').mp at h
      simpa [S, hs', mul_assoc] using h
    simpa [p04ComplexNorm2, p04ComplexNorm2Sq, v, u, f,
      p04_axisFiberEquiv, p04_coord_exact_slice, S] using h'
  have hforward := p04_fiber_norm_bound u v S (le_of_lt hS)
    (fun base => le_of_eq (hfiber base))
  have hbackward := p04_fiber_norm_bound v u (S⁻¹) (inv_nonneg.mpr (le_of_lt hS))
    (fun base => by
      rw [hfiber base]
      simp [ne_of_gt hS])
  have hv : (∑ p : P04AxisBase axis i × ZMod (axis i).order,
      ‖v p‖ ^ 2) =
      (∑ index : P04MultiIndex axis,
        ‖p04CoordinateTransform axis i x index‖ ^ 2) := by
    simpa [v] using (Equiv.sum_comp f
      (fun index => ‖p04CoordinateTransform axis i x index‖ ^ 2))
  have hu : (∑ p : P04AxisBase axis i × ZMod (axis i).order,
      ‖u p‖ ^ 2) = (∑ index : P04MultiIndex axis, ‖x index‖ ^ 2) := by
    simpa [u] using (Equiv.sum_comp f (fun index => ‖x index‖ ^ 2))
  rw [hv, hu] at hforward
  rw [hu, hv] at hbackward
  simp only [← p04MultiNorm2_eq_sqrtSum] at hforward hbackward
  have hback : S * p04MultiNorm2 x ≤
      p04MultiNorm2 (p04CoordinateTransform axis i x) := by
    have := mul_le_mul_of_nonneg_left hbackward (le_of_lt hS)
    simpa [S, mul_assoc, ne_of_gt hS] using this
  exact le_antisymm hforward hback

private theorem p04_coordinate_sub {m : ℕ}
    (axis : Fin m → P04FftAxis) (i : Fin m)
    (a b : P04MultiArray axis) :
    p04CoordinateTransform axis i (fun index => a index - b index) =
      fun index => p04CoordinateTransform axis i a index -
        p04CoordinateTransform axis i b index := by
  funext index
  simp only [p04CoordinateTransform]
  simp_rw [mul_sub, ← Finset.sum_sub_distrib]

private noncomputable def p04AxisListExact {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m))
    (x : P04MultiArray axis) : P04MultiArray axis :=
  l.foldl (fun state i => p04CoordinateTransform axis i state) x

private noncomputable def p04AxisListRounded {m : ℕ}
    (axis : Fin m → P04FftAxis) (model : P04WilkinsonModel)
    (l : List (Fin m)) (x : P04MultiArray axis) : P04MultiArray axis :=
  l.foldl (fun state i => p04RoundedCoordinateTransform axis i model state) x

private noncomputable def p04AxisListScale {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) : ℝ :=
  (l.map fun i => Real.sqrt ((axis i).order : ℝ)).prod

private noncomputable def p04AxisListCoeff {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) (γ : ℝ) : ℝ :=
  (l.map fun i => p04AxisK (axis i) γ).sum

private theorem p04AxisListExact_append {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) (i : Fin m)
    (x : P04MultiArray axis) :
    p04AxisListExact axis (l ++ [i]) x =
      p04CoordinateTransform axis i (p04AxisListExact axis l x) := by
  simp [p04AxisListExact, List.foldl_append]

private theorem p04AxisListRounded_append {m : ℕ}
    (axis : Fin m → P04FftAxis) (model : P04WilkinsonModel)
    (l : List (Fin m)) (i : Fin m) (x : P04MultiArray axis) :
    p04AxisListRounded axis model (l ++ [i]) x =
      p04RoundedCoordinateTransform axis i model
        (p04AxisListRounded axis model l x) := by
  simp [p04AxisListRounded, List.foldl_append]

private theorem p04AxisListScale_append {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) (i : Fin m) :
    p04AxisListScale axis (l ++ [i]) =
      p04AxisListScale axis l * Real.sqrt ((axis i).order : ℝ) := by
  simp [p04AxisListScale]

private theorem p04AxisListCoeff_append {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) (i : Fin m)
    (γ : ℝ) :
    p04AxisListCoeff axis (l ++ [i]) γ =
      p04AxisListCoeff axis l γ + p04AxisK (axis i) γ := by
  simp [p04AxisListCoeff]

private theorem p04AxisListScale_nonneg {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m)) :
    0 ≤ p04AxisListScale axis l := by
  induction l using List.reverseRecOn with
  | nil => simp [p04AxisListScale]
  | append_singleton l i ih =>
      rw [p04AxisListScale_append]
      exact mul_nonneg ih (Real.sqrt_nonneg _)

private theorem p04AxisListCoeff_nonneg {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    0 ≤ p04AxisListCoeff axis l γ := by
  induction l using List.reverseRecOn with
  | nil => simp [p04AxisListCoeff]
  | append_singleton l i ih =>
      rw [p04AxisListCoeff_append]
      exact add_nonneg ih (p04AxisK_nonneg (axis i) γ hγ)

private theorem p04AxisListExact_norm_scaling {m : ℕ}
    (axis : Fin m → P04FftAxis) (l : List (Fin m))
    (x : P04MultiArray axis) :
    p04MultiNorm2 (p04AxisListExact axis l x) =
      p04AxisListScale axis l * p04MultiNorm2 x := by
  induction l using List.reverseRecOn with
  | nil => simp [p04AxisListExact, p04AxisListScale]
  | append_singleton l i ih =>
      rw [p04AxisListExact_append, p04_coordinate_norm_scaling,
        ih, p04AxisListScale_append]
      ring

private theorem p04AxisList_error {m : ℕ}
    (axis : Fin m → P04FftAxis) (γ : ℝ) (hγ : 0 ≤ γ)
    (l : List (Fin m)) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (model : P04WilkinsonModel), model.gamma = γ →
        model.epsilon ≤ 1 → ∀ (x : P04MultiArray axis),
        p04MultiNorm2 (fun index =>
          p04AxisListRounded axis model l x index -
            p04AxisListExact axis l x index) ≤
          (p04AxisListScale axis l * p04AxisListCoeff axis l γ * model.epsilon +
            D * model.epsilon ^ 2) * p04MultiNorm2 x := by
  induction l using List.reverseRecOn with
  | nil =>
      refine ⟨0, le_refl 0, ?_⟩
      intro model hmodel hε x
      simp [p04AxisListRounded, p04AxisListExact,
        p04AxisListCoeff, p04AxisListScale,
        p04MultiNorm2_eq_sqrtSum]
  | append_singleton l i ih =>
      obtain ⟨Dp, hDp, hprevAll⟩ := ih
      obtain ⟨Ds, hDs, hstageAll⟩ := p04_coordinate_norm_error axis i γ hγ
      let P := p04AxisListScale axis l
      let S := Real.sqrt ((axis i).order : ℝ)
      let K := p04AxisListCoeff axis l γ
      let a := p04AxisK (axis i) γ
      let D := Ds * P + S * Dp + (S * a + Ds) * (P * K + Dp)
      have hP : 0 ≤ P := p04AxisListScale_nonneg axis l
      have hS : 0 ≤ S := Real.sqrt_nonneg _
      have hK : 0 ≤ K := p04AxisListCoeff_nonneg axis l γ hγ
      have ha : 0 ≤ a := p04AxisK_nonneg (axis i) γ hγ
      have hD : 0 ≤ D := by
        dsimp [D]
        positivity
      refine ⟨D, hD, ?_⟩
      intro model hmodel hε x
      let E := model.epsilon
      let cPrev := P * K * E + Dp * E ^ 2
      let cLoc := S * a * E + Ds * E ^ 2
      let rp := p04AxisListRounded axis model l x
      let ep := p04AxisListExact axis l x
      let ePrev : P04MultiArray axis := fun index => rp index - ep index
      let eLoc : P04MultiArray axis := fun index =>
        p04RoundedCoordinateTransform axis i model rp index -
          p04CoordinateTransform axis i rp index
      let eFinal : P04MultiArray axis := fun index =>
        p04AxisListRounded axis model (l ++ [i]) x index -
          p04AxisListExact axis (l ++ [i]) x index
      have hcLoc : 0 ≤ cLoc := by
        dsimp [cLoc]
        exact add_nonneg
          (mul_nonneg (mul_nonneg hS ha) (le_of_lt model.epsilon_pos))
          (mul_nonneg hDs (sq_nonneg _))
      have hprev : p04MultiNorm2 ePrev ≤
          cPrev * p04MultiNorm2 x := by
        have h := hprevAll model hmodel hε x
        convert h using 1
      have hepnorm : p04MultiNorm2 ep = P * p04MultiNorm2 x :=
        p04AxisListExact_norm_scaling axis l x
      have hrp : p04MultiNorm2 rp ≤
          (P + cPrev) * p04MultiNorm2 x := by
        have htri := p04MultiNorm2_add_le ePrev ep
        have heq : (fun index => ePrev index + ep index) = rp := by
          funext index
          dsimp [ePrev]
          ring
        rw [heq, hepnorm] at htri
        nlinarith [hprev]
      have hloc : p04MultiNorm2 eLoc ≤
          cLoc * p04MultiNorm2 rp := by
        have h := hstageAll model hmodel hε rp
        convert h using 1
      have hdecomp : eFinal =
          fun index => eLoc index + p04CoordinateTransform axis i ePrev index := by
        funext index
        rw [p04_coordinate_sub axis i rp ep]
        simp [eFinal, eLoc, ePrev, rp, ep,
          p04AxisListRounded_append, p04AxisListExact_append]
      have htri : p04MultiNorm2 eFinal ≤
          p04MultiNorm2 eLoc + S * p04MultiNorm2 ePrev := by
        rw [hdecomp]
        have h := p04MultiNorm2_add_le eLoc
          (p04CoordinateTransform axis i ePrev)
        rw [p04_coordinate_norm_scaling] at h
        exact h
      have hnormx : 0 ≤ p04MultiNorm2 x := by
        exact p04MultiNorm2_nonneg x
      have hraw : p04MultiNorm2 eFinal ≤
          (cLoc * (P + cPrev) + S * cPrev) * p04MultiNorm2 x := by
        have hmul := mul_le_mul_of_nonneg_left hrp hcLoc
        have hprev' := mul_le_mul_of_nonneg_left hprev hS
        nlinarith [htri, hloc]
      have hcoef := p04_compose_scaled_coeff E P S K a Dp Ds
        (le_of_lt model.epsilon_pos) hε hP hS hK ha hDp hDs
      have hgoal : p04MultiNorm2 eFinal ≤
          ((P * S) * (K + a) * E + D * E ^ 2) *
            p04MultiNorm2 x := by
        apply hraw.trans
        apply mul_le_mul_of_nonneg_right _ hnormx
        simpa [cLoc, cPrev, D] using hcoef
      convert hgoal using 1
      simp only [p04AxisListScale_append, p04AxisListCoeff_append]
      dsimp [P, S, K, a, E]

private theorem p04_foldr_ofFn {n : ℕ} {α β : Type*}
    (f : Fin n → α) (g : α → β → β) (x : β) :
    (List.ofFn f).foldr g x =
      Fin.foldr n (fun i state => g (f i) state) x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.foldr_cons, Fin.foldr_succ]
      exact congrArg (g (f 0)) (ih (fun i => f i.succ))

private theorem p04_exact_prefix_foldr {m : ℕ}
    (axis : Fin m → P04FftAxis) (k : ℕ) (hk : k ≤ m)
    (x : P04MultiArray axis) :
    p04ApplyCoordinatePrefix axis k x =
      Fin.foldr k
        (fun j state => p04CoordinateTransform axis (Fin.castLE hk j) state) x := by
  induction k generalizing x with
  | zero => simp [p04ApplyCoordinatePrefix]
  | succ k ih =>
      have hk' : k ≤ m := by omega
      have hkt : k < m := by omega
      have hfun :
          (fun j : Fin k =>
            p04CoordinateTransform axis (Fin.castLE hk j.castSucc)) =
          (fun j : Fin k =>
            p04CoordinateTransform axis (Fin.castLE hk' j)) := by
        funext j
        congr 1
      have hlast : Fin.castLE hk (Fin.last k) = (⟨k, hkt⟩ : Fin m) := by
        ext
        rfl
      rw [p04ApplyCoordinatePrefix, Fin.foldr_succ_last]
      simp only [hfun, hlast]
      simpa [p04CoordinateTransformNat, hkt] using
        ih hk' (p04CoordinateTransform axis ⟨k, hkt⟩ x)

private theorem p04AxisListExact_full {m : ℕ}
    (axis : Fin m → P04FftAxis) (x : P04MultiArray axis) :
    p04AxisListExact axis (List.ofFn (fun i : Fin m => i)).reverse x =
      p04ApplyCoordinatePrefix axis m x := by
  unfold p04AxisListExact
  rw [List.foldl_reverse, p04_foldr_ofFn]
  simpa using (p04_exact_prefix_foldr axis m (Nat.le_refl m) x).symm

private def p04SuffixAxis (m k : ℕ) (hk : k ≤ m)
    (j : Fin k) : Fin m :=
  ⟨m - k + j.val, by omega⟩

private theorem p04_run_foldr_suffix {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model)
    (k : ℕ) (hk : k ≤ m) :
    run.computedState ⟨m - k, by omega⟩ =
      Fin.foldr k (fun j state =>
        p04RoundedCoordinateTransform plan.axis
          (p04SuffixAxis m k hk j) model state) run.input := by
  induction k with
  | zero =>
      simpa using run.computed_input
  | succ k ih =>
      have hk' : k ≤ m := by omega
      let i := p04SuffixAxis m (k + 1) hk (0 : Fin (k + 1))
      have hic : i.castSucc = (⟨m - (k + 1), by omega⟩ : Fin (m + 1)) := by
        ext
        rfl
      have hi : i.succ = (⟨m - k, by omega⟩ : Fin (m + 1)) := by
        ext
        dsimp [i, p04SuffixAxis]
        omega
      have hstep : run.computedState ⟨m - (k + 1), by omega⟩ =
          p04RoundedCoordinateTransform plan.axis i model
            (run.computedState ⟨m - k, by omega⟩) := by
        simpa only [hic, hi] using run.stage_step i
      have htail :
          (fun j : Fin k => p04RoundedCoordinateTransform plan.axis
            (p04SuffixAxis m (k + 1) hk j.succ) model) =
          (fun j : Fin k => p04RoundedCoordinateTransform plan.axis
            (p04SuffixAxis m k hk' j) model) := by
        funext j
        congr 1
        ext
        dsimp [p04SuffixAxis]
        omega
      rw [Fin.foldr_succ, htail, ← ih hk']
      exact hstep

private theorem p04AxisListRounded_full {m : ℕ} [NeZero m]
    {plan : P04MultidimensionalFftPlan m} {model : P04WilkinsonModel}
    (run : P04MultidimensionalFftRun plan model) :
    p04AxisListRounded plan.axis model
        (List.ofFn (fun i : Fin m => i)).reverse run.input =
      run.computedState 0 := by
  unfold p04AxisListRounded
  rw [List.foldl_reverse, p04_foldr_ofFn]
  have h := p04_run_foldr_suffix run m (Nat.le_refl m)
  simpa [p04SuffixAxis] using h.symm

private theorem p04AxisListScale_full {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    p04AxisListScale axis
        (List.ofFn (fun i : Fin m => i)).reverse =
      Real.sqrt (p04MultiCardinality axis : ℝ) := by
  unfold p04AxisListScale
  simp only [List.map_reverse, List.prod_reverse,
    List.map_ofFn, List.prod_ofFn]
  calc
    (∏ i : Fin m, Real.sqrt ((axis i).order : ℝ)) =
        Real.sqrt (∏ i : Fin m, ((axis i).order : ℝ)) := by
      rw [Real.sqrt_prod]
      intro i _
      positivity
    _ = Real.sqrt (p04MultiCardinality axis : ℝ) := by
      norm_cast

private theorem p04AxisListCoeff_full {m : ℕ}
    (axis : Fin m → P04FftAxis) (γ : ℝ) :
    p04AxisListCoeff axis
        (List.ofFn (fun i : Fin m => i)).reverse γ =
      ∑ i : Fin m, p04AxisK (axis i) γ := by
  simp only [p04AxisListCoeff, List.map_reverse, List.sum_reverse,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply]

private theorem p04MultiCardinality_pos {m : ℕ}
    (axis : Fin m → P04FftAxis) :
    0 < (p04MultiCardinality axis : ℝ) := by
  have h : 0 < p04MultiCardinality axis := by
    unfold p04MultiCardinality
    exact Finset.prod_pos fun i _ => (axis i).order_pos
  exact_mod_cast h


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
  let l : List (Fin m) := (List.ofFn (fun i : Fin m => i)).reverse
  let S : ℝ := Real.sqrt (p04MultiCardinality plan.axis : ℝ)
  let K : ℝ := ∑ i : Fin m, p04AxisK (plan.axis i) γ
  have hS : 0 < S := Real.sqrt_pos.2 (p04MultiCardinality_pos plan.axis)
  obtain ⟨D, hD, hbound⟩ :=
    p04AxisList_error plan.axis γ family.gamma_nonneg l
  have hexact : p04MultiNorm2 (p04FamilyMultiExactOutput family) =
      S * p04MultiNorm2 family.input := by
    calc
      p04MultiNorm2 (p04FamilyMultiExactOutput family) =
          p04MultiNorm2 (p04AxisListExact plan.axis l family.input) := by
        simp [p04FamilyMultiExactOutput, l, p04AxisListExact_full]
      _ = S * p04MultiNorm2 family.input := by
        rw [p04AxisListExact_norm_scaling, p04AxisListScale_full]
  have hexactnorm : 0 < p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
    have h := mul_pos hexactOutput hS
    simpa [p04MultiRms, S, ne_of_gt hS] using h
  have hratio (ε : P04PositiveEpsilon) :
      p04MultiRms (p04FamilyMultiFftRoundoffError family ε) /
          p04MultiRms (p04FamilyMultiExactOutput family) =
        p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) /
          p04MultiNorm2 (p04FamilyMultiExactOutput family) := by
    unfold p04MultiRms
    field_simp [ne_of_gt hS, ne_of_gt hexactnorm, S]
  refine ⟨D / S, div_nonneg hD (le_of_lt hS), 1, by norm_num, ?_⟩
  intro ε hε
  have hεmodel : (family.model ε).epsilon ≤ 1 := by
    simpa [family.model_epsilon ε] using hε
  have herr : p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) ≤
      (S * K * ε.1 + D * ε.1 ^ 2) * p04MultiNorm2 family.input := by
    have h := hbound (family.model ε) (family.model_gamma ε)
      hεmodel family.input
    have hrun := p04AxisListRounded_full (family.run ε)
    rw [family.run_input ε] at hrun
    simpa [p04FamilyMultiFftRoundoffError, p04MultiComputedOutput,
      p04MultiVecSub, p04FamilyMultiExactOutput, l,
      hrun, p04AxisListExact_full, p04AxisListScale_full,
      p04AxisListCoeff_full, family.model_epsilon ε, S, K] using h
  rw [hratio]
  apply (div_le_iff₀ hexactnorm).2
  rw [hexact]
  calc
    p04MultiNorm2 (p04FamilyMultiFftRoundoffError family ε) ≤
        (S * K * ε.1 + D * ε.1 ^ 2) * p04MultiNorm2 family.input := herr
    _ = (ε.1 * K + D / S * ε.1 ^ 2) *
          (S * p04MultiNorm2 family.input) := by
      have hs : S ≠ 0 := ne_of_gt hS
      field_simp [hs]

end VSCLReuse

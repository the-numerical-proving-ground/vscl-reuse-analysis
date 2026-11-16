import VSCLReuse.P08.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatVec
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace VSCLReuse

open scoped BigOperators

private def p08ToFP (fp : StandardFPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := fp.fl_sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := fp.model_sqrt

private theorem p08ToFP_dot (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    roundedDotProduct fp n x y = NumStability.fl_dotProduct (p08ToFP fp) n x y := by
  cases n <;> rfl

private theorem p08ToFP_forward (fp : StandardFPModel) (n : ℕ)
    (L : P08Matrix n) (v : P08Vector n) :
    roundedForwardSub fp n L v =
      NumStability.fl_forwardSub (p08ToFP fp) n L v := by
  have hsteps : ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
      roundedForwardSubSteps fp n L v k hk x =
        NumStability.fl_forwardSub_steps (p08ToFP fp) n L v k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
        intro hk x
        unfold roundedForwardSubSteps NumStability.fl_forwardSub_steps
        exact ih _ _
  exact hsteps n (le_refl n) _

private theorem p08_orthonormal_bridge {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    NumStability.GramSchmidtOrthonormalColumns X := by
  intro j k
  simpa [NumStability.rectangularGram, NumStability.idMatrix] using hX j k

private theorem p08_rect_norm_bridge {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = NumStability.frobNormRect A := rfl

private theorem p08_rank_le_rank_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have h1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hs : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr h1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hs)]

private theorem p08_gamma_valid_parts {p b r : ℕ} (fp : StandardFPModel)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    NumStability.gammaValid (p08ToFP fp) b ∧
    NumStability.gammaValid (p08ToFP fp) r ∧
    NumStability.gammaValid (p08ToFP fp) p := by
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hrs : (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := p08_rank_le_rank_sqrt r
  dsimp [NumStability.gammaValid, p08ToFP]
  constructor
  · nlinarith [mul_nonneg (add_nonneg (mul_nonneg hr0 (Real.sqrt_nonneg (r : ℝ))) hp0)
      fp.u_nonneg]
  constructor
  · nlinarith [mul_nonneg (add_nonneg hb0 hp0) fp.u_nonneg,
      mul_le_mul_of_nonneg_right hrs fp.u_nonneg]
  · nlinarith [mul_nonneg (add_nonneg hb0 (mul_nonneg hr0 (Real.sqrt_nonneg (r : ℝ))))
      fp.u_nonneg]

private theorem p08_lowrank_norm {b r : ℕ} (X Y : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  have h := NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
    X (NumStability.finiteTranspose Y) (p08_orthonormal_bridge X hX)
  simpa [p08FrobNorm, p08RectFrobNorm, p08LowRankMatrix,
    p08RectMatMul, p08RectTranspose, NumStability.rectMatMul,
    NumStability.finiteTranspose, NumStability.frobNormRect_finiteTranspose] using h

private theorem p08_matvec_backward (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : P08Vector n)
    (hn : NumStability.gammaValid (p08ToFP fp) n) :
    ∃ E : P08RectMatrix m n,
      (∀ i j, |E i j| ≤ NumStability.gamma (p08ToFP fp) n * |A i j|) ∧
      p08RectFrobNorm E ≤
        NumStability.gamma (p08ToFP fp) n * p08RectFrobNorm A ∧
      ∀ i, p08RoundedRectMatVec fp A x i =
        ∑ j : Fin n, (A i j + E i j) * x j := by
  obtain ⟨E, hE, hEq⟩ :=
    NumStability.matVec_backward_error (p08ToFP fp) m n A x hn
  refine ⟨E, hE, ?_, ?_⟩
  · simpa [p08_rect_norm_bridge, NumStability.frobNormRect_eq_frobNormFn] using
      (NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        E A (NumStability.gamma_nonneg (p08ToFP fp) hn) hE)
  · intro i
    simpa [p08RoundedRectMatVec, roundedMatVec, NumStability.fl_matVec,
      p08ToFP_dot] using hEq i

private theorem p08_gamma_combine (a b u : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hvalid : (a + b) * u < 1) :
    a * u / (1 - a * u) + b * u / (1 - b * u) +
      (a * u / (1 - a * u)) * (b * u / (1 - b * u)) ≤
      (a + b) * u / (1 - (a + b) * u) := by
  have ha0 : 0 ≤ a * u := mul_nonneg ha hu
  have hb0 : 0 ≤ b * u := mul_nonneg hb hu
  have ha1 : 0 < 1 - a * u := by nlinarith
  have hb1 : 0 < 1 - b * u := by nlinarith
  have hc1 : 0 < 1 - (a + b) * u := by linarith
  have heq : a * u / (1 - a * u) + b * u / (1 - b * u) +
      (a * u / (1 - a * u)) * (b * u / (1 - b * u)) =
      ((a + b) * u - a * u * (b * u)) /
        ((1 - a * u) * (1 - b * u)) := by
    field_simp [ne_of_gt ha1, ne_of_gt hb1]
    have hcancel : (1 - u * b) * (1 - u * b)⁻¹ = 1 := by
      apply mul_inv_cancel₀
      nlinarith
    linear_combination -(u * a) * hcancel
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos ha1 hb1) hc1).mpr
  nlinarith [mul_nonneg ha0 hb0]

private theorem p08_lowrank_backward_raw (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (x : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hb : NumStability.gammaValid (p08ToFP fp) b)
    (hr : NumStability.gammaValid (p08ToFP fp) r) :
    ∃ F : P08Matrix b,
      (∀ α, p08RoundedLowRankMatVec fp X Y x α =
        ∑ β : Fin b, (p08LowRankMatrix X Y α β + F α β) * x β) ∧
      p08FrobNorm F ≤
        (NumStability.gamma (p08ToFP fp) b +
          NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) +
          NumStability.gamma (p08ToFP fp) b *
            (NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ))) *
          p08FrobNorm (p08LowRankMatrix X Y) := by
  let Yt : P08RectMatrix r b := fun k β => Y β k
  let z := p08RoundedRectMatVec fp Yt x
  obtain ⟨EY, hEYentry, hEYnorm, hEYeq⟩ := p08_matvec_backward fp Yt x hb
  obtain ⟨EX, hEXentry, hEXnorm, hEXeq⟩ := p08_matvec_backward fp X z hr
  let B : P08RectMatrix r b := fun k β => Yt k β + EY k β
  let F : P08Matrix b := fun α β =>
    NumStability.rectMatMul X EY α β + NumStability.rectMatMul EX B α β
  have hAF : ∀ α β, p08LowRankMatrix X Y α β + F α β =
      NumStability.rectMatMul (fun α k => X α k + EX α k) B α β := by
    intro α β
    dsimp [p08LowRankMatrix, p08RectMatMul, p08RectTranspose,
      NumStability.rectMatMul, F, B, Yt]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨F, ?_, ?_⟩
  · intro α
    calc
      p08RoundedLowRankMatVec fp X Y x α =
          NumStability.rectMatMulVec (fun α k => X α k + EX α k) z α := by
            simpa [p08RoundedLowRankMatVec, z, NumStability.rectMatMulVec] using
              hEXeq α
      _ = NumStability.rectMatMulVec (fun α k => X α k + EX α k)
          (NumStability.rectMatMulVec B x) α := by
            congr 1
            funext k
            simpa [NumStability.rectMatMulVec, B] using hEYeq k
      _ = NumStability.rectMatMulVec
          (NumStability.rectMatMul (fun α k => X α k + EX α k) B) x α := by
            rw [NumStability.rectMatMulVec_rectMatMul]
      _ = ∑ β : Fin b, (p08LowRankMatrix X Y α β + F α β) * x β := by
            simp only [NumStability.rectMatMulVec, ← hAF]
  · have hXnorm : NumStability.frobNormRect X = Real.sqrt (r : ℝ) :=
      NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
        (p08_orthonormal_bridge X hX)
    have hYtnorm : NumStability.frobNormRect Yt =
        NumStability.frobNormRect Y := by
      simpa [Yt, NumStability.finiteTranspose] using
        (NumStability.frobNormRect_finiteTranspose Y)
    have hEYnorm' : NumStability.frobNormRect EY ≤
        NumStability.gamma (p08ToFP fp) b * NumStability.frobNormRect Y := by
      simpa [p08_rect_norm_bridge, hYtnorm] using hEYnorm
    have hEXnorm' : NumStability.frobNormRect EX ≤
        NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) := by
      simpa [p08_rect_norm_bridge, hXnorm] using hEXnorm
    have hBnorm : NumStability.frobNormRect B ≤
        (1 + NumStability.gamma (p08ToFP fp) b) *
          NumStability.frobNormRect Y := by
      calc
        NumStability.frobNormRect B ≤
            NumStability.frobNormRect Yt + NumStability.frobNormRect EY := by
              simpa [B] using NumStability.frobNormRect_add_le Yt EY
        _ ≤ NumStability.frobNormRect Y +
            NumStability.gamma (p08ToFP fp) b * NumStability.frobNormRect Y := by
              rw [hYtnorm]
              linarith
        _ = _ := by ring
    have hXEY : NumStability.frobNormRect (NumStability.rectMatMul X EY) =
        NumStability.frobNormRect EY :=
      NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
        X EY (p08_orthonormal_bridge X hX)
    have hEXB : NumStability.frobNormRect (NumStability.rectMatMul EX B) ≤
        NumStability.frobNormRect EX * NumStability.frobNormRect B :=
      NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
        EX B (NumStability.frobNormRect_nonneg EX)
        (NumStability.rectOpNorm2Le_of_frobNormRect_le EX le_rfl)
    have hγb : 0 ≤ NumStability.gamma (p08ToFP fp) b :=
      NumStability.gamma_nonneg (p08ToFP fp) hb
    have hγr : 0 ≤ NumStability.gamma (p08ToFP fp) r :=
      NumStability.gamma_nonneg (p08ToFP fp) hr
    have hsmall : NumStability.frobNormRect F ≤
        (NumStability.gamma (p08ToFP fp) b +
          NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) +
          NumStability.gamma (p08ToFP fp) b *
            (NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ))) *
          NumStability.frobNormRect Y := by
      calc
        NumStability.frobNormRect F ≤
            NumStability.frobNormRect (NumStability.rectMatMul X EY) +
              NumStability.frobNormRect (NumStability.rectMatMul EX B) := by
                simpa [F] using NumStability.frobNormRect_add_le
                  (NumStability.rectMatMul X EY) (NumStability.rectMatMul EX B)
        _ ≤ NumStability.frobNormRect EY +
            NumStability.frobNormRect EX * NumStability.frobNormRect B := by
              rw [hXEY]
              gcongr
        _ ≤ NumStability.gamma (p08ToFP fp) b * NumStability.frobNormRect Y +
            (NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ)) *
              ((1 + NumStability.gamma (p08ToFP fp) b) *
                NumStability.frobNormRect Y) := by
              exact add_le_add hEYnorm'
                (mul_le_mul hEXnorm' hBnorm
                  (NumStability.frobNormRect_nonneg B)
                  (mul_nonneg hγr (Real.sqrt_nonneg _)))
        _ = _ := by ring
    calc
      p08FrobNorm F = NumStability.frobNormRect F := rfl
      _ ≤ _ := hsmall
      _ = _ := by rw [p08_lowrank_norm X Y hX]; rfl

private theorem p08_gamma_scale (a s u : ℝ)
    (ha : 0 ≤ a) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hvalid : (a * s) * u < 1) :
    (a * u / (1 - a * u)) * s ≤ (a * s) * u / (1 - (a * s) * u) := by
  have hmono : a * u ≤ (a * s) * u := by
    nlinarith [mul_nonneg (mul_nonneg ha (sub_nonneg.mpr hs)) hu]
  have hnum : 0 ≤ (a * s) * u := mul_nonneg (mul_nonneg ha (by linarith)) hu
  have hdena : 0 < 1 - a * u := by linarith
  have hdenas : 0 < 1 - (a * s) * u := by linarith
  calc
    (a * u / (1 - a * u)) * s =
        ((a * s) * u) / (1 - a * u) := by ring
    _ ≤ ((a * s) * u) / (1 - (a * s) * u) := by
      apply (div_le_div_iff₀ hdena hdenas).mpr
      nlinarith [mul_nonneg hnum (sub_nonneg.mpr hmono)]

private theorem p08_lowrank_backward (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (x : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      (∀ α, p08RoundedLowRankMatVec fp X Y x α =
        ∑ β : Fin b, (p08LowRankMatrix X Y α β + F α β) * x β) ∧
      p08FrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) := by
  have hparts := p08_gamma_valid_parts (p := 0) fp (by simpa using hvalid)
  obtain ⟨F, hFeq, hFnorm⟩ :=
    p08_lowrank_backward_raw fp X Y x hX hparts.1 hparts.2.1
  have hrValid : ((r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1 := by
    have hb0 : (0 : ℝ) ≤ b := by positivity
    nlinarith [mul_nonneg hb0 fp.u_nonneg]
  have hscale : NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
    by_cases hr0 : r = 0
    · simp [hr0, NumStability.gamma, p08GammaReal]
    · have h1 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
      have hs : (1 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr h1
      simpa [NumStability.gamma, p08GammaReal, p08ToFP] using
        (p08_gamma_scale (r : ℝ) (Real.sqrt (r : ℝ)) fp.u
          (by positivity) hs fp.u_nonneg hrValid)
  have hγb0 : 0 ≤ NumStability.gamma (p08ToFP fp) b :=
    NumStability.gamma_nonneg (p08ToFP fp) hparts.1
  have hrawcoef :
      NumStability.gamma (p08ToFP fp) b +
        NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ) +
        NumStability.gamma (p08ToFP fp) b *
          (NumStability.gamma (p08ToFP fp) r * Real.sqrt (r : ℝ)) ≤
      NumStability.gamma (p08ToFP fp) b +
        p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u +
        NumStability.gamma (p08ToFP fp) b *
          p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
    nlinarith [mul_le_mul_of_nonneg_left hscale hγb0]
  have hcombine :
      NumStability.gamma (p08ToFP fp) b +
        p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u +
        NumStability.gamma (p08ToFP fp) b *
          p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u := by
    simpa [NumStability.gamma, p08GammaReal, p08ToFP] using
      (p08_gamma_combine (b : ℝ) ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u
        (by positivity) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        fp.u_nonneg hvalid)
  refine ⟨F, hFeq, ?_⟩
  calc
    p08FrobNorm F ≤ _ := hFnorm
    _ ≤ (NumStability.gamma (p08ToFP fp) b +
          p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u +
          NumStability.gamma (p08ToFP fp) b *
            p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) fp.u) *
          p08FrobNorm (p08LowRankMatrix X Y) :=
        mul_le_mul_of_nonneg_right hrawcoef (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcombine (Real.sqrt_nonneg _)

private theorem p08_forward_backward (fp : StandardFPModel) {b : ℕ}
    (L : P08Matrix b) (v : P08Vector b)
    (hdiag : ∀ α, L α α ≠ 0) (hlower : p08LowerTriangular L)
    (hvalid : (b : ℝ) * fp.u < 1) :
    ∃ F : P08Matrix b,
      (∀ α, ∑ β : Fin b, (L α β + F α β) * roundedForwardSub fp b L v β = v α) ∧
      p08FrobNorm F ≤ p08GammaReal (b : ℝ) fp.u * p08FrobNorm L := by
  obtain ⟨F, hFentry, hFeq⟩ :=
    NumStability.forwardSub_backward_error (p08ToFP fp) b L v
      hdiag hlower hvalid
  refine ⟨F, ?_, ?_⟩
  · intro α
    simpa [p08ToFP_forward] using hFeq α
  · have hnorm := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      F L (NumStability.gamma_nonneg (p08ToFP fp) hvalid) hFentry
    simpa [p08FrobNorm, p08RectFrobNorm,
      NumStability.frobNorm_eq_sqrt_frobNormSq,
      NumStability.frobNormSq, p08GammaReal, NumStability.gamma,
      p08ToFP] using hnorm

private theorem p08_gamma_mono_real (a b u : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u) (hb : b * u < 1) :
    p08GammaReal a u ≤ p08GammaReal b u := by
  have hbu : 0 ≤ b * u := mul_nonneg (le_trans ha hab) hu
  have hau : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
  have hda : 0 < 1 - a * u := by linarith
  have hdb : 0 < 1 - b * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith

private theorem p08_frob_le_const {m n : ℕ}
    (A B : P08RectMatrix m n) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p08RectFrobNorm A ≤ c * p08RectFrobNorm B := by
  have h' := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    A B hc h
  simpa [p08RectFrobNorm, NumStability.frobNorm_eq_sqrt_frobNormSq,
    NumStability.frobNormSq] using h'

private theorem p08_frob_add_le {m n : ℕ}
    (A B : P08RectMatrix m n) :
    p08RectFrobNorm (fun i j => A i j + B i j) ≤
      p08RectFrobNorm A + p08RectFrobNorm B := by
  simpa [p08RectFrobNorm, NumStability.frobNormRect] using
    NumStability.frobNormRect_add_le A B

private theorem p08_sub_fold_backward (fp : StandardFPModel) {m p : ℕ}
    (hm : m ≤ p) (hp : NumStability.gammaValid (p08ToFP fp) p)
    (t : Fin m → ℝ) (c : ℝ) :
    ∃ Θ : ℝ, ∃ θ : Fin m → ℝ,
      |Θ| ≤ p08GammaReal (p : ℝ) fp.u ∧
      (∀ j, |θ j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      Fin.foldl m (fun acc j => fp.fl_sub acc (t j)) c =
        c * (1 + Θ) - ∑ j : Fin m, t j * (1 + θ j) := by
  let g := p08ToFP fp
  have hmvalid : NumStability.gammaValid g m :=
    NumStability.gammaValid_mono g hm hp
  obtain ⟨Θ, θ, hΘ, hθ, heq⟩ :=
    NumStability.fl_sub_sum_error_init g m t c hmvalid
  have hmono : NumStability.gamma g m ≤ NumStability.gamma g p :=
    NumStability.gamma_mono g hm hp
  refine ⟨Θ, θ, ?_, ?_, ?_⟩
  · exact le_trans hΘ (by simpa [g, p08ToFP, p08GammaReal,
      NumStability.gamma] using hmono)
  · intro j
    exact le_trans (hθ j) (by simpa [g, p08ToFP, p08GammaReal,
      NumStability.gamma] using hmono)
  · simpa [g, p08ToFP] using heq

private theorem p08_row_scaled_error {b : ℕ}
    (A F : P08Matrix b) (θ : Fin b → ℝ)
    {gA gθ g : ℝ} (_hgA : 0 ≤ gA) (hgθ : 0 ≤ gθ)
    (hθ : ∀ α, |θ α| ≤ gθ)
    (hF : p08FrobNorm F ≤ gA * p08FrobNorm A)
    (hcoef : gθ + gA + gθ * gA ≤ g) :
    p08FrobNorm (fun α β => θ α * A α β + (1 + θ α) * F α β) ≤
      g * p08FrobNorm A := by
  let U : P08Matrix b := fun α β => θ α * A α β
  let V : P08Matrix b := fun α β => (1 + θ α) * F α β
  have hU : p08FrobNorm U ≤ gθ * p08FrobNorm A := by
    apply p08_frob_le_const U A hgθ
    intro α β
    simpa [U, abs_mul] using
      (mul_le_mul_of_nonneg_right (hθ α) (abs_nonneg (A α β)))
  have hV : p08FrobNorm V ≤ (1 + gθ) * p08FrobNorm F := by
    apply p08_frob_le_const V F (by linarith)
    intro α β
    have hθ1 : |1 + θ α| ≤ 1 + gθ := by
      calc
        |1 + θ α| ≤ |(1 : ℝ)| + |θ α| := abs_add_le _ _
        _ ≤ 1 + gθ := by simpa using add_le_add_left (hθ α) 1
    simpa [V, abs_mul] using
      (mul_le_mul_of_nonneg_right hθ1 (abs_nonneg (F α β)))
  have hA0 : 0 ≤ p08FrobNorm A := Real.sqrt_nonneg _
  calc
    p08FrobNorm (fun α β => θ α * A α β + (1 + θ α) * F α β) ≤
        p08FrobNorm U + p08FrobNorm V := by
          simpa [p08FrobNorm, U, V] using p08_frob_add_le U V
    _ ≤ gθ * p08FrobNorm A + (1 + gθ) * p08FrobNorm F := by
      linarith
    _ ≤ (gθ + gA + gθ * gA) * p08FrobNorm A := by
      nlinarith [mul_le_mul_of_nonneg_left hF (by linarith : 0 ≤ 1 + gθ)]
    _ ≤ g * p08FrobNorm A := mul_le_mul_of_nonneg_right hcoef hA0

private theorem p08_frob_sq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A ^ 2 = ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
  unfold p08RectFrobNorm
  rw [Real.sq_sqrt (by positivity)]

private theorem p08_block_frob_le_const {p b : ℕ}
    (A B : P08BlockMatrix p b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, p08FrobNorm (A i j) ≤ c * p08FrobNorm (B i j)) :
    p08BlockFrobNorm A ≤ c * p08BlockFrobNorm B := by
  have hblock : ∀ i j, (∑ α : Fin b, ∑ β : Fin b, A i j α β ^ 2) ≤
      c ^ 2 * (∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2) := by
    intro i j
    have h1 : 0 ≤ p08FrobNorm (A i j) := Real.sqrt_nonneg _
    have h2 : 0 ≤ c * p08FrobNorm (B i j) :=
      mul_nonneg hc (Real.sqrt_nonneg _)
    have hsq : p08FrobNorm (A i j) ^ 2 ≤
        (c * p08FrobNorm (B i j)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr (h i j)) (add_nonneg h1 h2)]
    simpa [p08FrobNorm, mul_pow, p08_frob_sq] using hsq
  have htotal :
      (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, A i j α β ^ 2) ≤
      c ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2) := by
    calc
      (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, A i j α β ^ 2) ≤
          ∑ i : Fin p, ∑ j : Fin p,
            c ^ 2 * (∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact hblock i j
      _ = c ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2) := by
            simp_rw [Finset.mul_sum]
  unfold p08BlockFrobNorm
  calc
    Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, A i j α β ^ 2) ≤
        Real.sqrt (c ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2)) :=
      Real.sqrt_le_sqrt htotal
    _ = c * Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, B i j α β ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hc]

private theorem p08_fold_apply (fp : StandardFPModel) (b m : ℕ)
    (v : Fin b → ℝ) (w : Fin m → Fin b → ℝ) (α : Fin b) :
    (Fin.foldl m
      (fun acc j => fun β => fp.fl_sub (acc β) (w j β)) v) α =
      Fin.foldl m (fun acc j => fp.fl_sub acc (w j α)) (v α) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      change fp.fl_sub
        ((Fin.foldl m
          (fun acc j => fun β => fp.fl_sub (acc β) (w j.castSucc β)) v) α)
        (w (Fin.last m) α) =
        fp.fl_sub
          (Fin.foldl m (fun acc j => fp.fl_sub acc (w j.castSucc α)) (v α))
          (w (Fin.last m) α)
      rw [ih v (fun j => w j.castSucc)]

private theorem p08_sum_lt {p : ℕ} (i : Fin p) (f : Fin p → ℝ) :
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) =
      ∑ j ∈ (Finset.univ.filter (fun j : Fin p => j < i)), f j := by
  let e : Fin i.val ≃ {j : Fin p // j < i} := {
    toFun := fun (j : Fin i.val) =>
      ⟨(⟨j.val, by omega⟩ : Fin p), (by exact j.isLt)⟩
    invFun := fun (j : {j : Fin p // j < i}) => (⟨j.1.val, j.2⟩ : Fin i.val)
    left_inv := by intro j; ext; rfl
    right_inv := by intro j; ext; rfl
  }
  calc
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) =
        ∑ j : {j : Fin p // j < i}, f j.1 :=
      Fintype.sum_equiv e _ _ (by intro j; rfl)
    _ = ∑ j ∈ (Finset.univ.filter (fun j : Fin p => j < i)), f j := by
      symm
      apply Finset.sum_subtype
      intro j
      simp

private theorem p08_sum_split {p : ℕ} (i : Fin p) (f : Fin p → ℝ)
    (hzero : ∀ j, i < j → f j = 0) :
    (∑ j : Fin p, f j) = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
  calc
    (∑ j : Fin p, f j) =
        ∑ j : Fin p, ((if j < i then f j else 0) +
          (if j = i then f i else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j < i
        · simp [hji, ne_of_lt hji]
        · by_cases heq : j = i
          · simp [heq]
          · have hij : i < j := by omega
            simp [hji, heq, hzero j hij]
    _ = (∑ j : Fin p, if j < i then f j else 0) + f i := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
      rw [p08_sum_lt]
      simp only [Finset.sum_filter]


set_option maxHeartbeats 2000000 in
/-- P08-C3: complete Theorem 4.4 for a triangular BLR block system. -/
theorem p08_c3_blr_triangular_backward_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b)
    (trace : P08BLRTrace fp T X Y v)
    (hp : 0 < p) (hb : 0 < b)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hupper : ∀ i j : Fin p, i < j → T i j = 0)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    let x := trace.x
    let c := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)
    ∃ DT : P08BlockMatrix p b, ∃ dv : P08BlockVector p b,
      Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
          (p08AssembleVector x) =
        p08AssembleVector v + p08AssembleVector dv ∧
      p08BlockFrobNorm DT ≤
        p08GammaReal c fp.u * p08BlockFrobNorm T ∧
      p08BlockVecNorm dv ≤
        p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
  -- PROOF_START P08-C3-H001
  classical
  dsimp
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let c : ℝ := d + (p : ℝ)
  have hdvalid : d * fp.u < 1 := by
    have hp0 : (0 : ℝ) ≤ p := by positivity
    dsimp [c, d] at hvalid ⊢
    nlinarith [mul_nonneg hp0 fp.u_nonneg]
  have hparts := p08_gamma_valid_parts fp hvalid
  have hΓb0 : 0 ≤ p08GammaReal (b : ℝ) fp.u := by
    simpa [p08GammaReal, NumStability.gamma, p08ToFP] using
      (NumStability.gamma_nonneg (p08ToFP fp) hparts.1)
  have hΓp0 : 0 ≤ p08GammaReal (p : ℝ) fp.u := by
    simpa [p08GammaReal, NumStability.gamma, p08ToFP] using
      (NumStability.gamma_nonneg (p08ToFP fp) hparts.2.2)
  have hΓd0 : 0 ≤ p08GammaReal d fp.u := by
    unfold p08GammaReal
    exact div_nonneg (mul_nonneg (by dsimp [d]; positivity) fp.u_nonneg)
      (by linarith)
  have hΓc0 : 0 ≤ p08GammaReal c fp.u := by
    unfold p08GammaReal
    exact div_nonneg (mul_nonneg (by dsimp [c, d]; positivity) fp.u_nonneg)
      (by have hcvalid : c * fp.u < 1 := by simpa [c, d] using hvalid
          linarith)
  have hΓoff : p08GammaReal (p : ℝ) fp.u + p08GammaReal d fp.u +
      p08GammaReal (p : ℝ) fp.u * p08GammaReal d fp.u ≤
      p08GammaReal c fp.u := by
    have h := p08_gamma_combine (p : ℝ) d fp.u
      (by positivity) (by dsimp [d]; positivity) fp.u_nonneg
      (by simpa [c, add_comm, add_left_comm, add_assoc] using hvalid)
    simpa [p08GammaReal, c, add_comm, add_left_comm, add_assoc] using h
  have hΓdiag : p08GammaReal (b : ℝ) fp.u ≤ p08GammaReal c fp.u := by
    apply p08_gamma_mono_real (b : ℝ) c fp.u (by positivity)
    · have hrs : (0 : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
      have hp0 : (0 : ℝ) ≤ p := by positivity
      dsimp [c, d]
      linarith
    · exact fp.u_nonneg
    · simpa [c, d] using hvalid
  let offCert : ∀ i j : Fin p, j < i →
      ∃ F : P08Matrix b,
        (∀ α, p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) α =
          ∑ β : Fin b, (T i j α β + F α β) * trace.x j β) ∧
        p08FrobNorm F ≤ p08GammaReal d fp.u * p08FrobNorm (T i j) := by
    intro i j hij
    have h := p08_lowrank_backward fp (X i j) (Y i j) (trace.x j)
      (hX i j hij) (by simpa [d] using hdvalid)
    simpa [hlr i j hij, d] using h
  let Foff : P08BlockMatrix p b := fun i j =>
    if hij : j < i then Classical.choose (offCert i j hij) else 0
  have hFoffEq : ∀ i j : Fin p, ∀ hij : j < i, ∀ α,
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (trace.x j) α =
        ∑ β : Fin b, (T i j α β + Foff i j α β) * trace.x j β := by
    intro i j hij α
    simpa [Foff, hij] using (Classical.choose_spec (offCert i j hij)).1 α
  have hFoffNorm : ∀ i j : Fin p, ∀ hij : j < i,
      p08FrobNorm (Foff i j) ≤
        p08GammaReal d fp.u * p08FrobNorm (T i j) := by
    intro i j hij
    simpa [Foff, hij] using (Classical.choose_spec (offCert i j hij)).2
  let diagCert : ∀ i : Fin p, ∃ F : P08Matrix b,
      (∀ α, ∑ β : Fin b, (T i i α β + F α β) * trace.x i β =
        trace.rhs i α) ∧
      p08FrobNorm F ≤ p08GammaReal (b : ℝ) fp.u * p08FrobNorm (T i i) := by
    intro i
    obtain ⟨F, hEq, hNorm⟩ := p08_forward_backward fp (T i i) (trace.rhs i)
      (hdiag i) (hlower i) hparts.1
    refine ⟨F, ?_, hNorm⟩
    intro α
    simpa [trace.x_eq i] using hEq α
  let Fdiag : Fin p → P08Matrix b := fun i => Classical.choose (diagCert i)
  have hFdiagEq : ∀ i α, ∑ β : Fin b,
      (T i i α β + Fdiag i α β) * trace.x i β = trace.rhs i α := by
    intro i α
    exact (Classical.choose_spec (diagCert i)).1 α
  have hFdiagNorm : ∀ i, p08FrobNorm (Fdiag i) ≤
      p08GammaReal (b : ℝ) fp.u * p08FrobNorm (T i i) := by
    intro i
    exact (Classical.choose_spec (diagCert i)).2
  let w (i : Fin p) (j : Fin i.val) (α : Fin b) : ℝ :=
    p08RoundedLowRankMatVec fp
      (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
      (trace.x ⟨j.val, by omega⟩) α
  let foldCert : ∀ i : Fin p, ∀ α : Fin b,
      ∃ Θ : ℝ, ∃ θ : Fin i.val → ℝ,
        |Θ| ≤ p08GammaReal (p : ℝ) fp.u ∧
        (∀ j, |θ j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
        trace.rhs i α = v i α * (1 + Θ) -
          ∑ j : Fin i.val, w i j α * (1 + θ j) := by
    intro i α
    obtain ⟨Θ, θ, hΘ, hθ, heq⟩ :=
      p08_sub_fold_backward fp (Nat.le_of_lt i.isLt) hparts.2.2
        (fun j => w i j α) (v i α)
    refine ⟨Θ, θ, hΘ, hθ, ?_⟩
    have hrhs := congrFun (trace.rhs_eq i) α
    rw [p08_fold_apply] at hrhs
    simpa [w] using hrhs.trans heq
  let Θ : Fin p → Fin b → ℝ := fun i α => Classical.choose (foldCert i α)
  let θ : ∀ i : Fin p, Fin b → Fin i.val → ℝ := fun i α =>
    Classical.choose (Classical.choose_spec (foldCert i α))
  have hfoldSpecs : ∀ i α,
      |Θ i α| ≤ p08GammaReal (p : ℝ) fp.u ∧
      (∀ j, |θ i α j| ≤ p08GammaReal (p : ℝ) fp.u) ∧
      trace.rhs i α = v i α * (1 + Θ i α) -
        ∑ j : Fin i.val, w i j α * (1 + θ i α j) := by
    intro i α
    exact Classical.choose_spec (Classical.choose_spec (foldCert i α))
  let DT : P08BlockMatrix p b := fun i j =>
    if hij : j < i then
      fun α β =>
        θ i α ⟨j.val, hij⟩ * T i j α β +
          (1 + θ i α ⟨j.val, hij⟩) * Foff i j α β
    else if j = i then Fdiag i else 0
  let dv : P08BlockVector p b := fun i α => v i α * Θ i α
  have hDT_off : ∀ i j : Fin p, ∀ hij : j < i, ∀ α β,
      DT i j α β = θ i α ⟨j.val, hij⟩ * T i j α β +
        (1 + θ i α ⟨j.val, hij⟩) * Foff i j α β := by
    intro i j hij α β
    simp [DT, hij]
  have hDT_diag : ∀ i : Fin p, DT i i = Fdiag i := by
    intro i
    simp [DT]
  have hDT_upper : ∀ i j : Fin p, i < j → DT i j = 0 := by
    intro i j hij
    simp [DT, (not_lt.mpr (le_of_lt hij)), ne_of_gt hij]
  have hDTblock : ∀ i j : Fin p,
      p08FrobNorm (DT i j) ≤ p08GammaReal c fp.u * p08FrobNorm (T i j) := by
    intro i j
    rcases lt_trichotomy j i with hji | heq | hij
    · have hscaled := p08_row_scaled_error (T i j) (Foff i j)
        (fun α => θ i α ⟨j.val, hji⟩) hΓd0 hΓp0
        (fun α => (hfoldSpecs i α).2.1 ⟨j.val, hji⟩)
        (hFoffNorm i j hji) hΓoff
      have hDTeq : DT i j = fun α β =>
          θ i α ⟨j.val, hji⟩ * T i j α β +
            (1 + θ i α ⟨j.val, hji⟩) * Foff i j α β := by
        funext α β
        exact hDT_off i j hji α β
      rw [hDTeq]
      exact hscaled
    · subst j
      calc
        p08FrobNorm (DT i i) = p08FrobNorm (Fdiag i) := by rw [hDT_diag]
        _ ≤ p08GammaReal (b : ℝ) fp.u * p08FrobNorm (T i i) :=
          hFdiagNorm i
        _ ≤ p08GammaReal c fp.u * p08FrobNorm (T i i) :=
          mul_le_mul_of_nonneg_right hΓdiag (Real.sqrt_nonneg _)
    · have hTzero := hupper i j hij
      have hDzero := hDT_upper i j hij
      simp [hTzero, hDzero, p08FrobNorm, p08RectFrobNorm]
  have hDTnorm : p08BlockFrobNorm DT ≤
      p08GammaReal c fp.u * p08BlockFrobNorm T :=
    p08_block_frob_le_const DT T hΓc0 hDTblock
  have hDVnorm : p08BlockVecNorm dv ≤
      p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
    change p08RectFrobNorm dv ≤
      p08GammaReal (p : ℝ) fp.u * p08RectFrobNorm v
    apply p08_frob_le_const dv v hΓp0
    intro i α
    change |v i α * Θ i α| ≤
      p08GammaReal (p : ℝ) fp.u * |v i α|
    rw [abs_mul]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left (hfoldSpecs i α).1 (abs_nonneg (v i α)))
  have hOffRow : ∀ i : Fin p, ∀ j : Fin i.val, ∀ α : Fin b,
      w i j α * (1 + θ i α j) =
        ∑ β : Fin b,
          (T i ⟨j.val, by omega⟩ α β + DT i ⟨j.val, by omega⟩ α β) *
            trace.x ⟨j.val, by omega⟩ β := by
    intro i j α
    let j' : Fin p := ⟨j.val, by omega⟩
    have hij : j' < i := j.isLt
    change p08RoundedLowRankMatVec fp (X i j') (Y i j')
      (trace.x j') α * (1 + θ i α j) =
        ∑ β : Fin b, (T i j' α β + DT i j' α β) * trace.x j' β
    rw [hFoffEq i j' hij α, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β _
    rw [hDT_off i j' hij α β]
    have hθeq : (⟨j'.val, hij⟩ : Fin i.val) = j := by ext; rfl
    rw [hθeq]
    ring
  have hrow : ∀ i : Fin p, ∀ α : Fin b,
      (∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DT i j α β) * trace.x j β) =
        v i α + dv i α := by
    intro i α
    have hsplit := p08_sum_split i
      (fun j : Fin p => ∑ β : Fin b,
        (T i j α β + DT i j α β) * trace.x j β) (by
          intro j hij
          change (∑ β : Fin b,
            (T i j α β + DT i j α β) * trace.x j β) = 0
          rw [hupper i j hij, hDT_upper i j hij]
          simp)
    have hlow : (∑ j : Fin i.val, ∑ β : Fin b,
        (T i ⟨j.val, by omega⟩ α β +
          DT i ⟨j.val, by omega⟩ α β) *
          trace.x ⟨j.val, by omega⟩ β) =
        ∑ j : Fin i.val, w i j α * (1 + θ i α j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hOffRow i j α).symm
    calc
      (∑ j : Fin p, ∑ β : Fin b,
          (T i j α β + DT i j α β) * trace.x j β) =
          (∑ j : Fin i.val, w i j α * (1 + θ i α j)) +
            trace.rhs i α := by
        rw [hsplit, hlow]
        change (∑ j : Fin i.val, w i j α * (1 + θ i α j)) +
          (∑ β : Fin b, (T i i α β + DT i i α β) * trace.x i β) =
            (∑ j : Fin i.val, w i j α * (1 + θ i α j)) + trace.rhs i α
        rw [hDT_diag, hFdiagEq]
      _ = v i α + dv i α := by
        rw [(hfoldSpecs i α).2.2]
        simp [dv]
        ring
  have hEq : Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
      (p08AssembleVector trace.x) =
        p08AssembleVector v + p08AssembleVector dv := by
    funext q
    rcases q with ⟨i, α⟩
    change (∑ q : Fin p × Fin b,
      (T i q.1 α q.2 + DT i q.1 α q.2) * trace.x q.1 q.2) =
        v i α + dv i α
    rw [Fintype.sum_prod_type]
    exact hrow i α
  refine ⟨DT, dv, hEq, ?_, hDVnorm⟩
  simpa [c, d] using hDTnorm

end VSCLReuse

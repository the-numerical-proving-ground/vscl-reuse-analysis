import VSCLReuse.P08.Definitions
import NumStability.Algorithms.MatVec
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace VSCLReuse
open scoped Matrix.Norms.Frobenius BigOperators

private def p08FP (fp : StandardFPModel) : NumStability.FPModel where
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

private lemma p08_stage {m n : ℕ} (fp : StandardFPModel)
    (B : P08RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ Δ : P08RectMatrix m n,
      (∀ i j, |Δ i j| ≤ p08GammaReal (n : ℝ) fp.u * |B i j|) ∧
      p08RoundedRectMatVec fp B x = p08RectMatVec (p08RectAdd B Δ) x := by
  obtain ⟨Δ, hΔ, heq⟩ :=
    NumStability.matVec_backward_error (p08FP fp) m n B x hvalid
  refine ⟨Δ, ?_, ?_⟩
  · intro i j
    simpa only [NumStability.gamma, p08GammaReal, p08FP] using hΔ i j
  · funext i
    simpa only [p08RoundedRectMatVec, roundedMatVec,
      p08RectMatVec, p08RectAdd, NumStability.fl_matVec,
      NumStability.fl_dotProduct, roundedDotProduct, p08FP] using heq i

private lemma p08_norm_entry_bound {m n : ℕ}
    (B Δ : P08RectMatrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |Δ i j| ≤ c * |B i j|) :
    p08RectFrobNorm Δ ≤ c * p08RectFrobNorm B := by
  simpa only [← NumStability.frobNormRect_eq_frobNormFn,
    p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      Δ B hc h

private lemma p08_norm_mul {m n p : ℕ}
    (B : P08RectMatrix m n) (C : P08RectMatrix n p) :
    p08RectFrobNorm (p08RectMatMul B C) ≤
      p08RectFrobNorm B * p08RectFrobNorm C := by
  simpa only [p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect, p08RectMatMul,
    NumStability.rectMatMul] using
    NumStability.frobNormRect_rectMatMul_le B C

private lemma p08_norm_add {m n : ℕ}
    (B C : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectAdd B C) ≤
      p08RectFrobNorm B + p08RectFrobNorm C := by
  simpa only [p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect, p08RectAdd] using
    NumStability.frobNormRect_add_le B C

private lemma p08_norm_X {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  have hX' : NumStability.GramSchmidtOrthonormalColumns X := by
    intro j k
    simpa [NumStability.rectangularGram, NumStability.matMulRect,
      NumStability.finiteTranspose, NumStability.idMatrix] using hX j k
  simpa only [p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal hX'

private lemma p08_norm_XY {b r p : ℕ}
    (X : P08RectMatrix b r) (B : P08RectMatrix r p)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X B) = p08RectFrobNorm B := by
  have hX' : NumStability.GramSchmidtOrthonormalColumns X := by
    intro j k
    simpa [NumStability.rectangularGram, NumStability.matMulRect,
      NumStability.finiteTranspose, NumStability.idMatrix] using hX j k
  simpa only [p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect, p08RectMatMul,
    NumStability.rectMatMul] using
    NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
      X B hX'

private lemma p08_gamma_aux (a d t : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hdt : d ≤ t)
    (hsmall : a + t < 1) :
    a / (1 - a) + t / (1 - d) +
      (a / (1 - a)) * (t / (1 - d)) ≤
      (a + t) / (1 - a - t) := by
  have ha1 : 0 < 1 - a := by linarith
  have hd1 : 0 < 1 - d := by linarith
  have hat1 : 0 < 1 - a - t := by linarith
  have hx :
      a / (1 - a) + t / (1 - d) +
          (a / (1 - a)) * (t / (1 - d)) =
        (a - a * d + t) / ((1 - a) * (1 - d)) := by
    field_simp
    ring
  rw [hx]
  apply (div_le_div_iff₀ (mul_pos ha1 hd1) hat1).2
  have h1 : 0 ≤ (a + t) * (t - d) :=
    mul_nonneg (add_nonneg ha (le_trans hd hdt)) (sub_nonneg.mpr hdt)
  have h2 : 0 ≤ a * d := mul_nonneg ha hd
  nlinarith

private lemma p08_gamma_bound (b r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * u < 1) :
    p08GammaReal (b : ℝ) u +
      p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) +
      p08GammaReal (b : ℝ) u *
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ≤
      p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) u := by
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hrs : (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
    by_cases hr : r = 0
    · simp [hr]
    · have hr1 : (1 : ℝ) ≤ r := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hs1 : 1 ≤ Real.sqrt (r : ℝ) := by
        nlinarith [Real.sq_sqrt hr0]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs1)]
  have hdt : (r : ℝ) * u ≤ (r : ℝ) * Real.sqrt (r : ℝ) * u :=
    mul_le_mul_of_nonneg_right hrs hu
  have ha : 0 ≤ (b : ℝ) * u := mul_nonneg hb0 hu
  have hd : 0 ≤ (r : ℝ) * u := mul_nonneg hr0 hu
  have hsmall : (b : ℝ) * u + (r : ℝ) * Real.sqrt (r : ℝ) * u < 1 := by
    nlinarith [hvalid]
  have h := p08_gamma_aux ((b : ℝ) * u) ((r : ℝ) * u)
      ((r : ℝ) * Real.sqrt (r : ℝ) * u) ha hd hdt hsmall
  convert h using 1 <;> simp only [p08GammaReal] <;> ring

private lemma p08_norm_eq_matrix_norm {m n : ℕ}
    (B : P08RectMatrix m n) : p08RectFrobNorm B = ‖B‖ := by
  simpa only [p08RectFrobNorm, NumStability.frobNormRect,
    NumStability.frobNormSqRect] using
    NumStability.frobNormRect_eq_frobNormFn B

private lemma p08_matvec_mul {m n p : ℕ}
    (B : P08RectMatrix m n) (C : P08RectMatrix n p)
    (x : Fin p → ℝ) :
    p08RectMatVec (p08RectMatMul B C) x =
      p08RectMatVec B (p08RectMatVec C x) := by
  funext i
  simp only [p08RectMatVec, p08RectMatMul]
  calc
    (∑ j : Fin p, (∑ k : Fin n, B i k * C k j) * x j) =
        ∑ j : Fin p, ∑ k : Fin n, B i k * (C k j * x j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = ∑ k : Fin n, ∑ j : Fin p, B i k * (C k j * x j) :=
      Finset.sum_comm
    _ = ∑ k : Fin n, B i k * ∑ j : Fin p, C k j * x j := by
      simp_rw [Finset.mul_sum]

/-- Full Lemma 3.1: low-rank matrix-vector backward error and its A-relative bound. -/
theorem p08_c2_full_low_rank_matvec_error
    {b r : ℕ} (fp : StandardFPModel)
    (A : P08Matrix b) (X Y : P08RectMatrix b r) (v : P08Vector b)
    (ε β : ℝ) (hβ : 0 < β)
    (hX : p08OrthonormalColumns X)
    (happrox : p08FrobNorm (A - p08LowRankMatrix X Y) ≤ ε * β)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    let zHat := p08RoundedLowRankMatVec fp X Y v
    ∃ ΔAtilde ΔA : P08Matrix b,
      zHat = p08MatVec (p08RectAdd (p08LowRankMatrix X Y) ΔAtilde) v ∧
      p08FrobNorm ΔAtilde ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) ∧
      zHat = p08MatVec (p08RectAdd A ΔA) v ∧
      p08FrobNorm ΔA ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm A +
        ε * (1 + p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u) * β := by
  -- PROOF_START P08-C2-H001
  let L : P08Matrix b := p08LowRankMatrix X Y
  let wHat : Fin r → ℝ :=
    p08RoundedRectMatVec fp (p08RectTranspose Y) v
  let zHat : P08Vector b := p08RoundedLowRankMatVec fp X Y v
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hrs : (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
    by_cases hr : r = 0
    · simp [hr]
    · have hr1 : (1 : ℝ) ≤ r := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hs1 : 1 ≤ Real.sqrt (r : ℝ) := by
        nlinarith [Real.sq_sqrt hr0]
      nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hs1)]
  have hbvalid : (b : ℝ) * fp.u < 1 := by
    have ht : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) * fp.u :=
      mul_nonneg (mul_nonneg hr0 hs0) fp.u_nonneg
    nlinarith [hvalid]
  have hrvalid : (r : ℝ) * fp.u < 1 := by
    have hd := mul_le_mul_of_nonneg_right hrs fp.u_nonneg
    have ha : 0 ≤ (b : ℝ) * fp.u := mul_nonneg hb0 fp.u_nonneg
    nlinarith [hvalid]
  let gb := p08GammaReal (b : ℝ) fp.u
  let gr := p08GammaReal (r : ℝ) fp.u
  let gc := p08GammaReal
      ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  have hgb : 0 ≤ gb := by
    dsimp [gb, p08GammaReal]
    exact div_nonneg (mul_nonneg hb0 fp.u_nonneg) (by linarith)
  have hgr : 0 ≤ gr := by
    dsimp [gr, p08GammaReal]
    exact div_nonneg (mul_nonneg hr0 fp.u_nonneg) (by linarith)
  have hgc : 0 ≤ gc := by
    dsimp [gc, p08GammaReal]
    apply div_nonneg
    · exact mul_nonneg (add_nonneg hb0 (mul_nonneg hr0 hs0)) fp.u_nonneg
    · nlinarith [hvalid]
  obtain ⟨DY, hDYentry, hw⟩ :=
    p08_stage fp (p08RectTranspose Y) v hbvalid
  obtain ⟨DX, hDXentry, hz⟩ := p08_stage fp X wHat hrvalid
  have hDY : p08RectFrobNorm DY ≤ gb * p08RectFrobNorm (p08RectTranspose Y) :=
    p08_norm_entry_bound _ _ gb hgb hDYentry
  have hDX : p08RectFrobNorm DX ≤ gr * Real.sqrt (r : ℝ) := by
    calc
      p08RectFrobNorm DX ≤ gr * p08RectFrobNorm X :=
        p08_norm_entry_bound _ _ gr hgr hDXentry
      _ = gr * Real.sqrt (r : ℝ) := by rw [p08_norm_X X hX]
  have hL : p08FrobNorm L = p08RectFrobNorm (p08RectTranspose Y) := by
    exact p08_norm_XY X (p08RectTranspose Y) hX
  let T1 : P08Matrix b := p08RectMatMul X DY
  let T2 : P08Matrix b := p08RectMatMul DX (p08RectTranspose Y)
  let T3 : P08Matrix b := p08RectMatMul DX DY
  let D : P08Matrix b := p08RectAdd T1 (p08RectAdd T2 T3)
  have hmat :
      p08RectMatMul (p08RectAdd X DX)
          (p08RectAdd (p08RectTranspose Y) DY) =
        p08RectAdd L D := by
    ext i j
    simp only [p08RectMatMul, p08RectAdd, L, D, T1, T2, T3,
      p08LowRankMatrix]
    simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hzD : zHat = p08MatVec (p08RectAdd L D) v := by
    calc
      zHat = p08RectMatVec (p08RectAdd X DX) wHat := hz
      _ = p08RectMatVec (p08RectAdd X DX)
            (p08RectMatVec (p08RectAdd (p08RectTranspose Y) DY) v) := by
              exact congrArg (p08RectMatVec (p08RectAdd X DX)) hw
      _ = p08RectMatVec
            (p08RectMatMul (p08RectAdd X DX)
              (p08RectAdd (p08RectTranspose Y) DY)) v :=
            (p08_matvec_mul _ _ _).symm
      _ = p08MatVec (p08RectAdd L D) v := by rw [hmat]; rfl
  have hL0 : 0 ≤ p08FrobNorm L := Real.sqrt_nonneg _
  have hDY0 : 0 ≤ p08RectFrobNorm DY := Real.sqrt_nonneg _
  have hDX0 : 0 ≤ p08RectFrobNorm DX := Real.sqrt_nonneg _
  have hY0 : 0 ≤ p08RectFrobNorm (p08RectTranspose Y) := Real.sqrt_nonneg _
  have hT1 : p08FrobNorm T1 ≤ gb * p08FrobNorm L := by
    calc
      p08FrobNorm T1 = p08RectFrobNorm DY :=
        p08_norm_XY X DY hX
      _ ≤ gb * p08RectFrobNorm (p08RectTranspose Y) := hDY
      _ = gb * p08FrobNorm L := by rw [hL]
  have hT2 : p08FrobNorm T2 ≤
      (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L := by
    calc
      p08FrobNorm T2 ≤
          p08RectFrobNorm DX * p08RectFrobNorm (p08RectTranspose Y) :=
        p08_norm_mul _ _
      _ ≤ (gr * Real.sqrt (r : ℝ)) * p08RectFrobNorm
          (p08RectTranspose Y) :=
        mul_le_mul_of_nonneg_right hDX hY0
      _ = (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L := by rw [hL]
  have hT3 : p08FrobNorm T3 ≤
      gb * (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L := by
    calc
      p08FrobNorm T3 ≤ p08RectFrobNorm DX * p08RectFrobNorm DY :=
        p08_norm_mul _ _
      _ ≤ (gr * Real.sqrt (r : ℝ)) *
          (gb * p08RectFrobNorm (p08RectTranspose Y)) := by
        exact mul_le_mul hDX hDY
          hDY0 (mul_nonneg hgr hs0)
      _ = gb * (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L := by
        rw [hL]
        ring
  have hDpre : p08FrobNorm D ≤
      (gb + gr * Real.sqrt (r : ℝ) +
        gb * (gr * Real.sqrt (r : ℝ))) * p08FrobNorm L := by
    calc
      p08FrobNorm D ≤ p08FrobNorm T1 +
          p08FrobNorm (p08RectAdd T2 T3) := p08_norm_add _ _
      _ ≤ p08FrobNorm T1 + p08FrobNorm T2 + p08FrobNorm T3 := by
        have hh := p08_norm_add T2 T3
        change p08FrobNorm (p08RectAdd T2 T3) ≤
          p08FrobNorm T2 + p08FrobNorm T3 at hh
        linarith
      _ ≤ gb * p08FrobNorm L +
          (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L +
          gb * (gr * Real.sqrt (r : ℝ)) * p08FrobNorm L := by
        linarith [hT1, hT2, hT3]
      _ = (gb + gr * Real.sqrt (r : ℝ) +
          gb * (gr * Real.sqrt (r : ℝ))) * p08FrobNorm L := by ring
  have hD : p08FrobNorm D ≤ gc * p08FrobNorm L :=
    le_trans hDpre (mul_le_mul_of_nonneg_right
      (p08_gamma_bound b r fp.u fp.u_nonneg hvalid) hL0)
  let DA : P08Matrix b := L - A + D
  have hzDA : zHat = p08MatVec (p08RectAdd A DA) v := by
    rw [hzD]
    congr 1
    ext i j
    simp only [p08RectAdd, DA, Matrix.add_apply, Matrix.sub_apply]
    ring
  have hdiff : p08FrobNorm (L - A) = p08FrobNorm (A - L) := by
    change p08RectFrobNorm (L - A) = p08RectFrobNorm (A - L)
    rw [p08_norm_eq_matrix_norm, p08_norm_eq_matrix_norm]
    rw [show L - A = -(A - L) by abel, norm_neg]
  have hLbound : p08FrobNorm L ≤ p08FrobNorm A + ε * β := by
    change p08RectFrobNorm L ≤ p08RectFrobNorm A + ε * β
    rw [p08_norm_eq_matrix_norm, p08_norm_eq_matrix_norm]
    calc
      ‖L‖ = ‖A - (A - L)‖ := by congr 1; abel
      _ ≤ ‖A‖ + ‖A - L‖ := norm_sub_le _ _
      _ ≤ ‖A‖ + ε * β := by
        have hh : p08RectFrobNorm (A - L) ≤ ε * β := happrox
        rw [p08_norm_eq_matrix_norm] at hh
        exact add_le_add_right hh _
  have hDA : p08FrobNorm DA ≤
      gc * p08FrobNorm A + ε * (1 + gc) * β := by
    calc
      p08FrobNorm DA ≤ p08FrobNorm (L - A) + p08FrobNorm D := by
        simpa only [DA, p08RectAdd, Matrix.add_apply] using
          p08_norm_add (L - A) D
      _ ≤ ε * β + gc * p08FrobNorm L := by
        rw [hdiff]
        exact add_le_add happrox hD
      _ ≤ ε * β + gc * (p08FrobNorm A + ε * β) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hLbound hgc) _
      _ = gc * p08FrobNorm A + ε * (1 + gc) * β := by ring
  exact ⟨D, DA, hzD, hD, hzDA, hDA⟩

end VSCLReuse

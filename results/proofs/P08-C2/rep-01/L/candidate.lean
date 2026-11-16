import VSCLReuse.P08.Definitions
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt

namespace VSCLReuse

private def p08AsFPModel (fp : StandardFPModel) : NumStability.FPModel where
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

private theorem p08RoundedRectMatVec_eq_fl (fp : StandardFPModel)
    {m n : ℕ} (M : P08RectMatrix m n) (x : Fin n → ℝ) :
    p08RoundedRectMatVec fp M x =
      NumStability.fl_matVec (p08AsFPModel fp) m n M x := by
  rfl

private theorem p08FrobNorm_eq_frobNormRect {m n : ℕ}
    (M : P08RectMatrix m n) :
    p08RectFrobNorm M = NumStability.frobNormRect M := by
  rfl

private theorem p08OrthonormalColumns_opNorm {b r : ℕ}
    {X : P08RectMatrix b r} (hX : p08OrthonormalColumns X) :
    NumStability.rectOpNorm2Le X 1 := by
  apply NumStability.GramSchmidtOrthonormalColumns.rectOpNorm2Le_one
  intro j k
  simpa [NumStability.rectangularGram, NumStability.idMatrix,
    p08OrthonormalColumns] using hX j k

private theorem p08OrthonormalColumns_norm {b r : ℕ}
    {X : P08RectMatrix b r} (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  rw [Finset.sum_comm]
  have hj : ∀ j : Fin r, (∑ i : Fin b, X i j ^ 2) = 1 := by
    intro j
    simpa [pow_two] using hX j j
  simp only [hj, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul, mul_one]

private theorem p08OrthonormalColumns_lowRank_norm {b r : ℕ}
    {X Y : P08RectMatrix b r} (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  let XT := NumStability.finiteTranspose X
  let YT := NumStability.finiteTranspose Y
  have hXT_X : NumStability.rectMatMul XT X = NumStability.idMatrix r := by
    ext j k
    simpa [XT, NumStability.rectMatMul, NumStability.finiteTranspose,
      NumStability.idMatrix] using hX j k
  have hrec : NumStability.rectMatMul XT
      (NumStability.rectMatMul X YT) = YT := by
    rw [← NumStability.rectMatMul_assoc, hXT_X,
      NumStability.rectMatMul_id_left]
  have hXop := p08OrthonormalColumns_opNorm hX
  have hXTop := NumStability.rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le
    X (by norm_num : (0 : ℝ) ≤ 1) hXop
  have h1 := NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
    X YT (by norm_num : (0 : ℝ) ≤ 1) hXop
  have h2 := NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
    XT (NumStability.rectMatMul X YT) (by norm_num : (0 : ℝ) ≤ 1) hXTop
  rw [hrec] at h2
  have heq : NumStability.frobNormRect (NumStability.rectMatMul X YT) =
      NumStability.frobNormRect YT := by
    linarith
  rw [NumStability.frobNormRect_finiteTranspose] at heq
  simpa [p08FrobNorm, p08LowRankMatrix, p08RectMatMul,
    p08RectTranspose, p08RectFrobNorm, NumStability.rectMatMul,
    NumStability.frobNormRect, NumStability.frobNormSqRect] using heq

private theorem p08_sqrt_card_ge_one {r : ℕ} (hr : 0 < r) :
    1 ≤ Real.sqrt (r : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 := Real.sqrt_nonneg (r : ℝ)
  have hs2 := Real.sq_sqrt hr0
  nlinarith

private theorem p08_valid_small_indices {b r : ℕ} (fp : StandardFPModel)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    (b : ℝ) * fp.u < 1 ∧ (r : ℝ) * fp.u < 1 := by
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hs0 := Real.sqrt_nonneg (r : ℝ)
  have hrs0 : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := mul_nonneg hr0 hs0
  have hb : (b : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hrs0 fp.u_nonneg]
  constructor
  · exact hb
  · by_cases hr : r = 0
    · subst r
      simpa using (show (0 : ℝ) < 1 by norm_num)
    · have hsr : 1 ≤ Real.sqrt (r : ℝ) :=
        p08_sqrt_card_ge_one (Nat.pos_of_ne_zero hr)
      have hle : (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
        nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hsr)]
      have hmul : (r : ℝ) * fp.u ≤
          ((r : ℝ) * Real.sqrt (r : ℝ)) * fp.u :=
        mul_le_mul_of_nonneg_right hle fp.u_nonneg
      nlinarith [mul_nonneg hb0 fp.u_nonneg]

private theorem p08_gamma_composition
    {a d s u : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hs : 1 ≤ s)
    (hu : 0 ≤ u) (hvalid : (a + d * s) * u < 1) :
    a * u / (1 - a * u) +
      (d * u / (1 - d * u)) * s +
      (a * u / (1 - a * u)) * ((d * u / (1 - d * u)) * s) ≤
      (a + d * s) * u / (1 - (a + d * s) * u) := by
  let A := a * u
  let D := d * u
  have hA : 0 ≤ A := mul_nonneg ha hu
  have hD : 0 ≤ D := mul_nonneg hd hu
  have hDs : 0 ≤ D * s := mul_nonneg hD (by linarith)
  have hC : A + D * s < 1 := by dsimp [A, D]; nlinarith [hvalid]
  have hA1 : 0 < 1 - A := by linarith
  have hD1 : 0 < 1 - D := by
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hs)]
  have hC1 : 0 < 1 - (A + D * s) := by linarith
  have hrem : 0 ≤ D * s * (A + D * (s - 1)) := by
    exact mul_nonneg hDs (add_nonneg hA (mul_nonneg hD (by linarith)))
  have hid :
      (A + D * s) * ((1 - A) * (1 - D)) -
      (A * (1 - D) + D * s) * (1 - (A + D * s)) =
      D * s * (A + D * (s - 1)) := by ring
  have hcross :
      (A * (1 - D) + D * s) * (1 - (A + D * s)) ≤
      (A + D * s) * ((1 - A) * (1 - D)) := by linarith
  have hcore :
      A / (1 - A) + D / (1 - D) * s +
        A / (1 - A) * (D / (1 - D) * s) ≤
        (A + D * s) / (1 - (A + D * s)) := by
    rw [le_div_iff₀ hC1]
    have heq :
        (A / (1 - A) + D / (1 - D) * s +
          A / (1 - A) * (D / (1 - D) * s)) *
          (1 - (A + D * s)) =
        ((A * (1 - D) + D * s) * (1 - (A + D * s))) /
          ((1 - A) * (1 - D)) := by
      field_simp [ne_of_gt hA1, ne_of_gt hD1]
      ring
    rw [heq]
    exact (div_le_iff₀ (mul_pos hA1 hD1)).mpr hcross
  convert hcore using 1 <;> dsimp [A, D] <;> ring

private theorem p08_stage_backward (fp : StandardFPModel)
    {m n : ℕ} (M : P08RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      p08RoundedRectMatVec fp M x = p08RectMatVec (p08RectAdd M E) x ∧
      p08RectFrobNorm E ≤ p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm M := by
  obtain ⟨E, hentry, heq⟩ :=
    NumStability.matVec_backward_error (p08AsFPModel fp) m n M x hvalid
  have hg : 0 ≤ p08GammaReal (n : ℝ) fp.u := by
    have h := NumStability.gamma_nonneg (p08AsFPModel fp) hvalid
    exact h
  refine ⟨E, ?_, ?_⟩
  · ext i
    simpa [p08RoundedRectMatVec_eq_fl, p08RectMatVec, p08RectAdd] using heq i
  · have h := NumStability.frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
      E M hg hentry
    simpa only [p08FrobNorm_eq_frobNormRect,
      NumStability.frobNormRect_eq_frobNormFn] using h

private theorem p08_norm_add_le {m n : ℕ}
    (M N : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectAdd M N) ≤
      p08RectFrobNorm M + p08RectFrobNorm N := by
  exact NumStability.frobNormRect_add_le M N

private theorem p08_norm_sub_le {m n : ℕ}
    (M N : P08RectMatrix m n) :
    p08RectFrobNorm (M - N) ≤
      p08RectFrobNorm M + p08RectFrobNorm N := by
  exact NumStability.frobNormRect_sub_le M N

private theorem p08_norm_mul_le {m n p : ℕ}
    (M : P08RectMatrix m n) (N : P08RectMatrix n p) :
    p08RectFrobNorm (p08RectMatMul M N) ≤
      p08RectFrobNorm M * p08RectFrobNorm N := by
  exact NumStability.frobNormRect_rectMatMul_le M N

private theorem p08_norm_mul_orthonormal_le {b r p : ℕ}
    (X : P08RectMatrix b r) (N : P08RectMatrix r p)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X N) ≤ p08RectFrobNorm N := by
  have h := NumStability.frobNormRect_rectMatMul_le_mul_of_rectOpNorm2Le
    X N (by norm_num : (0 : ℝ) ≤ 1) (p08OrthonormalColumns_opNorm hX)
  simpa only [p08FrobNorm_eq_frobNormRect, one_mul] using h

private theorem p08_norm_transpose {m n : ℕ}
    (M : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose M) = p08RectFrobNorm M := by
  exact NumStability.frobNormRect_finiteTranspose M

private theorem p08_lowrank_backward
    {b r : ℕ} (fp : StandardFPModel)
    (X Y : P08RectMatrix b r) (v : P08Vector b)
    (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ D : P08Matrix b,
      p08RoundedLowRankMatVec fp X Y v =
        p08MatVec (p08RectAdd (p08LowRankMatrix X Y) D) v ∧
      p08FrobNorm D ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08FrobNorm (p08LowRankMatrix X Y) := by
  let YT := p08RectTranspose Y
  let wHat := p08RoundedRectMatVec fp YT v
  let M := p08LowRankMatrix X Y
  let gB := p08GammaReal (b : ℝ) fp.u
  let gR := p08GammaReal (r : ℝ) fp.u
  let gC := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  obtain ⟨hb, hr⟩ := p08_valid_small_indices fp hvalid
  obtain ⟨EY, hEYact, hEYnorm⟩ := p08_stage_backward fp YT v hb
  obtain ⟨EX, hEXact, hEXnorm⟩ := p08_stage_backward fp X wHat hr
  have hYn : p08RectFrobNorm YT = p08FrobNorm M := by
    rw [show YT = p08RectTranspose Y by rfl, p08_norm_transpose]
    exact (p08OrthonormalColumns_lowRank_norm hX).symm
  have hXn : p08RectFrobNorm X = Real.sqrt (r : ℝ) :=
    p08OrthonormalColumns_norm hX
  have hEYn : p08RectFrobNorm EY ≤ gB * p08FrobNorm M := by
    simpa only [gB, hYn] using hEYnorm
  have hEXn : p08RectFrobNorm EX ≤ gR * Real.sqrt (r : ℝ) := by
    simpa only [gR, hXn] using hEXnorm
  have hgB : 0 ≤ gB := by
    exact NumStability.gamma_nonneg (p08AsFPModel fp) hb
  have hgR : 0 ≤ gR := by
    exact NumStability.gamma_nonneg (p08AsFPModel fp) hr
  have hgC : 0 ≤ gC := by
    unfold gC p08GammaReal
    exact div_nonneg
      (mul_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity)
        (Real.sqrt_nonneg _))) fp.u_nonneg) (by linarith)
  have hcomp : gB + gR * Real.sqrt (r : ℝ) +
      gB * (gR * Real.sqrt (r : ℝ)) ≤ gC := by
    by_cases hr0 : r = 0
    · subst r
      simp [gB, gR, gC, p08GammaReal]
    · have hs := p08_sqrt_card_ge_one (Nat.pos_of_ne_zero hr0)
      exact p08_gamma_composition (by positivity : (0 : ℝ) ≤ b)
        (by positivity : (0 : ℝ) ≤ r) hs fp.u_nonneg hvalid
  let N1 := p08RectMatMul X EY
  let N2 := p08RectMatMul EX YT
  let N3 := p08RectMatMul EX EY
  let D : P08Matrix b := p08RectAdd (p08RectAdd N1 N2) N3
  have hN1 : p08FrobNorm N1 ≤ gB * p08FrobNorm M := by
    exact le_trans (p08_norm_mul_orthonormal_le X EY hX) hEYn
  have hN2 : p08FrobNorm N2 ≤
      (gR * Real.sqrt (r : ℝ)) * p08FrobNorm M := by
    calc
      p08FrobNorm N2 ≤ p08RectFrobNorm EX * p08RectFrobNorm YT :=
        p08_norm_mul_le EX YT
      _ ≤ (gR * Real.sqrt (r : ℝ)) * p08RectFrobNorm YT :=
        mul_le_mul_of_nonneg_right hEXn (Real.sqrt_nonneg _)
      _ = _ := by rw [hYn]
  have hN3 : p08FrobNorm N3 ≤
      (gB * (gR * Real.sqrt (r : ℝ))) * p08FrobNorm M := by
    calc
      p08FrobNorm N3 ≤ p08RectFrobNorm EX * p08RectFrobNorm EY :=
        p08_norm_mul_le EX EY
      _ ≤ (gR * Real.sqrt (r : ℝ)) * p08RectFrobNorm EY :=
        mul_le_mul_of_nonneg_right hEXn (Real.sqrt_nonneg _)
      _ ≤ (gR * Real.sqrt (r : ℝ)) * (gB * p08FrobNorm M) :=
        mul_le_mul_of_nonneg_left hEYn
          (mul_nonneg hgR (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hDnorm : p08FrobNorm D ≤ gC * p08FrobNorm M := by
    have h12 := p08_norm_add_le N1 N2
    have h123 := p08_norm_add_le (p08RectAdd N1 N2) N3
    change p08FrobNorm (p08RectAdd N1 N2) ≤
      p08FrobNorm N1 + p08FrobNorm N2 at h12
    change p08FrobNorm (p08RectAdd (p08RectAdd N1 N2) N3) ≤
      p08FrobNorm (p08RectAdd N1 N2) + p08FrobNorm N3 at h123
    have hsum : p08FrobNorm D ≤
        (gB + gR * Real.sqrt (r : ℝ) +
          gB * (gR * Real.sqrt (r : ℝ))) * p08FrobNorm M := by
      have htri : p08FrobNorm D ≤
          p08FrobNorm N1 + p08FrobNorm N2 + p08FrobNorm N3 := by
        dsimp [D]
        linarith [h12, h123]
      calc
        p08FrobNorm D ≤
            p08FrobNorm N1 + p08FrobNorm N2 + p08FrobNorm N3 := htri
        _ ≤ gB * p08FrobNorm M +
            (gR * Real.sqrt (r : ℝ)) * p08FrobNorm M +
            (gB * (gR * Real.sqrt (r : ℝ))) * p08FrobNorm M :=
          add_le_add (add_le_add hN1 hN2) hN3
        _ = _ := by ring
    exact le_trans hsum (mul_le_mul_of_nonneg_right hcomp (Real.sqrt_nonneg _))
  have hprod : p08RectMatMul (p08RectAdd X EX) (p08RectAdd YT EY) =
      p08RectAdd M D := by
    ext i j
    simp only [D, N1, N2, N3, M, YT, p08RectMatMul, p08RectAdd,
      p08LowRankMatrix, p08RectTranspose, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring
  have hact : p08RoundedLowRankMatVec fp X Y v =
      p08MatVec (p08RectMatMul (p08RectAdd X EX) (p08RectAdd YT EY)) v := by
    change p08RoundedRectMatVec fp X wHat = _
    rw [hEXact]
    have hw : wHat = p08RectMatVec (p08RectAdd YT EY) v := hEYact
    rw [hw]
    exact (NumStability.rectMatMulVec_rectMatMul
      (p08RectAdd X EX) (p08RectAdd YT EY) v).symm
  refine ⟨D, ?_, ?_⟩
  · simpa only [hprod] using hact
  · exact hDnorm

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
  let M := p08LowRankMatrix X Y
  let gC := p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u
  obtain ⟨D, hDact, hDnorm⟩ :=
    p08_lowrank_backward fp X Y v hX hvalid
  let E : P08Matrix b := A - M
  let D2 : P08Matrix b := D - E
  have hMnorm : p08FrobNorm M ≤ p08FrobNorm A + p08FrobNorm E := by
    have hMeq : M = A - E := by
      ext i j
      simp [E, Matrix.sub_apply]
    rw [hMeq]
    exact p08_norm_sub_le A E
  have hD2norm : p08FrobNorm D2 ≤ p08FrobNorm D + p08FrobNorm E :=
    p08_norm_sub_le D E
  have hgC : 0 ≤ gC := by
    unfold gC p08GammaReal
    exact div_nonneg
      (mul_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity)
        (Real.sqrt_nonneg _))) fp.u_nonneg) (by linarith)
  have hAeq : p08RectAdd A D2 = p08RectAdd M D := by
    ext i j
    simp [D2, E, p08RectAdd, Matrix.sub_apply]
    ring
  have hAbound : p08FrobNorm D2 ≤
      gC * p08FrobNorm A + ε * (1 + gC) * β := by
    have hε : p08FrobNorm E ≤ ε * β := happrox
    have hmul := mul_le_mul_of_nonneg_left hMnorm hgC
    have hεmul := mul_le_mul_of_nonneg_left hε (by linarith : 0 ≤ 1 + gC)
    calc
      p08FrobNorm D2 ≤ p08FrobNorm D + p08FrobNorm E := hD2norm
      _ ≤ gC * p08FrobNorm M + p08FrobNorm E :=
        add_le_add_left hDnorm _
      _ ≤ gC * p08FrobNorm A + (1 + gC) * p08FrobNorm E := by
        nlinarith
      _ ≤ gC * p08FrobNorm A + (1 + gC) * (ε * β) :=
        add_le_add_right hεmul _
      _ = gC * p08FrobNorm A + ε * (1 + gC) * β := by ring
  refine ⟨D, D2, ?_, ?_, ?_, ?_⟩
  · exact hDact
  · exact hDnorm
  · rw [hAeq]
    exact hDact
  · exact hAbound

end VSCLReuse

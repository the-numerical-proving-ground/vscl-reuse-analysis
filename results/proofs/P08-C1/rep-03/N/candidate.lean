import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped Matrix Matrix.Norms.Frobenius

private theorem p08_rect_norm_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = ‖A‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]

private theorem p08_rect_mul_eq {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectMatMul A B = A * B := by
  ext i j
  simp [p08RectMatMul, Matrix.mul_apply]

private theorem p08_rect_transpose_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectTranspose A = Aᵀ := by
  ext i j
  rfl

private theorem p08_mat_mul_eq {n : ℕ} (A B : P08Matrix n) :
    p08MatMul A B = A * B := p08_rect_mul_eq A B

private theorem p08_frob_norm_eq {n : ℕ} (A : P08Matrix n) :
    p08FrobNorm A = ‖A‖ := p08_rect_norm_eq A

private theorem p08_low_rank_eq {b r : ℕ} (X Y : P08RectMatrix b r) :
    p08LowRankMatrix X Y = X * Yᵀ := by
  rw [p08LowRankMatrix, p08_rect_mul_eq, p08_rect_transpose_eq]

private theorem p08_orthonormal_mul_self {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    Xᵀ * X = 1 := by
  ext j k
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact hX j k

private theorem p08_orthonormal_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖X‖ = Real.sqrt (r : ℝ) := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc
    (∑ i : Fin b, ∑ j : Fin r, X i j ^ 2) =
        ∑ j : Fin r, ∑ i : Fin b, X i j * X i j := by
          rw [Finset.sum_comm]
          congr 1
          ext j
          congr 1
          ext i
          ring
    _ = ∑ j : Fin r, (1 : ℝ) := by
      congr 1
      ext j
      simpa using hX j j
    _ = (r : ℝ) := by simp

private theorem p08_norm_sq_sum_eq_diag {m n : ℕ} (A : P08RectMatrix m n) :
    (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) =
      ∑ j : Fin n, (Aᵀ * A) j j := by
  rw [Finset.sum_comm]
  congr 1
  ext j
  rw [Matrix.mul_apply]
  congr 1
  ext i
  simp [sq]

private theorem p08_orthonormal_mul_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (Y : P08RectMatrix r n)
    (hX : p08OrthonormalColumns X) :
    ‖X * Y‖ = ‖Y‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow]
  congr 1
  rw [p08_norm_sq_sum_eq_diag, p08_norm_sq_sum_eq_diag]
  have h : (X * Y)ᵀ * (X * Y) = Yᵀ * Y := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc Yᵀ Xᵀ (X * Y),
      ← Matrix.mul_assoc Xᵀ X Y]
    rw [p08_orthonormal_mul_self X hX]
    simp
  rw [h]

private theorem p08_orthonormal_mul_transpose_norm {b r m : ℕ}
    (X : P08RectMatrix b r) (Y : P08RectMatrix m r)
    (hX : p08OrthonormalColumns X) :
    ‖Y * Xᵀ‖ = ‖Y‖ := by
  rw [← Matrix.frobenius_norm_transpose (Y * Xᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [p08_orthonormal_mul_norm X Yᵀ hX, Matrix.frobenius_norm_transpose]

private theorem p08_gamma_one_add (k u : ℝ) (h : k * u < 1) :
    1 + p08GammaReal k u = 1 / (1 - k * u) := by
  have hd : 1 - k * u ≠ 0 := ne_of_gt (sub_pos.mpr h)
  unfold p08GammaReal
  field_simp
  ring

private theorem p08_gamma_nonneg (k u : ℝ) (hk : 0 ≤ k) (hu : 0 ≤ u)
    (h : k * u < 1) : 0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (sub_nonneg.mpr h.le)

private theorem p08_gamma_combine (a d u : ℝ)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hu : 0 ≤ u)
    (h : (a + d) * u < 1) :
    (1 + p08GammaReal a u) * (1 + p08GammaReal d u) ≤
      1 + p08GammaReal (a + d) u := by
  have ha' : a * u < 1 := by nlinarith [mul_nonneg hd hu]
  have hd' : d * u < 1 := by nlinarith [mul_nonneg ha hu]
  rw [p08_gamma_one_add a u ha', p08_gamma_one_add d u hd',
    p08_gamma_one_add (a + d) u h]
  have hA : 0 < 1 - a * u := sub_pos.mpr ha'
  have hD : 0 < 1 - d * u := sub_pos.mpr hd'
  have hAD : 0 < 1 - (a + d) * u := sub_pos.mpr h
  rw [one_div_mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hA hD) hAD).2
  nlinarith [mul_nonneg (mul_nonneg ha hd) (mul_nonneg hu hu)]

private theorem p08_gamma_scaled (r u : ℝ) (hr : 0 ≤ r) (hu : 0 ≤ u)
    (hs : 1 ≤ Real.sqrt r) (h : r * Real.sqrt r * u < 1) :
    p08GammaReal r u * Real.sqrt r ≤
      p08GammaReal (r * Real.sqrt r) u := by
  have hrs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hru : r * u < 1 := by nlinarith [mul_nonneg hr hu]
  have hD : 0 < 1 - r * u := sub_pos.mpr hru
  have hDS : 0 < 1 - r * Real.sqrt r * u := sub_pos.mpr h
  unfold p08GammaReal
  conv_lhs => rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hD hDS).2
  nlinarith [mul_nonneg (mul_nonneg hr hu) hrs,
    mul_nonneg (mul_nonneg hr hu) (sub_nonneg.mpr hs)]

private theorem p08_gamma_budget (b r u : ℝ)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hu : 0 ≤ u)
    (hrank : r = 0 ∨ 1 ≤ r)
    (hvalid : (b + 2 * r * Real.sqrt r) * u < 1) :
    (1 + p08GammaReal b u) *
        (1 + p08GammaReal r u * Real.sqrt r) *
        (1 + p08GammaReal r u * Real.sqrt r) ≤
      1 + p08GammaReal (b + 2 * r * Real.sqrt r) u := by
  let s := Real.sqrt r
  let t := r * s
  have hs : 0 ≤ s := Real.sqrt_nonneg r
  have ht : 0 ≤ t := mul_nonneg hr hs
  have hbt : (b + t) * u < 1 := by
    dsimp [t, s] at *
    nlinarith [mul_nonneg ht hu]
  have htu : t * u < 1 := by nlinarith [mul_nonneg hb hu]
  have hru : r * u < 1 := by
    rcases hrank with hrzero | hr1
    · simp [hrzero]
    · have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hr1
      nlinarith [mul_nonneg (mul_nonneg hr hu) (sub_nonneg.mpr hs1)]
  have hgr : 0 ≤ p08GammaReal r u := p08_gamma_nonneg r u hr hu hru
  have hgb : 0 ≤ p08GammaReal b u :=
    p08_gamma_nonneg b u hb hu (by nlinarith [mul_nonneg ht hu])
  have hgt : 0 ≤ p08GammaReal t u := p08_gamma_nonneg t u ht hu htu
  have hgbt : 0 ≤ p08GammaReal (b + t) u :=
    p08_gamma_nonneg (b + t) u (add_nonneg hb ht) hu hbt
  have hscale : p08GammaReal r u * s ≤ p08GammaReal t u := by
    rcases hrank with hrzero | hr1
    · simp [t, hrzero, p08GammaReal]
    · have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hr1
      exact p08_gamma_scaled r u hr hu hs1 (by simpa [t, s] using htu)
  have hcombine1 :
      (1 + p08GammaReal b u) * (1 + p08GammaReal t u) ≤
        1 + p08GammaReal (b + t) u :=
    p08_gamma_combine b t u hb ht hu hbt
  have hcombine2 :
      (1 + p08GammaReal (b + t) u) * (1 + p08GammaReal t u) ≤
        1 + p08GammaReal (b + 2 * t) u := by
    have h2 : (b + t + t) * u < 1 := by
      convert hvalid using 1 <;> ring
    convert p08_gamma_combine (b + t) t u (add_nonneg hb ht) ht hu h2 using 1 <;> ring
  have hfirst :
      (1 + p08GammaReal b u) * (1 + p08GammaReal r u * s) ≤
        (1 + p08GammaReal b u) * (1 + p08GammaReal t u) := by
    gcongr
  have hsecond := mul_le_mul_of_nonneg_right
    (hfirst.trans hcombine1)
    (by nlinarith [mul_nonneg hgr hs] : 0 ≤ 1 + p08GammaReal r u * s)
  have hthird := mul_le_mul_of_nonneg_left
    (by linarith [hscale] : 1 + p08GammaReal r u * s ≤ 1 + p08GammaReal t u)
    (by linarith : 0 ≤ 1 + p08GammaReal (b + t) u)
  calc
    _ ≤ (1 + p08GammaReal (b + t) u) *
        (1 + p08GammaReal r u * s) := hsecond
    _ ≤ (1 + p08GammaReal (b + t) u) *
        (1 + p08GammaReal t u) := hthird
    _ ≤ 1 + p08GammaReal (b + 2 * t) u := hcombine2
    _ = _ := by congr 1; congr 1; dsimp [t, s]; ring

private theorem p08_stage_budget
    {g0 g1 gc P M L e0 e1 e2 : ℝ}
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hP : 0 ≤ P)
    (he0 : e0 ≤ g0 * P) (hM : M ≤ P + e0)
    (he1 : e1 ≤ g1 * M) (hL : L ≤ M + e1)
    (he2 : e2 ≤ g1 * L)
    (hbudget : (1 + g0) * (1 + g1) * (1 + g1) ≤ 1 + gc) :
    e0 + e1 + e2 ≤ gc * P := by
  have hM' : M ≤ (1 + g0) * P := by nlinarith
  have he1' : e1 ≤ g1 * ((1 + g0) * P) :=
    le_trans he1 (mul_le_mul_of_nonneg_left hM' hg1)
  have hL' : L ≤ (1 + g1) * ((1 + g0) * P) := by
    nlinarith [he1']
  have he2' : e2 ≤ g1 * ((1 + g1) * ((1 + g0) * P)) :=
    le_trans he2 (mul_le_mul_of_nonneg_left hL' hg1)
  have hbudget' : ((1 + g0) * (1 + g1) * (1 + g1)) * P ≤
      (1 + gc) * P := mul_le_mul_of_nonneg_right hbudget hP
  nlinarith [he1', he2', hbudget']

private theorem p08_left_error_identity {b r : ℕ}
    (X YA XB YB : P08RectMatrix b r)
    (E0 : P08RectMatrix r r) (E1 : P08RectMatrix b r)
    (E2 : P08Matrix b) :
    ((X * (YAᵀ * YB + E0) + E1) * XBᵀ + E2) -
        (X * YAᵀ) * (YB * XBᵀ) =
      (X * E0) * XBᵀ + E1 * XBᵀ + E2 := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

private theorem p08_right_error_identity {b r : ℕ}
    (X YA XB YB : P08RectMatrix b r)
    (E0 : P08RectMatrix r r) (E1 : P08RectMatrix r b)
    (E2 : P08Matrix b) :
    (X * ((YAᵀ * YB + E0) * XBᵀ + E1) + E2) -
        (X * YAᵀ) * (YB * XBᵀ) =
      X * (E0 * XBᵀ) + X * E1 + E2 := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

private theorem p08_left_trace_error {b r : ℕ} {u : ℝ}
    {X YA XB YB : P08RectMatrix b r}
    (hX : p08OrthonormalColumns X)
    (hXB : p08OrthonormalColumns XB)
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (left : P08RoundedMatMulStage b r r u X middle.result)
    (final : P08RoundedMatMulStage b r b u left.result (p08RectTranspose XB)) :
    ‖final.result - (X * YAᵀ) * (YB * XBᵀ)‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        ‖X * YAᵀ‖ * ‖YB * XBᵀ‖ := by
  let g0 := p08GammaReal (b : ℝ) u
  let g1 := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
  let gc := p08GammaReal (p08LowRankMatMulCost b r) u
  let P := ‖YAᵀ‖ * ‖YB‖
  have hrank : (r : ℝ) = 0 ∨ 1 ≤ (r : ℝ) := by
    by_cases hr0 : r = 0
    · left; simp [hr0]
    · right; exact_mod_cast (by omega : 1 ≤ r)
  have hbudget : (1 + g0) * (1 + g1) * (1 + g1) ≤ 1 + gc := by
    simpa only [g0, g1, gc, p08LowRankMatMulCost] using
      p08_gamma_budget (b : ℝ) (r : ℝ) u
        (by positivity) (by positivity) hu hrank (by simpa [p08LowRankMatMulCost] using hvalid)
  have hgb : 0 ≤ g0 := by
    apply p08_gamma_nonneg (b : ℝ) u (by positivity) hu
    have ht : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) * u := by positivity
    dsimp [p08LowRankMatMulCost] at hvalid
    nlinarith
  have hgr : 0 ≤ g1 := by
    have hru : (r : ℝ) * u < 1 := by
      rcases hrank with hr0 | hr1
      · simp [hr0]
      · have hs1 : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hr1
        have hrest : 0 ≤ (b : ℝ) * u := by positivity
        have hx : 0 ≤ ((r : ℝ) * u) * (Real.sqrt (r : ℝ) - 1) :=
          mul_nonneg (mul_nonneg (by positivity) hu) (sub_nonneg.mpr hs1)
        dsimp [p08LowRankMatMulCost] at hvalid
        nlinarith
    exact mul_nonneg (p08_gamma_nonneg (r : ℝ) u (by positivity) hu hru)
      (Real.sqrt_nonneg _)
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hE0 : ‖middle.error‖ ≤ g0 * P := by
    simpa only [p08_rect_norm_eq, p08_rect_transpose_eq, g0, P, mul_assoc]
      using middle.error_le
  have hM : ‖middle.result‖ ≤ P + ‖middle.error‖ := by
    change ‖YAᵀ * YB + middle.error‖ ≤ P + ‖middle.error‖
    calc
      _ ≤ ‖YAᵀ * YB‖ + ‖middle.error‖ := norm_add_le _ _
      _ ≤ P + ‖middle.error‖ := by
        dsimp [P]
        gcongr
        exact Matrix.frobenius_norm_mul YAᵀ YB
  have hE1 : ‖left.error‖ ≤ g1 * ‖middle.result‖ := by
    have h := left.error_le
    rw [p08_rect_norm_eq, p08_rect_norm_eq, p08_rect_norm_eq,
      p08_orthonormal_norm X hX] at h
    simpa only [g1, mul_assoc] using h
  have hL : ‖left.result‖ ≤ ‖middle.result‖ + ‖left.error‖ := by
    rw [P08RoundedMatMulStage.result, p08_rect_mul_eq]
    calc
      ‖X * middle.result + left.error‖ ≤
          ‖X * middle.result‖ + ‖left.error‖ := norm_add_le _ _
      _ = _ := by rw [p08_orthonormal_mul_norm X middle.result hX]
  have hE2 : ‖final.error‖ ≤ g1 * ‖left.result‖ := by
    have h := final.error_le
    simp only [p08_rect_norm_eq, p08_rect_transpose_eq,
      Matrix.frobenius_norm_transpose,
      p08_orthonormal_norm XB hXB] at h
    dsimp [g1]
    convert h using 1 <;> ring
  have htotal :
      ‖final.result - (X * YAᵀ) * (YB * XBᵀ)‖ ≤
        ‖middle.error‖ + ‖left.error‖ + ‖final.error‖ := by
    simp only [P08RoundedMatMulStage.result, p08_rect_mul_eq,
      p08_rect_transpose_eq]
    rw [p08_left_error_identity]
    calc
      ‖(X * middle.error) * XBᵀ + left.error * XBᵀ + final.error‖ ≤
          (‖(X * middle.error) * XBᵀ‖ + ‖left.error * XBᵀ‖) +
            ‖final.error‖ := by
              calc
                _ ≤ ‖(X * middle.error) * XBᵀ + left.error * XBᵀ‖ +
                    ‖final.error‖ := norm_add_le _ _
                _ ≤ (‖(X * middle.error) * XBᵀ‖ + ‖left.error * XBᵀ‖) +
                    ‖final.error‖ := by
                      gcongr
                      exact norm_add_le _ _
      _ = _ := by
        rw [p08_orthonormal_mul_transpose_norm XB (X * middle.error) hXB,
          p08_orthonormal_mul_norm X middle.error hX,
          p08_orthonormal_mul_transpose_norm XB left.error hXB]
  have hscalar : ‖middle.error‖ + ‖left.error‖ + ‖final.error‖ ≤ gc * P :=
    p08_stage_budget hgb hgr hP hE0 hM hE1 hL hE2 hbudget
  calc
    _ ≤ ‖middle.error‖ + ‖left.error‖ + ‖final.error‖ := htotal
    _ ≤ gc * P := hscalar
    _ = _ := by
      dsimp [gc, P]
      rw [p08_orthonormal_mul_norm X YAᵀ hX,
        p08_orthonormal_mul_transpose_norm XB YB hXB]
      ring

private theorem p08_right_trace_error {b r : ℕ} {u : ℝ}
    {X YA XB YB : P08RectMatrix b r}
    (hX : p08OrthonormalColumns X)
    (hXB : p08OrthonormalColumns XB)
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (right : P08RoundedMatMulStage r r b u middle.result (p08RectTranspose XB))
    (final : P08RoundedMatMulStage b r b u X right.result) :
    ‖final.result - (X * YAᵀ) * (YB * XBᵀ)‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        ‖X * YAᵀ‖ * ‖YB * XBᵀ‖ := by
  let g0 := p08GammaReal (b : ℝ) u
  let g1 := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
  let gc := p08GammaReal (p08LowRankMatMulCost b r) u
  let P := ‖YAᵀ‖ * ‖YB‖
  have hrank : (r : ℝ) = 0 ∨ 1 ≤ (r : ℝ) := by
    by_cases hr0 : r = 0
    · left; simp [hr0]
    · right; exact_mod_cast (by omega : 1 ≤ r)
  have hbudget : (1 + g0) * (1 + g1) * (1 + g1) ≤ 1 + gc := by
    simpa only [g0, g1, gc, p08LowRankMatMulCost] using
      p08_gamma_budget (b : ℝ) (r : ℝ) u
        (by positivity) (by positivity) hu hrank (by simpa [p08LowRankMatMulCost] using hvalid)
  have hgb : 0 ≤ g0 := by
    apply p08_gamma_nonneg (b : ℝ) u (by positivity) hu
    have ht : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) * u := by positivity
    dsimp [p08LowRankMatMulCost] at hvalid
    nlinarith
  have hgr : 0 ≤ g1 := by
    have hru : (r : ℝ) * u < 1 := by
      rcases hrank with hr0 | hr1
      · simp [hr0]
      · have hs1 : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hr1
        have hrest : 0 ≤ (b : ℝ) * u := by positivity
        have hx : 0 ≤ ((r : ℝ) * u) * (Real.sqrt (r : ℝ) - 1) :=
          mul_nonneg (mul_nonneg (by positivity) hu) (sub_nonneg.mpr hs1)
        dsimp [p08LowRankMatMulCost] at hvalid
        nlinarith
    exact mul_nonneg (p08_gamma_nonneg (r : ℝ) u (by positivity) hu hru)
      (Real.sqrt_nonneg _)
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hE0 : ‖middle.error‖ ≤ g0 * P := by
    simpa only [p08_rect_norm_eq, p08_rect_transpose_eq, g0, P, mul_assoc]
      using middle.error_le
  have hM : ‖middle.result‖ ≤ P + ‖middle.error‖ := by
    change ‖YAᵀ * YB + middle.error‖ ≤ P + ‖middle.error‖
    calc
      _ ≤ ‖YAᵀ * YB‖ + ‖middle.error‖ := norm_add_le _ _
      _ ≤ P + ‖middle.error‖ := by
        dsimp [P]
        gcongr
        exact Matrix.frobenius_norm_mul YAᵀ YB
  have hE1 : ‖right.error‖ ≤ g1 * ‖middle.result‖ := by
    have h := right.error_le
    simp only [p08_rect_norm_eq, p08_rect_transpose_eq,
      Matrix.frobenius_norm_transpose,
      p08_orthonormal_norm XB hXB] at h
    dsimp [g1]
    convert h using 1 <;> ring
  have hR : ‖right.result‖ ≤ ‖middle.result‖ + ‖right.error‖ := by
    change ‖middle.result * XBᵀ + right.error‖ ≤
      ‖middle.result‖ + ‖right.error‖
    calc
      _ ≤ ‖middle.result * XBᵀ‖ + ‖right.error‖ := norm_add_le _ _
      _ = _ := by rw [p08_orthonormal_mul_transpose_norm XB middle.result hXB]
  have hE2 : ‖final.error‖ ≤ g1 * ‖right.result‖ := by
    have h := final.error_le
    rw [p08_rect_norm_eq, p08_rect_norm_eq, p08_rect_norm_eq,
      p08_orthonormal_norm X hX] at h
    simpa only [g1, mul_assoc] using h
  have htotal :
      ‖final.result - (X * YAᵀ) * (YB * XBᵀ)‖ ≤
        ‖middle.error‖ + ‖right.error‖ + ‖final.error‖ := by
    simp only [P08RoundedMatMulStage.result, p08_rect_mul_eq,
      p08_rect_transpose_eq]
    rw [p08_right_error_identity]
    calc
      ‖X * (middle.error * XBᵀ) + X * right.error + final.error‖ ≤
          (‖X * (middle.error * XBᵀ)‖ + ‖X * right.error‖) +
            ‖final.error‖ := by
              calc
                _ ≤ ‖X * (middle.error * XBᵀ) + X * right.error‖ +
                    ‖final.error‖ := norm_add_le _ _
                _ ≤ (‖X * (middle.error * XBᵀ)‖ + ‖X * right.error‖) +
                    ‖final.error‖ := by
                      gcongr
                      exact norm_add_le _ _
      _ = _ := by
        rw [p08_orthonormal_mul_norm X (middle.error * XBᵀ) hX,
          p08_orthonormal_mul_transpose_norm XB middle.error hXB,
          p08_orthonormal_mul_norm X right.error hX]
  have hscalar : ‖middle.error‖ + ‖right.error‖ + ‖final.error‖ ≤ gc * P :=
    p08_stage_budget hgb hgr hP hE0 hM hE1 hR hE2 hbudget
  calc
    _ ≤ ‖middle.error‖ + ‖right.error‖ + ‖final.error‖ := htotal
    _ ≤ gc * P := hscalar
    _ = _ := by
      dsimp [gc, P]
      rw [p08_orthonormal_mul_norm X YAᵀ hX,
        p08_orthonormal_mul_transpose_norm XB YB hXB]
      ring

private theorem p08_perturbation_identity {n : ℕ}
    (A B EA EB : P08Matrix n) :
    (A + EA) * (B + EB) - A * B = EA * B + A * EB + EA * EB := by
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

private theorem p08_approximation_transfer {n : ℕ}
    (A B EA EB C : P08Matrix n) (g eA eB : ℝ)
    (hg : 0 ≤ g) (heA : 0 ≤ eA) (heB : 0 ≤ eB)
    (hEA : ‖EA‖ ≤ eA) (hEB : ‖EB‖ ≤ eB)
    (hC : ‖C - (A + EA) * (B + EB)‖ ≤
      g * ‖A + EA‖ * ‖B + EB‖) :
    ‖C - A * B‖ ≤ g * ‖A‖ * ‖B‖ +
      (1 + g) * (eA * ‖B‖ + ‖A‖ * eB + eA * eB) := by
  have hA : ‖A + EA‖ ≤ ‖A‖ + eA := by
    calc
      _ ≤ ‖A‖ + ‖EA‖ := norm_add_le _ _
      _ ≤ ‖A‖ + eA := by gcongr
  have hB : ‖B + EB‖ ≤ ‖B‖ + eB := by
    calc
      _ ≤ ‖B‖ + ‖EB‖ := norm_add_le _ _
      _ ≤ ‖B‖ + eB := by gcongr
  have hC' : ‖C - (A + EA) * (B + EB)‖ ≤
      g * ((‖A‖ + eA) * (‖B‖ + eB)) := by
    calc
      _ ≤ g * ‖A + EA‖ * ‖B + EB‖ := hC
      _ ≤ g * ((‖A‖ + eA) * (‖B‖ + eB)) := by
        have hp : ‖A + EA‖ * ‖B + EB‖ ≤
            (‖A‖ + eA) * (‖B‖ + eB) := by
          gcongr
        nlinarith [mul_le_mul_of_nonneg_left hp hg]
  have hpert : ‖(A + EA) * (B + EB) - A * B‖ ≤
      eA * ‖B‖ + ‖A‖ * eB + eA * eB := by
    rw [p08_perturbation_identity]
    calc
      ‖EA * B + A * EB + EA * EB‖ ≤
          ‖EA * B‖ + ‖A * EB‖ + ‖EA * EB‖ := by
            calc
              _ ≤ ‖EA * B + A * EB‖ + ‖EA * EB‖ := norm_add_le _ _
              _ ≤ ‖EA * B‖ + ‖A * EB‖ + ‖EA * EB‖ := by
                gcongr
                exact norm_add_le _ _
      _ ≤ ‖EA‖ * ‖B‖ + ‖A‖ * ‖EB‖ + ‖EA‖ * ‖EB‖ := by
        gcongr <;> exact Matrix.frobenius_norm_mul _ _
      _ ≤ eA * ‖B‖ + ‖A‖ * eB + eA * eB := by
        gcongr
  have htriangle : ‖C - A * B‖ ≤
      ‖C - (A + EA) * (B + EB)‖ +
        ‖(A + EA) * (B + EB) - A * B‖ := by
    have hid : C - A * B =
        (C - (A + EA) * (B + EB)) +
          ((A + EA) * (B + EB) - A * B) := by abel
    rw [hid]
    exact norm_add_le _ _
  nlinarith [hC', hpert, htriangle]

private theorem p08_trace_error {b r : ℕ} {u : ℝ}
    {X YA XB YB : P08RectMatrix b r}
    (hX : p08OrthonormalColumns X)
    (hXB : p08OrthonormalColumns XB)
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (trace : P08LowRankMatMulTrace u X YA XB YB) :
    ‖trace.result - (X * YAᵀ) * (YB * XBᵀ)‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        ‖X * YAᵀ‖ * ‖YB * XBᵀ‖ := by
  cases trace with
  | leftAssociated middle left final =>
      exact p08_left_trace_error hX hXB hu hvalid middle left final
  | rightAssociated middle right final =>
      exact p08_right_trace_error hX hXB hu hvalid middle right final

theorem p08_c1_low_rank_matmul_error {b r : ℕ}
    (run : P08LowRankMatMulExecution b r) :
    let Atilde := p08LowRankMatrix run.XA run.YA
    let Btilde := p08LowRankMatrix run.YB run.XB
    let gammaC :=
      p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
    p08FrobNorm (run.trace.result - p08MatMul Atilde Btilde) ≤
        gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde ∧
      p08FrobNorm (run.trace.result - p08MatMul run.A run.B) ≤
        gammaC * p08FrobNorm run.A * p08FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p08FrobNorm run.B +
              p08FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
  -- PROOF_START P08-C1-H001
  have htrace := p08_trace_error run.xA_orthonormal run.xB_orthonormal
    run.unitRoundoff_nonneg run.gamma_valid run.trace
  have hfirst :
      p08FrobNorm
          (run.trace.result -
            p08MatMul (p08LowRankMatrix run.XA run.YA)
              (p08LowRankMatrix run.YB run.XB)) ≤
        p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff *
          p08FrobNorm (p08LowRankMatrix run.XA run.YA) *
          p08FrobNorm (p08LowRankMatrix run.YB run.XB) := by
    simpa only [p08_frob_norm_eq, p08_mat_mul_eq, p08_low_rank_eq] using htrace
  have hEA : ‖run.approximationErrorA‖ ≤ run.epsilon * run.betaA := by
    simpa only [p08_frob_norm_eq] using run.approximationErrorA_le
  have hEB : ‖run.approximationErrorB‖ ≤ run.epsilon * run.betaB := by
    simpa only [p08_frob_norm_eq] using run.approximationErrorB_le
  have heA : 0 ≤ run.epsilon * run.betaA := le_trans (norm_nonneg _) hEA
  have heB : 0 ≤ run.epsilon * run.betaB := le_trans (norm_nonneg _) hEB
  have hg : 0 ≤ p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff :=
    p08_gamma_nonneg _ _ (by unfold p08LowRankMatMulCost; positivity)
      run.unitRoundoff_nonneg run.gamma_valid
  have hC :
      ‖run.trace.result -
        (run.A + run.approximationErrorA) *
          (run.B + run.approximationErrorB)‖ ≤
        p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff *
          ‖run.A + run.approximationErrorA‖ *
          ‖run.B + run.approximationErrorB‖ := by
    simpa only [run.approximationA_eq, run.approximationB_eq,
      p08_frob_norm_eq, p08_mat_mul_eq] using hfirst
  have htransfer := p08_approximation_transfer
    run.A run.B run.approximationErrorA run.approximationErrorB
    run.trace.result
    (p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff)
    (run.epsilon * run.betaA) (run.epsilon * run.betaB)
    hg heA heB hEA hEB hC
  constructor
  · exact hfirst
  · simpa only [p08_frob_norm_eq, p08_mat_mul_eq] using
      (show ‖run.trace.result - run.A * run.B‖ ≤
          p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff *
            ‖run.A‖ * ‖run.B‖ +
            run.epsilon *
              (1 + p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff) *
              (run.betaA * ‖run.B‖ + ‖run.A‖ * run.betaB +
                run.epsilon * run.betaA * run.betaB) from by
        convert htransfer using 1 <;> ring)

end VSCLReuse

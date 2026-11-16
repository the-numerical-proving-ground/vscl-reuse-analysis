import VSCLReuse.P08.Definitions
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace VSCLReuse

private lemma p08_norm_eq {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = NumStability.frobNormRect M := rfl

private lemma p08_mul_eq {m n p : ℕ}
    (M : P08RectMatrix m n) (N : P08RectMatrix n p) :
    p08RectMatMul M N = M * N := rfl

private lemma p08_transpose_eq {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectTranspose M = M.transpose := rfl

private lemma p08_norm_nonneg {m n : ℕ} (M : P08RectMatrix m n) :
    0 ≤ p08RectFrobNorm M := by
  exact NumStability.frobNormRect_nonneg M

private lemma p08_norm_add_le {m n : ℕ} (M N : P08RectMatrix m n) :
    p08RectFrobNorm (M + N) ≤ p08RectFrobNorm M + p08RectFrobNorm N := by
  simpa only [p08_norm_eq] using NumStability.frobNormRect_add_le M N

private lemma p08_norm_sub_le {m n : ℕ} (M N : P08RectMatrix m n) :
    p08RectFrobNorm (M - N) ≤ p08RectFrobNorm M + p08RectFrobNorm N := by
  simpa only [p08_norm_eq] using NumStability.frobNormRect_sub_le M N

private lemma p08_norm_mul_le {m n p : ℕ}
    (M : P08RectMatrix m n) (N : P08RectMatrix n p) :
    p08RectFrobNorm (p08RectMatMul M N) ≤
      p08RectFrobNorm M * p08RectFrobNorm N := by
  exact NumStability.frobNormRect_rectMatMul_le M N

private lemma p08_orth_is_gram {m n : ℕ} (X : P08RectMatrix m n)
    (hX : p08OrthonormalColumns X) :
    NumStability.GramSchmidtOrthonormalColumns X := by
  intro i j
  simpa [NumStability.rectangularGram, NumStability.matMulRect,
    NumStability.finiteTranspose, NumStability.idMatrix] using hX i j

private lemma p08_norm_orth_left {m n p : ℕ}
    (X : P08RectMatrix m n) (M : P08RectMatrix n p)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X M) = p08RectFrobNorm M := by
  exact NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
    X M (p08_orth_is_gram X hX)

private lemma p08_norm_transpose {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose M) = p08RectFrobNorm M := by
  exact NumStability.frobNormRect_finiteTranspose M

private lemma p08_norm_orth_right {m n p : ℕ}
    (M : P08RectMatrix p n) (X : P08RectMatrix m n)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul M (p08RectTranspose X)) =
      p08RectFrobNorm M := by
  have htranspose :
      p08RectTranspose (p08RectMatMul M (p08RectTranspose X)) =
        p08RectMatMul X (p08RectTranspose M) := by
    ext i j
    simp only [p08RectTranspose, p08RectMatMul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    p08RectFrobNorm (p08RectMatMul M (p08RectTranspose X)) =
        p08RectFrobNorm (p08RectTranspose (p08RectMatMul M (p08RectTranspose X))) :=
      (p08_norm_transpose _).symm
    _ = p08RectFrobNorm (p08RectMatMul X (p08RectTranspose M)) := by rw [htranspose]
    _ = p08RectFrobNorm (p08RectTranspose M) := p08_norm_orth_left X _ hX
    _ = p08RectFrobNorm M := p08_norm_transpose M

private lemma p08_norm_orth_sqrt {m n : ℕ}
    (X : P08RectMatrix m n) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (n : ℝ) := by
  exact NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
    (p08_orth_is_gram X hX)

private lemma p08_gamma_comp (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y < 1) :
    (1 + x / (1 - x)) * (1 + y / (1 - y)) ≤
      1 + (x + y) / (1 - (x + y)) := by
  have hdx : 0 < 1 - x := by linarith
  have hdy : 0 < 1 - y := by linarith
  have hdxy : 0 < 1 - (x + y) := by linarith
  have hdx' : (1 - x) ≠ 0 := ne_of_gt hdx
  have hdy' : (1 - y) ≠ 0 := ne_of_gt hdy
  have hdxy' : (1 - (x + y)) ≠ 0 := ne_of_gt hdxy
  have hden : 1 - (x + y) ≤ (1 - x) * (1 - y) := by
    nlinarith [mul_nonneg hx hy]
  rw [show 1 + x / (1 - x) = 1 / (1 - x) by field_simp; ring,
    show 1 + y / (1 - y) = 1 / (1 - y) by field_simp; ring,
    show 1 + (x + y) / (1 - (x + y)) = 1 / (1 - (x + y)) by field_simp; ring]
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    (one_div_le_one_div_of_le hdxy hden)

private lemma p08_gamma_scale (y s : ℝ) (hy : 0 ≤ y) (hs : 1 ≤ s)
    (hys : y * s < 1) :
    (y / (1 - y)) * s ≤ (y * s) / (1 - y * s) := by
  have hle : y ≤ y * s := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hs)]
  have hdy : 0 < 1 - y := by linarith
  have hdys : 0 < 1 - y * s := by linarith
  have hn : 0 ≤ y * s := by nlinarith
  calc
    (y / (1 - y)) * s = (y * s) / (1 - y) := by ring
    _ ≤ (y * s) / (1 - y * s) :=
      div_le_div_of_nonneg_left hn hdys (by linarith)

private lemma p08_gamma_cost_bound {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hvalid : p08LowRankMatMulCost b r * u < 1) :
    (1 + p08GammaReal (b : ℝ) u) *
        (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ^ 2 ≤
      1 + p08GammaReal (p08LowRankMatMulCost b r) u := by
  let x : ℝ := (b : ℝ) * u
  let y : ℝ := (r : ℝ) * u
  let s : ℝ := Real.sqrt (r : ℝ)
  let z : ℝ := y * s
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg _) hu
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hz : 0 ≤ z := mul_nonneg hy hs0
  have hzs : y ≤ z := by
    by_cases hr : r = 0
    · simp [hr, y, z, s]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hs1 : 1 ≤ s := by
        simpa [s] using (Real.sqrt_le_sqrt hr1 : Real.sqrt 1 ≤ Real.sqrt (r : ℝ))
      exact le_mul_of_one_le_right hy hs1
  have hcost : p08LowRankMatMulCost b r * u = x + 2 * z := by
    dsimp [p08LowRankMatMulCost, x, y, s, z]
    ring
  have hxzz : x + z + z < 1 := by rw [hcost] at hvalid; linarith
  have hxy : x + z < 1 := by linarith
  have hz1 : z < 1 := by linarith
  have hscale :
      p08GammaReal (r : ℝ) u * s ≤ z / (1 - z) := by
    by_cases hr : r = 0
    · simp [hr, p08GammaReal, y, z, s]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hs1 : 1 ≤ s := by
        simpa [s] using (Real.sqrt_le_sqrt hr1 : Real.sqrt 1 ≤ Real.sqrt (r : ℝ))
      simpa [p08GammaReal, y, z, mul_assoc] using p08_gamma_scale y s hy hs1 hz1
  have hc1 := p08_gamma_comp x z hx hz hxy
  have hc2 := p08_gamma_comp (x + z) z (add_nonneg hx hz) hz hxzz
  have hgb : p08GammaReal (b : ℝ) u = x / (1 - x) := rfl
  have hgc : p08GammaReal (p08LowRankMatMulCost b r) u =
      (x + z + z) / (1 - (x + z + z)) := by
    simp only [p08GammaReal, hcost]
    ring
  rw [hgb, hgc]
  have hfac : 0 ≤ 1 + x / (1 - x) := by
    have hdx : 0 < 1 - x := by linarith
    positivity
  have hqfac : 0 ≤ 1 + p08GammaReal (r : ℝ) u * s := by
    have hdy : 0 < 1 - y := by linarith
    have hgr : 0 ≤ p08GammaReal (r : ℝ) u := by
      change 0 ≤ y / (1 - y)
      positivity
    nlinarith [mul_nonneg hgr hs0]
  have hzfac : 0 ≤ 1 + z / (1 - z) := by
    have hdz : 0 < 1 - z := by linarith
    positivity
  calc
    (1 + x / (1 - x)) * (1 + p08GammaReal (r : ℝ) u * s) ^ 2 ≤
        (1 + x / (1 - x)) * (1 + z / (1 - z)) ^ 2 := by
      gcongr
    _ ≤ (1 + (x + z) / (1 - (x + z))) * (1 + z / (1 - z)) := by
      simpa [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right hc1 hzfac
    _ ≤ 1 + (x + z + z) / (1 - (x + z + z)) := by
      convert hc2 using 1

private lemma p08_left_error_identity {b r : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r b)
    (N : P08RectMatrix b r)
    (Y : P08RectMatrix b r)
    (E₀ : P08RectMatrix r r) (E₁ : P08RectMatrix b r)
    (E₂ : P08RectMatrix b b) :
    ((p08RectMatMul X (p08RectMatMul M N + E₀) + E₁) *
        (p08RectTranspose Y) + E₂) -
      p08RectMatMul (p08RectMatMul X (p08RectMatMul M N))
        (p08RectTranspose Y) =
      p08RectMatMul (p08RectMatMul X E₀ + E₁) (p08RectTranspose Y) + E₂ := by
  simp only [p08_mul_eq, p08_transpose_eq]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

private lemma p08_right_error_identity {b r : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r b)
    (N : P08RectMatrix b r) (Y : P08RectMatrix b r)
    (E₀ : P08RectMatrix r r) (E₁ : P08RectMatrix r b)
    (E₂ : P08RectMatrix b b) :
    (p08RectMatMul X
        (p08RectMatMul (p08RectMatMul M N + E₀) (p08RectTranspose Y) + E₁) + E₂) -
      p08RectMatMul (p08RectMatMul X (p08RectMatMul M N))
        (p08RectTranspose Y) =
      p08RectMatMul X (p08RectMatMul E₀ (p08RectTranspose Y) + E₁) + E₂ := by
  simp only [p08_mul_eq, p08_transpose_eq]
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.add_mul]
  abel

private lemma p08_left_error_norm_le {b r : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r b)
    (N Y : P08RectMatrix b r)
    (E₀ : P08RectMatrix r r) (E₁ : P08RectMatrix b r)
    (E₂ : P08RectMatrix b b)
    (hX : p08OrthonormalColumns X) (hY : p08OrthonormalColumns Y) :
    p08FrobNorm
        (((p08RectMatMul X (p08RectMatMul M N + E₀) + E₁) *
            (p08RectTranspose Y) + E₂) -
          p08RectMatMul (p08RectMatMul X (p08RectMatMul M N))
            (p08RectTranspose Y)) ≤
      p08RectFrobNorm E₀ + p08RectFrobNorm E₁ + p08FrobNorm E₂ := by
  rw [p08_left_error_identity]
  calc
    p08FrobNorm
        (p08RectMatMul (p08RectMatMul X E₀ + E₁) (p08RectTranspose Y) + E₂) ≤
        p08RectFrobNorm
          (p08RectMatMul (p08RectMatMul X E₀ + E₁) (p08RectTranspose Y)) +
          p08FrobNorm E₂ := p08_norm_add_le _ _
    _ = p08RectFrobNorm (p08RectMatMul X E₀ + E₁) + p08FrobNorm E₂ := by
      rw [p08_norm_orth_right _ Y hY]
    _ ≤ (p08RectFrobNorm (p08RectMatMul X E₀) + p08RectFrobNorm E₁) +
        p08FrobNorm E₂ := by
      gcongr
      exact p08_norm_add_le _ _
    _ = p08RectFrobNorm E₀ + p08RectFrobNorm E₁ + p08FrobNorm E₂ := by
      rw [p08_norm_orth_left X E₀ hX]

private lemma p08_right_error_norm_le {b r : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r b)
    (N Y : P08RectMatrix b r)
    (E₀ : P08RectMatrix r r) (E₁ : P08RectMatrix r b)
    (E₂ : P08RectMatrix b b)
    (hX : p08OrthonormalColumns X) (hY : p08OrthonormalColumns Y) :
    p08FrobNorm
        ((p08RectMatMul X
            (p08RectMatMul (p08RectMatMul M N + E₀) (p08RectTranspose Y) + E₁) + E₂) -
          p08RectMatMul (p08RectMatMul X (p08RectMatMul M N))
            (p08RectTranspose Y)) ≤
      p08RectFrobNorm E₀ + p08RectFrobNorm E₁ + p08FrobNorm E₂ := by
  rw [p08_right_error_identity]
  calc
    p08FrobNorm
        (p08RectMatMul X (p08RectMatMul E₀ (p08RectTranspose Y) + E₁) + E₂) ≤
        p08RectFrobNorm
          (p08RectMatMul X (p08RectMatMul E₀ (p08RectTranspose Y) + E₁)) +
          p08FrobNorm E₂ := p08_norm_add_le _ _
    _ = p08RectFrobNorm (p08RectMatMul E₀ (p08RectTranspose Y) + E₁) +
        p08FrobNorm E₂ := by rw [p08_norm_orth_left X _ hX]
    _ ≤ (p08RectFrobNorm (p08RectMatMul E₀ (p08RectTranspose Y)) +
        p08RectFrobNorm E₁) + p08FrobNorm E₂ := by
      gcongr
      exact p08_norm_add_le _ _
    _ = p08RectFrobNorm E₀ + p08RectFrobNorm E₁ + p08FrobNorm E₂ := by
      rw [p08_norm_orth_right E₀ Y hY]

private lemma p08_three_error_bound
    (P g q gc e₀ e₁ e₂ : ℝ)
    (hP : 0 ≤ P)
    (hcost : (1 + g) * (1 + q) ^ 2 ≤ 1 + gc)
    (h₀ : e₀ ≤ g * P)
    (h₁ : e₁ ≤ q * (1 + g) * P)
    (h₂ : e₂ ≤ q * (1 + q) * (1 + g) * P) :
    e₀ + e₁ + e₂ ≤ gc * P := by
  have hcoeff : g + q * (1 + g) + q * (1 + q) * (1 + g) ≤ gc := by
    nlinarith [hcost]
  calc
    e₀ + e₁ + e₂ ≤ g * P + q * (1 + g) * P +
        q * (1 + q) * (1 + g) * P := by linarith
    _ = (g + q * (1 + g) + q * (1 + q) * (1 + g)) * P := by ring
    _ ≤ gc * P := mul_le_mul_of_nonneg_right hcoeff hP

private lemma p08_nat_le_nat_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hs1 : 1 ≤ Real.sqrt (r : ℝ) := by
      simpa using (Real.sqrt_le_sqrt hr1 : Real.sqrt 1 ≤ Real.sqrt (r : ℝ))
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) hs1

private lemma p08_gamma_stage_nonneg {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hvalid : p08LowRankMatMulCost b r * u < 1) :
    0 ≤ p08GammaReal (b : ℝ) u ∧
      0 ≤ p08GammaReal (r : ℝ) u ∧
      0 ≤ p08GammaReal (p08LowRankMatMulCost b r) u := by
  have hcostb : (b : ℝ) ≤ p08LowRankMatMulCost b r := by
    dsimp [p08LowRankMatMulCost]
    have hrs : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    linarith
  have hcostr : (r : ℝ) ≤ p08LowRankMatMulCost b r := by
    dsimp [p08LowRankMatMulCost]
    have hrs := p08_nat_le_nat_sqrt r
    have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
    linarith
  have hbvalid : (b : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcostb hu) hvalid
  have hrvalid : (r : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcostr hu) hvalid
  have hb0 : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hr0 : 0 ≤ (r : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hc0 : 0 ≤ p08LowRankMatMulCost b r * u := by
    exact mul_nonneg (le_trans (Nat.cast_nonneg _) hcostb) hu
  simp only [p08GammaReal]
  constructor
  · exact div_nonneg hb0 (by linarith)
  constructor
  · exact div_nonneg hr0 (by linarith)
  · exact div_nonneg hc0 (by linarith)

private lemma p08_trace_error_bound {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P08RectMatrix b r}
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (trace : P08LowRankMatMulTrace u XA YA XB YB) :
    p08FrobNorm
        (trace.result - p08MatMul
          (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        p08FrobNorm (p08LowRankMatrix XA YA) *
        p08FrobNorm (p08LowRankMatrix YB XB) := by
  let M : P08RectMatrix r b := p08RectTranspose YA
  let P : ℝ := p08RectFrobNorm M * p08RectFrobNorm YB
  let g : ℝ := p08GammaReal (b : ℝ) u
  let q : ℝ := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
  let gc : ℝ := p08GammaReal (p08LowRankMatMulCost b r) u
  have hP : 0 ≤ P := mul_nonneg (p08_norm_nonneg M) (p08_norm_nonneg YB)
  have hg : 0 ≤ g := (p08_gamma_stage_nonneg hu hvalid).1
  have hq : 0 ≤ q := mul_nonneg (p08_gamma_stage_nonneg hu hvalid).2.1
    (Real.sqrt_nonneg _)
  have hq1 : 0 ≤ 1 + q := by linarith
  have hcost : (1 + g) * (1 + q) ^ 2 ≤ 1 + gc :=
    p08_gamma_cost_bound hu hvalid
  have hA : p08FrobNorm (p08LowRankMatrix XA YA) = p08RectFrobNorm M := by
    change p08RectFrobNorm (p08RectMatMul XA M) = p08RectFrobNorm M
    exact p08_norm_orth_left XA M hXA
  have hB : p08FrobNorm (p08LowRankMatrix YB XB) = p08RectFrobNorm YB := by
    change p08RectFrobNorm (p08RectMatMul YB (p08RectTranspose XB)) =
      p08RectFrobNorm YB
    exact p08_norm_orth_right YB XB hXB
  have hexact :
      p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
        p08RectMatMul (p08RectMatMul XA (p08RectMatMul M YB))
          (p08RectTranspose XB) := by
    change (XA * YA.transpose) * (YB * XB.transpose) =
      (XA * (YA.transpose * YB)) * XB.transpose
    simp only [Matrix.mul_assoc]
  cases trace with
  | leftAssociated middleStage leftStage finalStage =>
      have hE₀ : p08RectFrobNorm middleStage.error ≤ g * P := by
        simpa only [g, P, M, mul_assoc] using middleStage.error_le
      have hW : p08RectFrobNorm middleStage.result ≤ (1 + g) * P := by
        calc
          p08RectFrobNorm middleStage.result =
              p08RectFrobNorm (p08RectMatMul M YB + middleStage.error) := rfl
          _ ≤ p08RectFrobNorm (p08RectMatMul M YB) +
              p08RectFrobNorm middleStage.error := p08_norm_add_le _ _
          _ ≤ P + g * P :=
            add_le_add (p08_norm_mul_le M YB) hE₀
          _ = (1 + g) * P := by ring
      have hE₁ : p08RectFrobNorm leftStage.error ≤
          q * p08RectFrobNorm middleStage.result := by
        calc
          p08RectFrobNorm leftStage.error ≤
              p08GammaReal (r : ℝ) u * p08RectFrobNorm XA *
                p08RectFrobNorm middleStage.result := leftStage.error_le
          _ = q * p08RectFrobNorm middleStage.result := by
            rw [p08_norm_orth_sqrt XA hXA]
      have hE₁' : p08RectFrobNorm leftStage.error ≤ q * (1 + g) * P := by
        calc
          _ ≤ q * p08RectFrobNorm middleStage.result := hE₁
          _ ≤ q * ((1 + g) * P) := mul_le_mul_of_nonneg_left hW hq
          _ = q * (1 + g) * P := by ring
      have hL : p08RectFrobNorm leftStage.result ≤
          (1 + q) * (1 + g) * P := by
        calc
          p08RectFrobNorm leftStage.result =
              p08RectFrobNorm
                (p08RectMatMul XA middleStage.result + leftStage.error) := rfl
          _ ≤ p08RectFrobNorm (p08RectMatMul XA middleStage.result) +
              p08RectFrobNorm leftStage.error := p08_norm_add_le _ _
          _ = p08RectFrobNorm middleStage.result +
              p08RectFrobNorm leftStage.error := by
                rw [p08_norm_orth_left XA _ hXA]
          _ ≤ p08RectFrobNorm middleStage.result +
              q * p08RectFrobNorm middleStage.result :=
                add_le_add_right hE₁ _
          _ = (1 + q) * p08RectFrobNorm middleStage.result := by ring
          _ ≤ (1 + q) * ((1 + g) * P) :=
            mul_le_mul_of_nonneg_left hW hq1
          _ = (1 + q) * (1 + g) * P := by ring
      have hE₂ : p08FrobNorm finalStage.error ≤
          q * p08RectFrobNorm leftStage.result := by
        calc
          p08FrobNorm finalStage.error ≤
              p08GammaReal (r : ℝ) u * p08RectFrobNorm leftStage.result *
                p08RectFrobNorm (p08RectTranspose XB) := finalStage.error_le
          _ = q * p08RectFrobNorm leftStage.result := by
            rw [p08_norm_transpose XB, p08_norm_orth_sqrt XB hXB]
            dsimp [q]
            ring
      have hE₂' : p08FrobNorm finalStage.error ≤
          q * (1 + q) * (1 + g) * P := by
        calc
          _ ≤ q * p08RectFrobNorm leftStage.result := hE₂
          _ ≤ q * ((1 + q) * (1 + g) * P) :=
            mul_le_mul_of_nonneg_left hL hq
          _ = q * (1 + q) * (1 + g) * P := by ring
      have herr := p08_left_error_norm_le XA M YB XB
        middleStage.error leftStage.error finalStage.error hXA hXB
      have hsum := p08_three_error_bound P g q gc
        (p08RectFrobNorm middleStage.error)
        (p08RectFrobNorm leftStage.error)
        (p08FrobNorm finalStage.error)
        hP hcost hE₀ hE₁' hE₂'
      change p08FrobNorm (finalStage.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤ _
      rw [hexact]
      calc
        _ ≤ p08RectFrobNorm middleStage.error +
            p08RectFrobNorm leftStage.error + p08FrobNorm finalStage.error := herr
        _ ≤ gc * P := hsum
        _ = p08GammaReal (p08LowRankMatMulCost b r) u *
            p08FrobNorm (p08LowRankMatrix XA YA) *
            p08FrobNorm (p08LowRankMatrix YB XB) := by
          rw [hA, hB]
          dsimp [gc, P]
          ring

  | rightAssociated middleStage rightStage finalStage =>
      have hE₀ : p08RectFrobNorm middleStage.error ≤ g * P := by
        simpa only [g, P, M, mul_assoc] using middleStage.error_le
      have hW : p08RectFrobNorm middleStage.result ≤ (1 + g) * P := by
        calc
          p08RectFrobNorm middleStage.result =
              p08RectFrobNorm (p08RectMatMul M YB + middleStage.error) := rfl
          _ ≤ p08RectFrobNorm (p08RectMatMul M YB) +
              p08RectFrobNorm middleStage.error := p08_norm_add_le _ _
          _ ≤ P + g * P :=
            add_le_add (p08_norm_mul_le M YB) hE₀
          _ = (1 + g) * P := by ring
      have hE₁ : p08RectFrobNorm rightStage.error ≤
          q * p08RectFrobNorm middleStage.result := by
        calc
          p08RectFrobNorm rightStage.error ≤
              p08GammaReal (r : ℝ) u * p08RectFrobNorm middleStage.result *
                p08RectFrobNorm (p08RectTranspose XB) := rightStage.error_le
          _ = q * p08RectFrobNorm middleStage.result := by
            rw [p08_norm_transpose XB, p08_norm_orth_sqrt XB hXB]
            dsimp [q]
            ring
      have hE₁' : p08RectFrobNorm rightStage.error ≤ q * (1 + g) * P := by
        calc
          _ ≤ q * p08RectFrobNorm middleStage.result := hE₁
          _ ≤ q * ((1 + g) * P) := mul_le_mul_of_nonneg_left hW hq
          _ = q * (1 + g) * P := by ring
      have hR : p08RectFrobNorm rightStage.result ≤
          (1 + q) * (1 + g) * P := by
        calc
          p08RectFrobNorm rightStage.result =
              p08RectFrobNorm
                (p08RectMatMul middleStage.result (p08RectTranspose XB) +
                  rightStage.error) := rfl
          _ ≤ p08RectFrobNorm
              (p08RectMatMul middleStage.result (p08RectTranspose XB)) +
              p08RectFrobNorm rightStage.error := p08_norm_add_le _ _
          _ = p08RectFrobNorm middleStage.result +
              p08RectFrobNorm rightStage.error := by
                rw [p08_norm_orth_right _ XB hXB]
          _ ≤ p08RectFrobNorm middleStage.result +
              q * p08RectFrobNorm middleStage.result :=
                add_le_add_right hE₁ _
          _ = (1 + q) * p08RectFrobNorm middleStage.result := by ring
          _ ≤ (1 + q) * ((1 + g) * P) :=
            mul_le_mul_of_nonneg_left hW hq1
          _ = (1 + q) * (1 + g) * P := by ring
      have hE₂ : p08FrobNorm finalStage.error ≤
          q * p08RectFrobNorm rightStage.result := by
        calc
          p08FrobNorm finalStage.error ≤
              p08GammaReal (r : ℝ) u * p08RectFrobNorm XA *
                p08RectFrobNorm rightStage.result := finalStage.error_le
          _ = q * p08RectFrobNorm rightStage.result := by
            rw [p08_norm_orth_sqrt XA hXA]
      have hE₂' : p08FrobNorm finalStage.error ≤
          q * (1 + q) * (1 + g) * P := by
        calc
          _ ≤ q * p08RectFrobNorm rightStage.result := hE₂
          _ ≤ q * ((1 + q) * (1 + g) * P) :=
            mul_le_mul_of_nonneg_left hR hq
          _ = q * (1 + q) * (1 + g) * P := by ring
      have herr := p08_right_error_norm_le XA M YB XB
        middleStage.error rightStage.error finalStage.error hXA hXB
      have hsum := p08_three_error_bound P g q gc
        (p08RectFrobNorm middleStage.error)
        (p08RectFrobNorm rightStage.error)
        (p08FrobNorm finalStage.error)
        hP hcost hE₀ hE₁' hE₂'
      change p08FrobNorm (finalStage.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤ _
      rw [hexact]
      calc
        _ ≤ p08RectFrobNorm middleStage.error +
            p08RectFrobNorm rightStage.error + p08FrobNorm finalStage.error := herr
        _ ≤ gc * P := hsum
        _ = p08GammaReal (p08LowRankMatMulCost b r) u *
            p08FrobNorm (p08LowRankMatrix XA YA) *
            p08FrobNorm (p08LowRankMatrix YB XB) := by
          rw [hA, hB]
          dsimp [gc, P]
          ring

private lemma p08_approx_product_identity {b : ℕ}
    (A B EA EB : P08Matrix b) :
    p08MatMul (A + EA) (B + EB) - p08MatMul A B =
      p08MatMul EA B + p08MatMul A EB + p08MatMul EA EB := by
  change (A + EA) * (B + EB) - A * B = EA * B + A * EB + EA * EB
  simp only [Matrix.add_mul, Matrix.mul_add]
  abel

private lemma p08_approx_product_norm_le {b : ℕ}
    (A B EA EB : P08Matrix b) :
    p08FrobNorm (p08MatMul (A + EA) (B + EB) - p08MatMul A B) ≤
      p08FrobNorm EA * p08FrobNorm B +
        p08FrobNorm A * p08FrobNorm EB +
        p08FrobNorm EA * p08FrobNorm EB := by
  rw [p08_approx_product_identity]
  calc
    p08FrobNorm (p08MatMul EA B + p08MatMul A EB + p08MatMul EA EB) ≤
        p08FrobNorm (p08MatMul EA B + p08MatMul A EB) +
          p08FrobNorm (p08MatMul EA EB) := p08_norm_add_le _ _
    _ ≤ p08FrobNorm (p08MatMul EA B) + p08FrobNorm (p08MatMul A EB) +
          p08FrobNorm (p08MatMul EA EB) := by
      gcongr
      exact p08_norm_add_le _ _
    _ ≤ p08FrobNorm EA * p08FrobNorm B +
          p08FrobNorm A * p08FrobNorm EB +
          p08FrobNorm EA * p08FrobNorm EB := by
      gcongr <;> exact p08_norm_mul_le _ _

private lemma p08_perturbation_bound {b : ℕ}
    (A B EA EB C : P08Matrix b) (g α β : ℝ)
    (hg : 0 ≤ g) (hα : 0 ≤ α)
    (hEA : p08FrobNorm EA ≤ α)
    (hEB : p08FrobNorm EB ≤ β)
    (hC : p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) ≤
      g * p08FrobNorm (A + EA) * p08FrobNorm (B + EB)) :
    p08FrobNorm (C - p08MatMul A B) ≤
      g * p08FrobNorm A * p08FrobNorm B +
        (1 + g) * (α * p08FrobNorm B + p08FrobNorm A * β + α * β) := by
  have hβ : 0 ≤ β := le_trans (p08_norm_nonneg EB) hEB
  have hAn : p08FrobNorm (A + EA) ≤ p08FrobNorm A + α := by
    exact (p08_norm_add_le A EA).trans (add_le_add_right hEA _)
  have hBn : p08FrobNorm (B + EB) ≤ p08FrobNorm B + β := by
    exact (p08_norm_add_le B EB).trans (add_le_add_right hEB _)
  have hA0 : 0 ≤ p08FrobNorm A + α :=
    add_nonneg (p08_norm_nonneg A) hα
  have hC' : p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) ≤
      g * (p08FrobNorm A + α) * (p08FrobNorm B + β) := by
    calc
      _ ≤ g * p08FrobNorm (A + EA) * p08FrobNorm (B + EB) := hC
      _ ≤ g * (p08FrobNorm A + α) * p08FrobNorm (B + EB) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAn hg)
          (p08_norm_nonneg (B + EB))
      _ ≤ g * (p08FrobNorm A + α) * (p08FrobNorm B + β) :=
        mul_le_mul_of_nonneg_left hBn (mul_nonneg hg hA0)
  have hPert :
      p08FrobNorm (p08MatMul (A + EA) (B + EB) - p08MatMul A B) ≤
        α * p08FrobNorm B + p08FrobNorm A * β + α * β := by
    have h₁ : p08FrobNorm EA * p08FrobNorm B ≤ α * p08FrobNorm B :=
      mul_le_mul_of_nonneg_right hEA (p08_norm_nonneg B)
    have h₂ : p08FrobNorm A * p08FrobNorm EB ≤ p08FrobNorm A * β :=
      mul_le_mul_of_nonneg_left hEB (p08_norm_nonneg A)
    have h₃ : p08FrobNorm EA * p08FrobNorm EB ≤ α * β := by
      calc
        _ ≤ α * p08FrobNorm EB :=
          mul_le_mul_of_nonneg_right hEA (p08_norm_nonneg EB)
        _ ≤ α * β := mul_le_mul_of_nonneg_left hEB hα
    exact (p08_approx_product_norm_le A B EA EB).trans
      (add_le_add (add_le_add h₁ h₂) h₃)
  have hdecomp : C - p08MatMul A B =
      (C - p08MatMul (A + EA) (B + EB)) +
      (p08MatMul (A + EA) (B + EB) - p08MatMul A B) := by abel
  rw [hdecomp]
  calc
    p08FrobNorm
        ((C - p08MatMul (A + EA) (B + EB)) +
          (p08MatMul (A + EA) (B + EB) - p08MatMul A B)) ≤
      p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) +
        p08FrobNorm (p08MatMul (A + EA) (B + EB) - p08MatMul A B) :=
        p08_norm_add_le _ _
    _ ≤ g * (p08FrobNorm A + α) * (p08FrobNorm B + β) +
        (α * p08FrobNorm B + p08FrobNorm A * β + α * β) :=
      add_le_add hC' hPert
    _ = g * p08FrobNorm A * p08FrobNorm B +
        (1 + g) * (α * p08FrobNorm B + p08FrobNorm A * β + α * β) := by
      ring

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
  constructor
  · exact p08_trace_error_bound run.unitRoundoff_nonneg run.gamma_valid
      run.xA_orthonormal run.xB_orthonormal run.trace
  · let gammaC := p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
    have hg : 0 ≤ gammaC :=
      (p08_gamma_stage_nonneg run.unitRoundoff_nonneg run.gamma_valid).2.2
    have hα : 0 ≤ run.epsilon * run.betaA :=
      le_trans (p08_norm_nonneg run.approximationErrorA)
        run.approximationErrorA_le
    have hC :
        p08FrobNorm
          (run.trace.result -
            p08MatMul (run.A + run.approximationErrorA)
              (run.B + run.approximationErrorB)) ≤
          gammaC * p08FrobNorm (run.A + run.approximationErrorA) *
            p08FrobNorm (run.B + run.approximationErrorB) := by
      rw [← run.approximationA_eq, ← run.approximationB_eq]
      exact p08_trace_error_bound run.unitRoundoff_nonneg run.gamma_valid
        run.xA_orthonormal run.xB_orthonormal run.trace
    have h := p08_perturbation_bound run.A run.B
      run.approximationErrorA run.approximationErrorB run.trace.result
      gammaC (run.epsilon * run.betaA) (run.epsilon * run.betaB)
      hg hα run.approximationErrorA_le run.approximationErrorB_le hC
    convert h using 1
    ring

end VSCLReuse

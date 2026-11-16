import VSCLReuse.P08.Definitions
import NumStability.Source.Higham.Chapter19.Sensitivity.Closure

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius

private lemma p08_norm_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = NumStability.frobNormRect A := rfl

private lemma p08_mul_eq {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectMatMul A B = NumStability.rectMatMul A B := rfl

private lemma p08_norm_mul {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectFrobNorm (p08RectMatMul A B) ≤
      p08RectFrobNorm A * p08RectFrobNorm B := by
  exact NumStability.frobNormRect_rectMatMul_le A B

private lemma p08_norm_add {m n : ℕ}
    (A B : P08RectMatrix m n) :
    p08RectFrobNorm (A + B) ≤ p08RectFrobNorm A + p08RectFrobNorm B := by
  exact NumStability.frobNormRect_add_le A B

private lemma p08_norm_nonneg {m n : ℕ} (A : P08RectMatrix m n) :
    0 ≤ p08RectFrobNorm A := NumStability.frobNormRect_nonneg A

private lemma p08_norm_transpose {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  exact NumStability.frobNormRect_finiteTranspose A

private lemma p08_orthonormal_gram {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    NumStability.GramSchmidtOrthonormalColumns X := by
  intro i j
  simpa [NumStability.rectangularGram, NumStability.matMulRect,
    NumStability.finiteTranspose, NumStability.idMatrix] using hX i j

private lemma p08_norm_mul_orth_left {b r p : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r p)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul X M) = p08RectFrobNorm M := by
  exact NumStability.H19Sensitivity.frobNormRect_rectMatMul_eq_of_orthonormal_left
    X M (p08_orthonormal_gram X hX)

private lemma p08_norm_mul_orth_right {b r p : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix p r)
    (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm (p08RectMatMul M (p08RectTranspose X)) =
      p08RectFrobNorm M := by
  calc
    p08RectFrobNorm (p08RectMatMul M (p08RectTranspose X)) =
        p08RectFrobNorm (p08RectTranspose (p08RectMatMul X (p08RectTranspose M))) := by
          congr 1
          ext i j
          simp [p08RectMatMul, p08RectTranspose, mul_comm]
    _ = p08RectFrobNorm (p08RectMatMul X (p08RectTranspose M)) :=
      p08_norm_transpose _
    _ = p08RectFrobNorm (p08RectTranspose M) := p08_norm_mul_orth_left X _ hX
    _ = p08RectFrobNorm M := p08_norm_transpose _

private lemma p08_gamma_one_add (x u : ℝ) (h : x * u < 1) :
    1 + p08GammaReal x u = (1 - x * u)⁻¹ := by
  unfold p08GammaReal
  have hd : 1 - x * u ≠ 0 := ne_of_gt (sub_pos.mpr h)
  field_simp
  ring

private lemma p08_gamma_nonneg (x u : ℝ) (hx : 0 ≤ x) (hu : 0 ≤ u)
    (h : x * u < 1) : 0 ≤ p08GammaReal x u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hx hu) (le_of_lt (sub_pos.mpr h))

private lemma p08_gamma_compose (x y u : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u)
    (h : (x + y) * u < 1) :
    (1 + p08GammaReal x u) * (1 + p08GammaReal y u) ≤
      1 + p08GammaReal (x + y) u := by
  have hxu : x * u < 1 := by nlinarith [mul_nonneg hy hu]
  have hyu : y * u < 1 := by nlinarith [mul_nonneg hx hu]
  have hdx : 0 < 1 - x * u := sub_pos.mpr hxu
  have hdy : 0 < 1 - y * u := sub_pos.mpr hyu
  have hdxy : 0 < 1 - (x + y) * u := sub_pos.mpr h
  rw [p08_gamma_one_add _ _ hxu, p08_gamma_one_add _ _ hyu,
      p08_gamma_one_add _ _ h]
  have hbase : 1 / ((1 - x * u) * (1 - y * u)) ≤
      1 / (1 - (x + y) * u) := by
    apply (div_le_div_iff₀ (mul_pos hdx hdy) hdxy).2
    nlinarith [mul_nonneg (mul_nonneg hx hu) (mul_nonneg hy hu)]
  rw [← one_div_mul_one_div] at hbase
  simpa only [one_div] using hbase

private lemma p08_r_le_rsqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => simp
  | succ r =>
    have hr : (1 : ℝ) ≤ (↑(r + 1) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
    have hs : (1 : ℝ) ≤ Real.sqrt (↑(r + 1) : ℝ) := Real.one_le_sqrt.mpr hr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ↑(r+1) by positivity) (sub_nonneg.mpr hs)]

private lemma p08_gamma_scaled (r u : ℝ) (s : ℝ)
    (hr : 0 ≤ r) (hu : 0 ≤ u) (hs : 0 ≤ s) (hrs : r ≤ r * s)
    (h : (r * s) * u < 1) :
    p08GammaReal r u * s ≤ p08GammaReal (r * s) u := by
  have hru : r * u < 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hu]
  have hdr : 0 < 1 - r * u := sub_pos.mpr hru
  have hds : 0 < 1 - (r * s) * u := sub_pos.mpr h
  have hq : 0 ≤ (r * s) * u := by positivity
  have hpq : r * u ≤ (r * s) * u := mul_le_mul_of_nonneg_right hrs hu
  unfold p08GammaReal
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hdr hds).2
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hpq)]

private lemma p08_gamma_budget (b r u : ℝ) (s : ℝ)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hrs : r ≤ r * s)
    (h : (b + 2 * r * s) * u < 1) :
    p08GammaReal b u +
      2 * (p08GammaReal r u * s) +
      (p08GammaReal r u * s)^2 +
      2 * p08GammaReal b u * (p08GammaReal r u * s) +
      p08GammaReal b u * (p08GammaReal r u * s)^2 ≤
      p08GammaReal (b + 2 * r * s) u := by
  let t := r * s
  have ht : 0 ≤ t := mul_nonneg hr hs
  have hbt : (b + t) * u < 1 := by nlinarith [mul_nonneg ht hu]
  have htt : (t + t) * u < 1 := by nlinarith [mul_nonneg hb hu]
  have htvalid : t * u < 1 := by nlinarith [mul_nonneg hb hu, mul_nonneg ht hu]
  have hbvalid : b * u < 1 := by nlinarith [mul_nonneg ht hu]
  have hgr : 0 ≤ p08GammaReal r u :=
    p08_gamma_nonneg r u hr hu (by nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hu])
  have hgb : 0 ≤ p08GammaReal b u := p08_gamma_nonneg b u hb hu hbvalid
  have hgscaled : p08GammaReal r u * s ≤ p08GammaReal t u := by
    exact p08_gamma_scaled r u s hr hu hs hrs htvalid
  have hgt : 0 ≤ p08GammaReal t u := p08_gamma_nonneg t u ht hu htvalid
  have h1 : (1 + p08GammaReal b u) * (1 + p08GammaReal t u) ≤
      1 + p08GammaReal (b + t) u := p08_gamma_compose b t u hb ht hu hbt
  have h2 : (1 + p08GammaReal (b + t) u) *
      (1 + p08GammaReal t u) ≤ 1 + p08GammaReal (b + t + t) u :=
    p08_gamma_compose (b+t) t u (by positivity) ht hu (by nlinarith [h])
  have hprod :
      (1 + p08GammaReal b u) * (1 + p08GammaReal t u)^2 ≤
        1 + p08GammaReal (b + t + t) u := by
    calc
      _ = ((1 + p08GammaReal b u) * (1 + p08GammaReal t u)) *
          (1 + p08GammaReal t u) := by ring
      _ ≤ (1 + p08GammaReal (b+t) u) *
          (1 + p08GammaReal t u) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ _ := h2
  have hscaled :
      (1 + p08GammaReal b u) * (1 + p08GammaReal r u * s)^2 ≤
        (1 + p08GammaReal b u) * (1 + p08GammaReal t u)^2 := by
    gcongr
  dsimp [t] at hprod hscaled
  calc
    _ = (1 + p08GammaReal b u) *
        (1 + p08GammaReal r u * s)^2 - 1 := by ring
    _ ≤ (1 + p08GammaReal (b + r * s + r * s) u) - 1 :=
      sub_le_sub_right (hscaled.trans hprod) 1
    _ = _ := by
      have heq : b + r * s + r * s = b + 2 * r * s := by ring
      rw [heq]
      ring

private lemma p08_rect_mul_matrix {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectMatMul A B = A * B := by
  ext i j
  simp [p08RectMatMul, Matrix.mul_apply]

private lemma p08_sq_mul_matrix {n : ℕ} (A B : P08Matrix n) :
    p08MatMul A B = A * B := by
  ext i j
  simp [p08MatMul, Matrix.mul_apply]

private lemma p08_norm_sq {n : ℕ} (A : P08Matrix n) :
    p08FrobNorm A = p08RectFrobNorm A := rfl

private lemma p08_left_error_norm {b r : ℕ}
    (XA YA XB YB : P08RectMatrix b r)
    (EM : P08RectMatrix r r) (EL : P08RectMatrix b r)
    (EF : P08Matrix b)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB) :
    p08FrobNorm
      (((XA * ((p08RectTranspose YA) * YB + EM) + EL) *
          (p08RectTranspose XB) + EF) -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      p08RectFrobNorm EM + p08RectFrobNorm EL + p08FrobNorm EF := by
  have heq :
      ((XA * ((p08RectTranspose YA) * YB + EM) + EL) *
          (p08RectTranspose XB) + EF) -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
      (XA * EM + EL) * p08RectTranspose XB + EF := by
    rw [p08_sq_mul_matrix]
    simp only [p08LowRankMatrix, p08_rect_mul_matrix]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [heq]
  change p08RectFrobNorm ((XA * EM + EL) * p08RectTranspose XB + EF) ≤
    p08RectFrobNorm EM + p08RectFrobNorm EL + p08RectFrobNorm EF
  calc
    _ ≤ p08RectFrobNorm ((XA * EM + EL) * p08RectTranspose XB) +
          p08RectFrobNorm EF := p08_norm_add _ _
    _ = p08RectFrobNorm (XA * EM + EL) + p08RectFrobNorm EF := by
      rw [← p08_rect_mul_matrix, p08_norm_mul_orth_right XB _ hXB]
    _ ≤ (p08RectFrobNorm (XA * EM) + p08RectFrobNorm EL) +
          p08RectFrobNorm EF := by
      gcongr
      exact p08_norm_add _ _
    _ = _ := by rw [← p08_rect_mul_matrix, p08_norm_mul_orth_left XA _ hXA]

private lemma p08_right_error_norm {b r : ℕ}
    (XA YA XB YB : P08RectMatrix b r)
    (EM : P08RectMatrix r r) (ER : P08RectMatrix r b)
    (EF : P08Matrix b)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB) :
    p08FrobNorm
      (XA * (((p08RectTranspose YA) * YB + EM) *
            (p08RectTranspose XB) + ER) + EF -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      p08RectFrobNorm EM + p08RectFrobNorm ER + p08FrobNorm EF := by
  have heq :
      XA * (((p08RectTranspose YA) * YB + EM) *
            (p08RectTranspose XB) + ER) + EF -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
      XA * (EM * p08RectTranspose XB + ER) + EF := by
    rw [p08_sq_mul_matrix]
    simp only [p08LowRankMatrix, p08_rect_mul_matrix]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [heq]
  change p08RectFrobNorm (XA * (EM * p08RectTranspose XB + ER) + EF) ≤
    p08RectFrobNorm EM + p08RectFrobNorm ER + p08RectFrobNorm EF
  calc
    _ ≤ p08RectFrobNorm (XA * (EM * p08RectTranspose XB + ER)) +
          p08RectFrobNorm EF := p08_norm_add _ _
    _ = p08RectFrobNorm (EM * p08RectTranspose XB + ER) +
          p08RectFrobNorm EF := by
      rw [← p08_rect_mul_matrix, p08_norm_mul_orth_left XA _ hXA]
    _ ≤ (p08RectFrobNorm (EM * p08RectTranspose XB) +
          p08RectFrobNorm ER) + p08RectFrobNorm EF := by
      gcongr
      exact p08_norm_add _ _
    _ = _ := by rw [← p08_rect_mul_matrix, p08_norm_mul_orth_right XB _ hXB]

private lemma p08_three_error_bound
    (m e l f P gb q gc : ℝ)
    (hm : m ≤ P) (he : e ≤ gb * P)
    (hl : l ≤ q * (m + e))
    (hf : f ≤ q * (m + e + l))
    (hP : 0 ≤ P) (hgb : 0 ≤ gb) (hq : 0 ≤ q)
    (hbudget : gb + 2*q + q^2 + 2*gb*q + gb*q^2 ≤ gc) :
    e + l + f ≤ gc * P := by
  have hme : m + e ≤ (1 + gb) * P := by nlinarith [hm, he]
  have hl' : l ≤ q * (1 + gb) * P := by
    calc
      l ≤ q * (m + e) := hl
      _ ≤ q * ((1 + gb) * P) := mul_le_mul_of_nonneg_left hme hq
      _ = _ := by ring
  have hmel : m + e + l ≤ (1 + q) * (1 + gb) * P := by
    nlinarith [hme, hl']
  have hf' : f ≤ q * (1 + q) * (1 + gb) * P := by
    calc
      f ≤ q * (m + e + l) := hf
      _ ≤ q * ((1 + q) * (1 + gb) * P) :=
        mul_le_mul_of_nonneg_left hmel hq
      _ = _ := by ring
  have hsum : e + l + f ≤
      (gb + 2*q + q^2 + 2*gb*q + gb*q^2) * P := by
    nlinarith [he, hl', hf']
  exact hsum.trans (mul_le_mul_of_nonneg_right hbudget hP)

private lemma p08_left_stage_bound {b r : ℕ} (u : ℝ)
    (XA YA XB YB : P08RectMatrix b r)
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (middleStage : P08RoundedMatMulStage r b r u
      (p08RectTranspose YA) YB)
    (leftStage : P08RoundedMatMulStage b r r u XA middleStage.result)
    (finalStage : P08RoundedMatMulStage b r b u leftStage.result
      (p08RectTranspose XB)) :
    p08FrobNorm (finalStage.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        p08FrobNorm (p08LowRankMatrix XA YA) *
          p08FrobNorm (p08LowRankMatrix YB XB) := by
  let s : ℝ := Real.sqrt (r : ℝ)
  let q : ℝ := p08GammaReal (r : ℝ) u * s
  let gb : ℝ := p08GammaReal (b : ℝ) u
  let gc : ℝ := p08GammaReal (p08LowRankMatMulCost b r) u
  let M : P08RectMatrix r r :=
    p08RectMatMul (p08RectTranspose YA) YB
  let P : ℝ := p08FrobNorm (p08LowRankMatrix XA YA) *
    p08FrobNorm (p08LowRankMatrix YB XB)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hrs : (r : ℝ) ≤ (r : ℝ) * s := p08_r_le_rsqrt r
  have hcost : ((b : ℝ) + 2 * (r : ℝ) * s) * u < 1 := by
    simpa [p08LowRankMatMulCost, s] using hvalid
  have hrvalid : (r : ℝ) * u < 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hu,
      mul_nonneg (show (0 : ℝ) ≤ b by positivity) hu,
      mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ r by positivity) hs) hu]
  have hbvalid : (b : ℝ) * u < 1 := by
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ r by positivity) hs) hu]
  have hq : 0 ≤ q := mul_nonneg
    (p08_gamma_nonneg _ _ (by positivity) hu hrvalid) hs
  have hgb : 0 ≤ gb := p08_gamma_nonneg _ _ (by positivity) hu hbvalid
  have hP : 0 ≤ P := mul_nonneg (p08_norm_nonneg _) (p08_norm_nonneg _)
  have hbudget : gb + 2*q + q^2 + 2*gb*q + gb*q^2 ≤ gc := by
    exact p08_gamma_budget (b : ℝ) (r : ℝ) u s
      (by positivity) (by positivity) hu hs hrs hcost
  have hXA_norm : p08RectFrobNorm XA = s := by
    exact NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
      (p08_orthonormal_gram XA hXA)
  have hXB_norm : p08RectFrobNorm (p08RectTranspose XB) = s := by
    rw [p08_norm_transpose]
    exact NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
      (p08_orthonormal_gram XB hXB)
  have hYA : p08RectFrobNorm (p08RectTranspose YA) =
      p08FrobNorm (p08LowRankMatrix XA YA) := by
    symm
    exact p08_norm_mul_orth_left XA _ hXA
  have hYB : p08RectFrobNorm YB =
      p08FrobNorm (p08LowRankMatrix YB XB) := by
    symm
    exact p08_norm_mul_orth_right XB YB hXB
  have hM : p08RectFrobNorm M ≤ P := by
    calc
      p08RectFrobNorm M ≤
          p08RectFrobNorm (p08RectTranspose YA) * p08RectFrobNorm YB :=
        p08_norm_mul _ _
      _ = P := by rw [hYA, hYB]
  have hEM : p08RectFrobNorm middleStage.error ≤ gb * P := by
    simpa only [gb, P, hYA, hYB, mul_assoc] using middleStage.error_le
  have hMiddle : p08RectFrobNorm middleStage.result ≤
      p08RectFrobNorm M + p08RectFrobNorm middleStage.error := by
    exact p08_norm_add _ _
  have hEL : p08RectFrobNorm leftStage.error ≤
      q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error) := by
    calc
      p08RectFrobNorm leftStage.error ≤
          p08GammaReal (r : ℝ) u * p08RectFrobNorm XA *
            p08RectFrobNorm middleStage.result := leftStage.error_le
      _ = q * p08RectFrobNorm middleStage.result := by rw [hXA_norm]
      _ ≤ q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error) :=
        mul_le_mul_of_nonneg_left hMiddle hq
  have hLeft : p08RectFrobNorm leftStage.result ≤
      p08RectFrobNorm M + p08RectFrobNorm middleStage.error +
        p08RectFrobNorm leftStage.error := by
    calc
      p08RectFrobNorm leftStage.result ≤
          p08RectFrobNorm (p08RectMatMul XA middleStage.result) +
            p08RectFrobNorm leftStage.error := p08_norm_add _ _
      _ = p08RectFrobNorm middleStage.result +
            p08RectFrobNorm leftStage.error := by
        rw [p08_norm_mul_orth_left XA _ hXA]
      _ ≤ _ := by linarith [hMiddle]
  have hEF : p08FrobNorm finalStage.error ≤
      q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error +
        p08RectFrobNorm leftStage.error) := by
    calc
      p08FrobNorm finalStage.error ≤
          p08GammaReal (r : ℝ) u * p08RectFrobNorm leftStage.result *
            p08RectFrobNorm (p08RectTranspose XB) := finalStage.error_le
      _ = q * p08RectFrobNorm leftStage.result := by rw [hXB_norm]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hLeft hq
  have htotal := p08_three_error_bound
    (p08RectFrobNorm M) (p08RectFrobNorm middleStage.error)
    (p08RectFrobNorm leftStage.error) (p08FrobNorm finalStage.error)
    P gb q gc hM hEM hEL hEF hP hgb hq hbudget
  have hnorm := p08_left_error_norm XA YA XB YB
    middleStage.error leftStage.error finalStage.error hXA hXB
  have hresult :
      finalStage.result =
        (XA * ((p08RectTranspose YA) * YB + middleStage.error) +
          leftStage.error) * p08RectTranspose XB + finalStage.error := by
    simp only [P08RoundedMatMulStage.result, p08_rect_mul_matrix]
  rw [hresult]
  calc
    _ ≤ p08RectFrobNorm middleStage.error + p08RectFrobNorm leftStage.error +
          p08FrobNorm finalStage.error := hnorm
    _ ≤ gc * P := htotal
    _ = _ := by dsimp [gc, P]; ring
private lemma p08_right_stage_bound {b r : ℕ} (u : ℝ)
    (XA YA XB YB : P08RectMatrix b r)
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (middleStage : P08RoundedMatMulStage r b r u
      (p08RectTranspose YA) YB)
    (rightStage : P08RoundedMatMulStage r r b u middleStage.result
      (p08RectTranspose XB))
    (finalStage : P08RoundedMatMulStage b r b u XA rightStage.result) :
    p08FrobNorm (finalStage.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        p08FrobNorm (p08LowRankMatrix XA YA) *
          p08FrobNorm (p08LowRankMatrix YB XB) := by
  let s : ℝ := Real.sqrt (r : ℝ)
  let q : ℝ := p08GammaReal (r : ℝ) u * s
  let gb : ℝ := p08GammaReal (b : ℝ) u
  let gc : ℝ := p08GammaReal (p08LowRankMatMulCost b r) u
  let M : P08RectMatrix r r :=
    p08RectMatMul (p08RectTranspose YA) YB
  let P : ℝ := p08FrobNorm (p08LowRankMatrix XA YA) *
    p08FrobNorm (p08LowRankMatrix YB XB)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hrs : (r : ℝ) ≤ (r : ℝ) * s := p08_r_le_rsqrt r
  have hcost : ((b : ℝ) + 2 * (r : ℝ) * s) * u < 1 := by
    simpa [p08LowRankMatMulCost, s] using hvalid
  have hrvalid : (r : ℝ) * u < 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrs) hu,
      mul_nonneg (show (0 : ℝ) ≤ b by positivity) hu,
      mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ r by positivity) hs) hu]
  have hbvalid : (b : ℝ) * u < 1 := by
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ r by positivity) hs) hu]
  have hq : 0 ≤ q := mul_nonneg
    (p08_gamma_nonneg _ _ (by positivity) hu hrvalid) hs
  have hgb : 0 ≤ gb := p08_gamma_nonneg _ _ (by positivity) hu hbvalid
  have hP : 0 ≤ P := mul_nonneg (p08_norm_nonneg _) (p08_norm_nonneg _)
  have hbudget : gb + 2*q + q^2 + 2*gb*q + gb*q^2 ≤ gc := by
    exact p08_gamma_budget (b : ℝ) (r : ℝ) u s
      (by positivity) (by positivity) hu hs hrs hcost
  have hXA_norm : p08RectFrobNorm XA = s := by
    exact NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
      (p08_orthonormal_gram XA hXA)
  have hXB_norm : p08RectFrobNorm (p08RectTranspose XB) = s := by
    rw [p08_norm_transpose]
    exact NumStability.H19Sensitivity.frobNormRect_eq_sqrt_nat_of_orthonormal
      (p08_orthonormal_gram XB hXB)
  have hYA : p08RectFrobNorm (p08RectTranspose YA) =
      p08FrobNorm (p08LowRankMatrix XA YA) := by
    symm
    exact p08_norm_mul_orth_left XA _ hXA
  have hYB : p08RectFrobNorm YB =
      p08FrobNorm (p08LowRankMatrix YB XB) := by
    symm
    exact p08_norm_mul_orth_right XB YB hXB
  have hM : p08RectFrobNorm M ≤ P := by
    calc
      p08RectFrobNorm M ≤
          p08RectFrobNorm (p08RectTranspose YA) * p08RectFrobNorm YB :=
        p08_norm_mul _ _
      _ = P := by rw [hYA, hYB]
  have hEM : p08RectFrobNorm middleStage.error ≤ gb * P := by
    simpa only [gb, P, hYA, hYB, mul_assoc] using middleStage.error_le
  have hMiddle : p08RectFrobNorm middleStage.result ≤
      p08RectFrobNorm M + p08RectFrobNorm middleStage.error := by
    exact p08_norm_add _ _
  have hER : p08RectFrobNorm rightStage.error ≤
      q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error) := by
    calc
      p08RectFrobNorm rightStage.error ≤
          p08GammaReal (r : ℝ) u * p08RectFrobNorm middleStage.result *
            p08RectFrobNorm (p08RectTranspose XB) := rightStage.error_le
      _ = q * p08RectFrobNorm middleStage.result := by rw [hXB_norm]; ring
      _ ≤ q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error) :=
        mul_le_mul_of_nonneg_left hMiddle hq
  have hRight : p08RectFrobNorm rightStage.result ≤
      p08RectFrobNorm M + p08RectFrobNorm middleStage.error +
        p08RectFrobNorm rightStage.error := by
    calc
      p08RectFrobNorm rightStage.result ≤
          p08RectFrobNorm
            (p08RectMatMul middleStage.result (p08RectTranspose XB)) +
              p08RectFrobNorm rightStage.error := p08_norm_add _ _
      _ = p08RectFrobNorm middleStage.result +
            p08RectFrobNorm rightStage.error := by
        rw [p08_norm_mul_orth_right XB _ hXB]
      _ ≤ _ := by linarith [hMiddle]
  have hEF : p08FrobNorm finalStage.error ≤
      q * (p08RectFrobNorm M + p08RectFrobNorm middleStage.error +
        p08RectFrobNorm rightStage.error) := by
    calc
      p08FrobNorm finalStage.error ≤
          p08GammaReal (r : ℝ) u * p08RectFrobNorm XA *
            p08RectFrobNorm rightStage.result := finalStage.error_le
      _ = q * p08RectFrobNorm rightStage.result := by rw [hXA_norm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hRight hq
  have htotal := p08_three_error_bound
    (p08RectFrobNorm M) (p08RectFrobNorm middleStage.error)
    (p08RectFrobNorm rightStage.error) (p08FrobNorm finalStage.error)
    P gb q gc hM hEM hER hEF hP hgb hq hbudget
  have hnorm := p08_right_error_norm XA YA XB YB
    middleStage.error rightStage.error finalStage.error hXA hXB
  have hresult :
      finalStage.result =
        XA * (((p08RectTranspose YA) * YB + middleStage.error) *
          p08RectTranspose XB + rightStage.error) + finalStage.error := by
    simp only [P08RoundedMatMulStage.result, p08_rect_mul_matrix]
  rw [hresult]
  calc
    _ ≤ p08RectFrobNorm middleStage.error + p08RectFrobNorm rightStage.error +
          p08FrobNorm finalStage.error := hnorm
    _ ≤ gc * P := htotal
    _ = _ := by dsimp [gc, P]; ring

private lemma p08_approximation_transfer {b : ℕ}
    (A B EA EB C : P08Matrix b) (epsilon betaA betaB gammaC : ℝ)
    (hgamma : 0 ≤ gammaC)
    (hEA : p08FrobNorm EA ≤ epsilon * betaA)
    (hEB : p08FrobNorm EB ≤ epsilon * betaB)
    (hfirst : p08FrobNorm
        (C - p08MatMul (A + EA) (B + EB)) ≤
      gammaC * p08FrobNorm (A + EA) * p08FrobNorm (B + EB)) :
    p08FrobNorm (C - p08MatMul A B) ≤
        gammaC * p08FrobNorm A * p08FrobNorm B +
          epsilon * (1 + gammaC) *
            (betaA * p08FrobNorm B +
              p08FrobNorm A * betaB +
              epsilon * betaA * betaB) := by
  let a := p08FrobNorm A
  let d := p08FrobNorm B
  let e := p08FrobNorm EA
  let f := p08FrobNorm EB
  let x := epsilon * betaA
  let y := epsilon * betaB
  have ha : 0 ≤ a := p08_norm_nonneg _
  have hd : 0 ≤ d := p08_norm_nonneg _
  have he : 0 ≤ e := p08_norm_nonneg _
  have hf : 0 ≤ f := p08_norm_nonneg _
  have hx : 0 ≤ x := he.trans hEA
  have hy : 0 ≤ y := hf.trans hEB
  have hAnorm : p08FrobNorm (A + EA) ≤ a + e := p08_norm_add _ _
  have hBnorm : p08FrobNorm (B + EB) ≤ d + f := p08_norm_add _ _
  have hprod : p08FrobNorm (A + EA) * p08FrobNorm (B + EB) ≤
      (a + x) * (d + y) := by
    calc
      _ ≤ (a + e) * (d + f) := by
        exact mul_le_mul hAnorm hBnorm (p08_norm_nonneg _) (by positivity)
      _ ≤ (a + x) * (d + y) := by gcongr
  have hpertEq :
      p08MatMul (A + EA) (B + EB) - p08MatMul A B =
        p08MatMul EA B + p08MatMul A EB + p08MatMul EA EB := by
    simp only [p08_sq_mul_matrix, Matrix.add_mul, Matrix.mul_add]
    abel
  have hpert : p08FrobNorm
      (p08MatMul (A + EA) (B + EB) - p08MatMul A B) ≤
      e * d + a * f + e * f := by
    rw [hpertEq]
    calc
      _ ≤ p08FrobNorm (p08MatMul EA B + p08MatMul A EB) +
            p08FrobNorm (p08MatMul EA EB) := p08_norm_add _ _
      _ ≤ (p08FrobNorm (p08MatMul EA B) +
            p08FrobNorm (p08MatMul A EB)) +
            p08FrobNorm (p08MatMul EA EB) := by
        gcongr
        exact p08_norm_add _ _
      _ ≤ e * d + a * f + e * f := by
        gcongr <;> exact p08_norm_mul _ _
  have hcombined : p08FrobNorm (C - p08MatMul A B) ≤
      gammaC * (a + x) * (d + y) +
        (e * d + a * f + e * f) := by
    have hsplit : C - p08MatMul A B =
        (C - p08MatMul (A + EA) (B + EB)) +
          (p08MatMul (A + EA) (B + EB) - p08MatMul A B) := by abel
    rw [hsplit]
    calc
      _ ≤ p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) +
            p08FrobNorm
              (p08MatMul (A + EA) (B + EB) - p08MatMul A B) :=
        p08_norm_add _ _
      _ ≤ gammaC * p08FrobNorm (A + EA) *
            p08FrobNorm (B + EB) + (e * d + a * f + e * f) :=
        add_le_add hfirst hpert
      _ ≤ gammaC * (a + x) * (d + y) +
            (e * d + a * f + e * f) := by
        have hgprod := mul_le_mul_of_nonneg_left hprod hgamma
        nlinarith [hgprod]
  have hp1 : e * d ≤ x * d := mul_le_mul_of_nonneg_right hEA hd
  have hp2 : a * f ≤ a * y := mul_le_mul_of_nonneg_left hEB ha
  have hp3 : e * f ≤ x * y := by
    exact (mul_le_mul_of_nonneg_right hEA hf).trans
      (mul_le_mul_of_nonneg_left hEB hx)
  dsimp [a, d, e, f, x, y] at *
  nlinarith [hcombined, hp1, hp2, hp3]

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
  dsimp only
  have hfirst :
      p08FrobNorm (run.trace.result -
        p08MatMul (p08LowRankMatrix run.XA run.YA)
          (p08LowRankMatrix run.YB run.XB)) ≤
        p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff *
          p08FrobNorm (p08LowRankMatrix run.XA run.YA) *
            p08FrobNorm (p08LowRankMatrix run.YB run.XB) := by
    cases run.trace with
    | leftAssociated middleStage leftStage finalStage =>
      exact p08_left_stage_bound run.unitRoundoff run.XA run.YA run.XB run.YB
        run.unitRoundoff_nonneg run.gamma_valid
        run.xA_orthonormal run.xB_orthonormal
        middleStage leftStage finalStage
    | rightAssociated middleStage rightStage finalStage =>
      exact p08_right_stage_bound run.unitRoundoff run.XA run.YA run.XB run.YB
        run.unitRoundoff_nonneg run.gamma_valid
        run.xA_orthonormal run.xB_orthonormal
        middleStage rightStage finalStage
  refine ⟨hfirst, ?_⟩
  have hgamma :
      0 ≤ p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff := by
    exact p08_gamma_nonneg _ _
      (by unfold p08LowRankMatMulCost; positivity)
      run.unitRoundoff_nonneg run.gamma_valid
  have hfirst' : p08FrobNorm
      (run.trace.result - p08MatMul
        (run.A + run.approximationErrorA)
        (run.B + run.approximationErrorB)) ≤
      p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff *
        p08FrobNorm (run.A + run.approximationErrorA) *
          p08FrobNorm (run.B + run.approximationErrorB) := by
    rw [← run.approximationA_eq, ← run.approximationB_eq]
    exact hfirst
  exact p08_approximation_transfer run.A run.B
    run.approximationErrorA run.approximationErrorB run.trace.result
    run.epsilon run.betaA run.betaB
    (p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff)
    hgamma run.approximationErrorA_le run.approximationErrorB_le hfirst'

end VSCLReuse

import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix Matrix.Norms.Frobenius


private lemma p08_norm_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def, p08RectFrobNorm, Real.sqrt_eq_rpow]
  simp [Real.norm_eq_abs, sq_abs]

private lemma p08_norm_left_ortho {b r p : ℕ}
    (X : P08RectMatrix b r) (M : P08RectMatrix r p)
    (hX : p08OrthonormalColumns X) : ‖X * M‖ = ‖M‖ := by
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
  simp [Real.norm_eq_abs, sq_abs]
  apply congrArg (fun z : ℝ => z ^ (2⁻¹ : ℝ))
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.mul_apply]
  calc
    (∑ i : Fin b, (∑ j : Fin r, X i j * M j l) ^ 2) =
        ∑ j : Fin r, ∑ k : Fin r, (∑ i : Fin b, X i j * X i k) *
          (M j l * M k l) := by
          simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Fin r, M j l ^ 2 := by
      unfold p08OrthonormalColumns at hX
      simp_rw [hX]
      simp [pow_two]

private lemma p08_norm_right_ortho {p b r : ℕ}
    (M : P08RectMatrix p r) (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) : ‖M * Xᵀ‖ = ‖M‖ := by
  rw [← Matrix.frobenius_norm_transpose (M * Xᵀ), Matrix.transpose_mul,
    Matrix.transpose_transpose, p08_norm_left_ortho X Mᵀ hX,
    Matrix.frobenius_norm_transpose]

private lemma p08_norm_ortho {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖X‖ = Real.sqrt (r : ℝ) := by
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp [Real.norm_eq_abs, sq_abs]
  apply congrArg (fun z : ℝ => z ^ (2⁻¹ : ℝ))
  rw [Finset.sum_comm]
  have h : ∀ j : Fin r, (∑ i : Fin b, X i j ^ 2) = 1 := by
    intro j
    simpa [p08OrthonormalColumns, pow_two] using hX j j
  simp [h]

private lemma p08_rect_mul_eq {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectMatMul A B = A * B := by
  ext i j
  rfl

private lemma p08_mat_mul_eq {n : ℕ} (A B : P08Matrix n) :
    p08MatMul A B = A * B := p08_rect_mul_eq A B

private lemma p08_transpose_eq {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectTranspose A = Aᵀ := rfl

private lemma p08_gamma_nonneg (u k : ℝ) (hu : 0 ≤ u) (hk : 0 ≤ k)
    (hv : k * u < 1) : 0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private lemma p08_gamma_mono (u a d : ℝ) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (had : a ≤ d) (hv : d * u < 1) :
    p08GammaReal a u ≤ p08GammaReal d u := by
  have hau : 0 < 1 - a * u := by nlinarith [mul_le_mul_of_nonneg_right had hu]
  have hdu : 0 < 1 - d * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ hau hdu).2
  nlinarith [mul_le_mul_of_nonneg_right had hu]

private lemma p08_gamma_combine (u a d : ℝ) (hu : 0 ≤ u)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hv : (a + d) * u < 1) :
    (1 + p08GammaReal a u) * (1 + p08GammaReal d u) ≤
      1 + p08GammaReal (a + d) u := by
  have hau : 0 < 1 - a * u := by nlinarith [mul_nonneg hd hu]
  have hdu : 0 < 1 - d * u := by nlinarith [mul_nonneg ha hu]
  have hadu : 0 < 1 - (a + d) * u := by linarith
  have hrew (x : ℝ) (hx : 0 < 1 - x * u) :
      1 + p08GammaReal x u = 1 / (1 - x * u) := by
    unfold p08GammaReal
    field_simp
    ring
  rw [hrew a hau, hrew d hdu, hrew (a + d) hadu]
  rw [one_div_mul_one_div]
  apply (div_le_div_iff₀ (mul_pos hau hdu) hadu).2
  dsimp
  nlinarith [mul_nonneg (mul_nonneg ha hd) (mul_nonneg hu hu)]

private lemma p08_sqrt_nat_ge_one_or_zero (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  by_cases hr : r = 0
  · simp [hr]
  · have hcast : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hs : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hcast
    nlinarith

private lemma p08_gamma_stage_le (b r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hv : p08LowRankMatMulCost b r * u < 1) :
    p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) ≤
      p08GammaReal ((r : ℝ) * Real.sqrt (r : ℝ)) u := by
  let d : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hrd : (r : ℝ) ≤ d := p08_sqrt_nat_ge_one_or_zero r
  have hdu : d * u < 1 := by
    unfold p08LowRankMatMulCost at hv
    dsimp [d]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) b) hu,
      mul_nonneg hd hu]
  have hru : (r : ℝ) * u < 1 := by nlinarith [mul_le_mul_of_nonneg_right hrd hu]
  have hγr : 0 ≤ p08GammaReal (r : ℝ) u :=
    p08_gamma_nonneg u _ hu (Nat.cast_nonneg _) hru
  by_cases hr : r = 0
  · simp [hr, p08GammaReal, d]
  · have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
    have hden : 0 < 1 - (r : ℝ) * u := by linarith
    have hden2 : 0 < 1 - d * u := by linarith
    have hnum : 0 ≤ d * u := mul_nonneg hd hu
    calc
      p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ) =
          (d * u) / (1 - (r : ℝ) * u) := by
            unfold p08GammaReal
            dsimp [d]
            rw [div_mul_eq_mul_div]
            congr 1
            ring
      _ ≤ (d * u) / (1 - d * u) := by
        apply (div_le_div_iff₀ hden hden2).2
        have hdenle : 1 - d * u ≤ 1 - (r : ℝ) * u := by
          nlinarith [mul_le_mul_of_nonneg_right hrd hu]
        nlinarith [mul_nonneg hnum (sub_nonneg.mpr hdenle)]
      _ = p08GammaReal d u := rfl

private lemma p08_gamma_budget (b r : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hv : p08LowRankMatMulCost b r * u < 1) :
    (1 + p08GammaReal (b : ℝ) u) *
        (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ^ 2 ≤
      1 + p08GammaReal (p08LowRankMatMulCost b r) u := by
  let d : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  have hd : 0 ≤ d := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hcost : ((b : ℝ) + 2 * d) * u < 1 := by
    convert hv using 1 <;> dsimp [p08LowRankMatMulCost, d] <;> ring
  have hbd : ((b : ℝ) + d) * u < 1 := by
    nlinarith [mul_nonneg hd hu]
  have hdu : d * u < 1 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) b) hu,
      mul_nonneg hd hu]
  have hbu : (b : ℝ) * u < 1 := by
    nlinarith [mul_nonneg hd hu]
  have hγb : 0 ≤ p08GammaReal (b : ℝ) u :=
    p08_gamma_nonneg u _ hu (Nat.cast_nonneg _) hbu
  have hγd : 0 ≤ p08GammaReal d u := p08_gamma_nonneg u _ hu hd hdu
  have hγr : 0 ≤ p08GammaReal (r : ℝ) u := by
    exact p08_gamma_nonneg u _ hu (Nat.cast_nonneg _)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right
        (p08_sqrt_nat_ge_one_or_zero r) hu) hdu)
  have hstage := p08_gamma_stage_le b r u hu hv
  have h1 := p08_gamma_combine u (b : ℝ) d hu (Nat.cast_nonneg _) hd hbd
  have h2 := p08_gamma_combine u ((b : ℝ) + d) d hu
    (add_nonneg (Nat.cast_nonneg _) hd) hd (by convert hcost using 1 <;> ring)
  calc
    (1 + p08GammaReal (b : ℝ) u) *
        (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) ^ 2 ≤
        (1 + p08GammaReal (b : ℝ) u) * (1 + p08GammaReal d u) ^ 2 := by
          gcongr
    _ = ((1 + p08GammaReal (b : ℝ) u) * (1 + p08GammaReal d u)) *
        (1 + p08GammaReal d u) := by ring
    _ ≤ (1 + p08GammaReal ((b : ℝ) + d) u) *
        (1 + p08GammaReal d u) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ 1 + p08GammaReal (((b : ℝ) + d) + d) u := h2
    _ = 1 + p08GammaReal (p08LowRankMatMulCost b r) u := by
      congr 1
      unfold p08LowRankMatMulCost d
      ring

private lemma p08_three_stage_left {b r : ℕ}
    (X Z : P08RectMatrix b r) (M E0 : P08RectMatrix r r)
    (E1 : P08RectMatrix b r) (E2 : P08Matrix b)
    (u P : ℝ) (hu : 0 ≤ u)
    (hv : p08LowRankMatMulCost b r * u < 1)
    (hX : p08OrthonormalColumns X) (hZ : p08OrthonormalColumns Z)
    (hP : 0 ≤ P) (hM : ‖M‖ ≤ P)
    (hE0 : ‖E0‖ ≤ p08GammaReal (b : ℝ) u * P)
    (hE1 : ‖E1‖ ≤ p08GammaReal (r : ℝ) u * ‖X‖ * ‖M + E0‖)
    (hE2 : ‖E2‖ ≤ p08GammaReal (r : ℝ) u *
      ‖X * (M + E0) + E1‖ * ‖Zᵀ‖) :
    ‖((X * (M + E0) + E1) * Zᵀ + E2) - (X * M) * Zᵀ‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u * P := by
  let gb := p08GammaReal (b : ℝ) u
  let t := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
  have hbu : (b : ℝ) * u < 1 := by
    unfold p08LowRankMatMulCost at hv
    have hnonneg : 0 ≤ 2 * (r : ℝ) * Real.sqrt (r : ℝ) * u := by positivity
    nlinarith
  have hgb : 0 ≤ gb := p08_gamma_nonneg u _ hu (Nat.cast_nonneg _) hbu
  have ht : 0 ≤ t := by
    dsimp [t]
    have hrd := p08_sqrt_nat_ge_one_or_zero r
    have hdu : ((r : ℝ) * Real.sqrt (r : ℝ)) * u < 1 := by
      unfold p08LowRankMatMulCost at hv
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) b) hu]
    exact mul_nonneg (p08_gamma_nonneg u _ hu (Nat.cast_nonneg _)
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrd hu) hdu))
      (Real.sqrt_nonneg _)
  have hMhat : ‖M + E0‖ ≤ (1 + gb) * P := by
    calc
      ‖M + E0‖ ≤ ‖M‖ + ‖E0‖ := norm_add_le M E0
      _ ≤ P + gb * P := add_le_add hM hE0
      _ = (1 + gb) * P := by ring
  have hE1' : ‖E1‖ ≤ t * ((1 + gb) * P) := by
    rw [p08_norm_ortho X hX] at hE1
    calc
      ‖E1‖ ≤ t * ‖M + E0‖ := by simpa [t, mul_assoc] using hE1
      _ ≤ t * ((1 + gb) * P) := mul_le_mul_of_nonneg_left hMhat ht
  have hLhat : ‖X * (M + E0) + E1‖ ≤ (1 + t) * ((1 + gb) * P) := by
    calc
      ‖X * (M + E0) + E1‖ ≤ ‖X * (M + E0)‖ + ‖E1‖ := norm_add_le _ _
      _ = ‖M + E0‖ + ‖E1‖ := by rw [p08_norm_left_ortho X _ hX]
      _ ≤ (1 + gb) * P + t * ((1 + gb) * P) := add_le_add hMhat hE1'
      _ = (1 + t) * ((1 + gb) * P) := by ring
  have hE2' : ‖E2‖ ≤ t * ((1 + t) * ((1 + gb) * P)) := by
    rw [Matrix.frobenius_norm_transpose, p08_norm_ortho Z hZ] at hE2
    calc
      ‖E2‖ ≤ t * ‖X * (M + E0) + E1‖ := by
        convert hE2 using 1 <;> dsimp [t] <;> ring
      _ ≤ t * ((1 + t) * ((1 + gb) * P)) :=
        mul_le_mul_of_nonneg_left hLhat ht
  have hdiff :
      ‖((X * (M + E0) + E1) * Zᵀ + E2) - (X * M) * Zᵀ‖ ≤
        ‖E0‖ + ‖E1‖ + ‖E2‖ := by
    calc
      ‖((X * (M + E0) + E1) * Zᵀ + E2) - (X * M) * Zᵀ‖ =
          ‖((X * (M + E0) + E1) - X * M) * Zᵀ + E2‖ := by
            congr 1
            rw [Matrix.sub_mul]
            abel
      _ ≤ ‖((X * (M + E0) + E1) - X * M) * Zᵀ‖ + ‖E2‖ := norm_add_le _ _
      _ = ‖(X * (M + E0) + E1) - X * M‖ + ‖E2‖ := by
        rw [p08_norm_right_ortho _ Z hZ]
      _ = ‖X * E0 + E1‖ + ‖E2‖ := by
        congr 1
        rw [Matrix.mul_add]
        abel
      _ ≤ (‖X * E0‖ + ‖E1‖) + ‖E2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖E0‖ + ‖E1‖ + ‖E2‖ := by rw [p08_norm_left_ortho X E0 hX]
  have hscalar := p08_gamma_budget b r u hu hv
  calc
    ‖((X * (M + E0) + E1) * Zᵀ + E2) - (X * M) * Zᵀ‖ ≤
        ‖E0‖ + ‖E1‖ + ‖E2‖ := hdiff
    _ ≤ gb * P + t * ((1 + gb) * P) +
        t * ((1 + t) * ((1 + gb) * P)) := by
          exact add_le_add (add_le_add hE0 hE1') hE2'
    _ = (((1 + gb) * (1 + t) ^ 2) - 1) * P := by ring
    _ ≤ p08GammaReal (p08LowRankMatMulCost b r) u * P := by
      apply mul_le_mul_of_nonneg_right _ hP
      dsimp [gb, t]
      linarith

private lemma p08_three_stage_right {b r : ℕ}
    (X Z : P08RectMatrix b r) (M E0 : P08RectMatrix r r)
    (E1 : P08RectMatrix r b) (E2 : P08Matrix b)
    (u P : ℝ) (hu : 0 ≤ u)
    (hv : p08LowRankMatMulCost b r * u < 1)
    (hX : p08OrthonormalColumns X) (hZ : p08OrthonormalColumns Z)
    (hP : 0 ≤ P) (hM : ‖M‖ ≤ P)
    (hE0 : ‖E0‖ ≤ p08GammaReal (b : ℝ) u * P)
    (hE1 : ‖E1‖ ≤ p08GammaReal (r : ℝ) u * ‖M + E0‖ * ‖Zᵀ‖)
    (hE2 : ‖E2‖ ≤ p08GammaReal (r : ℝ) u * ‖X‖ *
      ‖(M + E0) * Zᵀ + E1‖) :
    ‖X * ((M + E0) * Zᵀ + E1) + E2 - (X * M) * Zᵀ‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u * P := by
  have hE1' : ‖E1ᵀ‖ ≤ p08GammaReal (r : ℝ) u * ‖Z‖ *
      ‖Mᵀ + E0ᵀ‖ := by
    rw [Matrix.frobenius_norm_transpose]
    simp only [← Matrix.transpose_add, Matrix.frobenius_norm_transpose]
    rw [Matrix.frobenius_norm_transpose] at hE1
    convert hE1 using 1 <;> ring
  have hE2' : ‖E2ᵀ‖ ≤ p08GammaReal (r : ℝ) u *
      ‖Z * (Mᵀ + E0ᵀ) + E1ᵀ‖ * ‖Xᵀ‖ := by
    rw [Matrix.frobenius_norm_transpose]
    have ht : ((M + E0) * Zᵀ + E1)ᵀ = Z * (Mᵀ + E0ᵀ) + E1ᵀ := by
      simp [Matrix.transpose_add, Matrix.transpose_mul]
    rw [← ht, Matrix.frobenius_norm_transpose, Matrix.frobenius_norm_transpose]
    convert hE2 using 1 <;> ring
  have h := p08_three_stage_left Z X Mᵀ E0ᵀ E1ᵀ E2ᵀ u P hu hv
    hZ hX hP (by simpa only [Matrix.frobenius_norm_transpose] using hM)
    (by simpa only [Matrix.frobenius_norm_transpose] using hE0)
    hE1' hE2'
  convert h using 1
  rw [← Matrix.frobenius_norm_transpose
    (X * ((M + E0) * Zᵀ + E1) + E2 - (X * M) * Zᵀ)]
  simp [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.mul_assoc]

private lemma p08_trace_bound {b r : ℕ}
    (XA YA XB YB : P08RectMatrix b r) (u : ℝ)
    (hu : 0 ≤ u) (hv : p08LowRankMatMulCost b r * u < 1)
    (hXA : p08OrthonormalColumns XA) (hXB : p08OrthonormalColumns XB)
    (trace : P08LowRankMatMulTrace u XA YA XB YB) :
    ‖trace.result - (XA * YAᵀ) * (YB * XBᵀ)‖ ≤
      p08GammaReal (p08LowRankMatMulCost b r) u *
        ‖XA * YAᵀ‖ * ‖YB * XBᵀ‖ := by
  let M : P08RectMatrix r r := YAᵀ * YB
  let P : ℝ := ‖YA‖ * ‖YB‖
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hM : ‖M‖ ≤ P := by
    calc
      ‖M‖ = ‖YAᵀ * YB‖ := rfl
      _ ≤ ‖YAᵀ‖ * ‖YB‖ := Matrix.frobenius_norm_mul _ _
      _ = P := by rw [Matrix.frobenius_norm_transpose]
  have hA : ‖XA * YAᵀ‖ = ‖YA‖ := by
    rw [p08_norm_left_ortho XA YAᵀ hXA, Matrix.frobenius_norm_transpose]
  have hB : ‖YB * XBᵀ‖ = ‖YB‖ := p08_norm_right_ortho YB XB hXB
  have hprod : (XA * YAᵀ) * (YB * XBᵀ) = (XA * M) * XBᵀ := by
    dsimp [M]
    simp only [Matrix.mul_assoc]
  cases trace with
  | leftAssociated middle left final =>
      have hm : middle.result = M + middle.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, M]
      have hl : left.result = XA * (M + middle.error) + left.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, hm, M]
      have hf : final.result =
          (XA * (M + middle.error) + left.error) * XBᵀ + final.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, hl, M]
      have he0 : ‖middle.error‖ ≤ p08GammaReal (b : ℝ) u * P := by
        simpa [P, p08_norm_eq, p08_transpose_eq,
          Matrix.frobenius_norm_transpose, mul_assoc] using middle.error_le
      have he1 : ‖left.error‖ ≤ p08GammaReal (r : ℝ) u *
          ‖XA‖ * ‖M + middle.error‖ := by
        simpa [p08_norm_eq, hm] using left.error_le
      have he2 : ‖final.error‖ ≤ p08GammaReal (r : ℝ) u *
          ‖XA * (M + middle.error) + left.error‖ * ‖XBᵀ‖ := by
        simpa [p08_norm_eq, p08_transpose_eq, hl] using final.error_le
      have h := p08_three_stage_left XA XB M middle.error left.error
        final.error u P hu hv hXA hXB hP hM he0 he1 he2
      simpa only [P08LowRankMatMulTrace.result, hf, hprod, hA, hB,
        P, mul_assoc] using h

  | rightAssociated middle right final =>
      have hm : middle.result = M + middle.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, M]
      have hr : right.result = (M + middle.error) * XBᵀ + right.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, hm, M]
      have hf : final.result =
          XA * ((M + middle.error) * XBᵀ + right.error) + final.error := by
        simp [P08RoundedMatMulStage.result, p08_rect_mul_eq,
          p08_transpose_eq, hr, M]
      have he0 : ‖middle.error‖ ≤ p08GammaReal (b : ℝ) u * P := by
        simpa [P, p08_norm_eq, p08_transpose_eq,
          Matrix.frobenius_norm_transpose, mul_assoc] using middle.error_le
      have he1 : ‖right.error‖ ≤ p08GammaReal (r : ℝ) u *
          ‖M + middle.error‖ * ‖XBᵀ‖ := by
        simpa [p08_norm_eq, p08_transpose_eq, hm] using right.error_le
      have he2 : ‖final.error‖ ≤ p08GammaReal (r : ℝ) u *
          ‖XA‖ * ‖(M + middle.error) * XBᵀ + right.error‖ := by
        simpa [p08_norm_eq, hr] using final.error_le
      have h := p08_three_stage_right XA XB M middle.error right.error
        final.error u P hu hv hXA hXB hP hM he0 he1 he2
      simpa only [P08LowRankMatMulTrace.result, hf, hprod, hA, hB,
        P, mul_assoc] using h

private lemma p08_perturbation_bound {b : ℕ}
    (A B EA EB C : P08Matrix b) (γ ea eb : ℝ)
    (hγ : 0 ≤ γ) (hEA : ‖EA‖ ≤ ea) (hEB : ‖EB‖ ≤ eb)
    (hC : ‖C - (A + EA) * (B + EB)‖ ≤
      γ * ‖A + EA‖ * ‖B + EB‖) :
    ‖C - A * B‖ ≤ γ * ‖A‖ * ‖B‖ +
      (1 + γ) * (ea * ‖B‖ + ‖A‖ * eb + ea * eb) := by
  have hea : 0 ≤ ea := le_trans (norm_nonneg EA) hEA
  have heb : 0 ≤ eb := le_trans (norm_nonneg EB) hEB
  have hAnorm : ‖A + EA‖ ≤ ‖A‖ + ea := by
    exact (norm_add_le A EA).trans (add_le_add le_rfl hEA)
  have hBnorm : ‖B + EB‖ ≤ ‖B‖ + eb := by
    exact (norm_add_le B EB).trans (add_le_add le_rfl hEB)
  have hprod : ‖A + EA‖ * ‖B + EB‖ ≤
      (‖A‖ + ea) * (‖B‖ + eb) := by
    exact mul_le_mul hAnorm hBnorm (norm_nonneg _) (by positivity)
  have hdiff : ‖(A + EA) * (B + EB) - A * B‖ ≤
      ea * (‖B‖ + eb) + ‖A‖ * eb := by
    calc
      ‖(A + EA) * (B + EB) - A * B‖ =
          ‖EA * (B + EB) + A * EB‖ := by
            congr 1
            rw [Matrix.add_mul, Matrix.mul_add]
            abel
      _ ≤ ‖EA * (B + EB)‖ + ‖A * EB‖ := norm_add_le _ _
      _ ≤ ‖EA‖ * ‖B + EB‖ + ‖A‖ * ‖EB‖ := by
        exact add_le_add (Matrix.frobenius_norm_mul _ _)
          (Matrix.frobenius_norm_mul _ _)
      _ ≤ ea * (‖B‖ + eb) + ‖A‖ * eb := by
        apply add_le_add
        · exact mul_le_mul hEA hBnorm (norm_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left hEB (norm_nonneg _)
  calc
    ‖C - A * B‖ = ‖(C - (A + EA) * (B + EB)) +
        ((A + EA) * (B + EB) - A * B)‖ := by congr 1; abel
    _ ≤ ‖C - (A + EA) * (B + EB)‖ +
        ‖(A + EA) * (B + EB) - A * B‖ := norm_add_le _ _
    _ ≤ γ * ‖A + EA‖ * ‖B + EB‖ +
        (ea * (‖B‖ + eb) + ‖A‖ * eb) := add_le_add hC hdiff
    _ ≤ γ * ((‖A‖ + ea) * (‖B‖ + eb)) +
        (ea * (‖B‖ + eb) + ‖A‖ * eb) := by
          apply add_le_add _ le_rfl
          calc
            γ * ‖A + EA‖ * ‖B + EB‖ =
                γ * (‖A + EA‖ * ‖B + EB‖) := by ring
            _ ≤ γ * ((‖A‖ + ea) * (‖B‖ + eb)) :=
              mul_le_mul_of_nonneg_left hprod hγ
    _ = γ * ‖A‖ * ‖B‖ +
        (1 + γ) * (ea * ‖B‖ + ‖A‖ * eb + ea * eb) := by ring

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
  let At : P08Matrix b := p08LowRankMatrix run.XA run.YA
  let Bt : P08Matrix b := p08LowRankMatrix run.YB run.XB
  let gc : ℝ := p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
  have hAt : At = run.A + run.approximationErrorA := run.approximationA_eq
  have hBt : Bt = run.B + run.approximationErrorB := run.approximationB_eq
  have hcost : 0 ≤ p08LowRankMatMulCost b r := by
    unfold p08LowRankMatMulCost
    positivity
  have hgc : 0 ≤ gc := p08_gamma_nonneg run.unitRoundoff _
    run.unitRoundoff_nonneg hcost run.gamma_valid
  have hfirst : ‖run.trace.result - At * Bt‖ ≤ gc * ‖At‖ * ‖Bt‖ := by
    have h := p08_trace_bound run.XA run.YA run.XB run.YB run.unitRoundoff
      run.unitRoundoff_nonneg run.gamma_valid run.xA_orthonormal
      run.xB_orthonormal run.trace
    simpa [At, Bt, gc, p08LowRankMatrix, p08_rect_mul_eq,
      p08_transpose_eq] using h
  have hEA : ‖run.approximationErrorA‖ ≤ run.epsilon * run.betaA := by
    simpa [p08FrobNorm, p08_norm_eq] using run.approximationErrorA_le
  have hEB : ‖run.approximationErrorB‖ ≤ run.epsilon * run.betaB := by
    simpa [p08FrobNorm, p08_norm_eq] using run.approximationErrorB_le
  have hfirst' : ‖run.trace.result -
      (run.A + run.approximationErrorA) *
        (run.B + run.approximationErrorB)‖ ≤
      gc * ‖run.A + run.approximationErrorA‖ *
        ‖run.B + run.approximationErrorB‖ := by
    simpa only [hAt, hBt] using hfirst
  have hsecond := p08_perturbation_bound run.A run.B
    run.approximationErrorA run.approximationErrorB run.trace.result
    gc (run.epsilon * run.betaA) (run.epsilon * run.betaB)
    hgc hEA hEB hfirst'
  dsimp only
  constructor
  · simpa [At, Bt, gc, p08FrobNorm, p08_norm_eq,
      p08_mat_mul_eq] using hfirst
  · have hsecond' : ‖run.trace.result - run.A * run.B‖ ≤
        gc * ‖run.A‖ * ‖run.B‖ +
          run.epsilon * (1 + gc) *
            (run.betaA * ‖run.B‖ + ‖run.A‖ * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
          calc
            _ ≤ gc * ‖run.A‖ * ‖run.B‖ +
                (1 + gc) *
                  ((run.epsilon * run.betaA) * ‖run.B‖ +
                    ‖run.A‖ * (run.epsilon * run.betaB) +
                    (run.epsilon * run.betaA) * (run.epsilon * run.betaB)) := hsecond
            _ = _ := by ring
    simpa [gc, p08FrobNorm, p08_norm_eq, p08_mat_mul_eq] using hsecond'

end VSCLReuse

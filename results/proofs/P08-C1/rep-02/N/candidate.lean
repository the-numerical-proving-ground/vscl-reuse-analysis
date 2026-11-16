import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius


private theorem p08_frob_eq_norm {m n : ℕ} (A : P08RectMatrix m n) :
    p08RectFrobNorm A = ‖A‖ := by
  simp [p08RectFrobNorm, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow,
    Real.norm_eq_abs, sq_abs]

private theorem p08_frob_nonneg {m n : ℕ} (A : P08RectMatrix m n) :
    0 ≤ p08RectFrobNorm A := by
  rw [p08_frob_eq_norm]
  exact norm_nonneg _

private theorem p08_frob_add_le {m n : ℕ}
    (A B : P08RectMatrix m n) :
    p08RectFrobNorm (A + B) ≤ p08RectFrobNorm A + p08RectFrobNorm B := by
  simp only [p08_frob_eq_norm]
  exact norm_add_le _ _

private theorem p08_frob_mul_le {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    p08RectFrobNorm (p08RectMatMul A B) ≤
      p08RectFrobNorm A * p08RectFrobNorm B := by
  simp only [p08_frob_eq_norm]
  simpa only [p08RectMatMul, Matrix.mul_apply] using
    Matrix.frobenius_norm_mul A B

private theorem p08_orthonormal_vec_sq {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (v : Fin r → ℝ) :
    (∑ i : Fin b, (∑ k : Fin r, X i k * v k) ^ 2) =
      ∑ k : Fin r, v k ^ 2 := by
  calc
    (∑ i : Fin b, (∑ k : Fin r, X i k * v k) ^ 2)
        = ∑ i : Fin b, ∑ k : Fin r, ∑ l : Fin r,
            (X i k * v k) * (X i l * v l) := by
              simp_rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ l : Fin r,
          (∑ i : Fin b, X i k * X i l) * (v k * v l) := by
            rw [Finset.sum_comm]
            congr 1
            ext k
            rw [Finset.sum_comm]
            congr 1
            ext l
            rw [Finset.sum_mul]
            congr 1
            ext i
            ring
    _ = ∑ k : Fin r, v k ^ 2 := by
          change (∀ j k, (∑ i : Fin b, X i j * X i k) =
            if j = k then 1 else 0) at hX
          simp [hX, pow_two]

private theorem p08_frob_transpose {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  simp only [p08_frob_eq_norm]
  simpa only [p08RectTranspose, Matrix.transpose_apply] using
    Matrix.frobenius_norm_transpose A

private theorem p08_frob_mul_left_orthonormal {b r p : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (M : P08RectMatrix r p) :
    p08RectFrobNorm (p08RectMatMul X M) = p08RectFrobNorm M := by
  unfold p08RectFrobNorm p08RectMatMul
  congr 1
  rw [Finset.sum_comm]
  simp_rw [p08_orthonormal_vec_sq X hX]
  rw [Finset.sum_comm]

private theorem p08_frob_mul_right_orthonormal {b r p : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (M : P08RectMatrix p r) :
    p08RectFrobNorm (p08RectMatMul M (p08RectTranspose X)) =
      p08RectFrobNorm M := by
  rw [← p08_frob_transpose M]
  rw [← p08_frob_transpose (p08RectMatMul M (p08RectTranspose X))]
  have htranspose :
      p08RectTranspose (p08RectMatMul M (p08RectTranspose X)) =
        p08RectMatMul X (p08RectTranspose M) := by
    ext i j
    simp only [p08RectTranspose, p08RectMatMul]
    congr 1
    ext k
    ring
  rw [htranspose, p08_frob_mul_left_orthonormal X hX]

private theorem p08_frob_orthonormal {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  congr 1
  rw [Finset.sum_comm]
  have hXX : ∀ j : Fin r, (∑ i : Fin b, X i j ^ 2) = 1 := by
    intro j
    simpa [p08OrthonormalColumns, pow_two] using hX j j
  simp [hXX]

private theorem p08_rect_mul_assoc {m n p q : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p)
    (C : P08RectMatrix p q) :
    p08RectMatMul (p08RectMatMul A B) C =
      p08RectMatMul A (p08RectMatMul B C) := by
  change (A * B) * C = A * (B * C)
  exact Matrix.mul_assoc A B C

private theorem p08_rect_mul_add {m n p : ℕ}
    (A : P08RectMatrix m n) (B C : P08RectMatrix n p) :
    p08RectMatMul A (B + C) =
      p08RectMatMul A B + p08RectMatMul A C := by
  change A * (B + C) = A * B + A * C
  exact Matrix.mul_add A B C

private theorem p08_rect_add_mul {m n p : ℕ}
    (A B : P08RectMatrix m n) (C : P08RectMatrix n p) :
    p08RectMatMul (A + B) C =
      p08RectMatMul A C + p08RectMatMul B C := by
  change (A + B) * C = A * C + B * C
  exact Matrix.add_mul A B C

private theorem p08_left_trace_error_eq {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P08RectMatrix b r)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (left : P08RoundedMatMulStage b r r u XA middle.result)
    (final : P08RoundedMatMulStage b r b u left.result
      (p08RectTranspose XB)) :
    final.result -
      p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
      p08RectMatMul
          (p08RectMatMul XA middle.error) (p08RectTranspose XB) +
        p08RectMatMul left.error (p08RectTranspose XB) + final.error := by
  change
    (((XA * ((p08RectTranspose YA * YB) + middle.error)) + left.error) *
        p08RectTranspose XB + final.error) -
      ((XA * p08RectTranspose YA) * (YB * p08RectTranspose XB)) =
      ((XA * middle.error) * p08RectTranspose XB) +
        left.error * p08RectTranspose XB + final.error
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

private theorem p08_right_trace_error_eq {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P08RectMatrix b r)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (right : P08RoundedMatMulStage r r b u middle.result
      (p08RectTranspose XB))
    (final : P08RoundedMatMulStage b r b u XA right.result) :
    final.result -
      p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
      p08RectMatMul XA
          (p08RectMatMul middle.error (p08RectTranspose XB)) +
        p08RectMatMul XA right.error + final.error := by
  change
    (XA * (((p08RectTranspose YA * YB) + middle.error) *
        p08RectTranspose XB + right.error) + final.error) -
      ((XA * p08RectTranspose YA) * (YB * p08RectTranspose XB)) =
      XA * (middle.error * p08RectTranspose XB) +
        XA * right.error + final.error
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

private theorem p08_left_trace_error_le {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P08RectMatrix b r)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (left : P08RoundedMatMulStage b r r u XA middle.result)
    (final : P08RoundedMatMulStage b r b u left.result
      (p08RectTranspose XB))
    (hgr : 0 ≤ p08GammaReal (r : ℝ) u) :
    p08FrobNorm
        (final.result -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      (p08GammaReal (b : ℝ) u +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u) +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u)) *
        (p08RectFrobNorm YA * p08RectFrobNorm YB) := by
  let gb := p08GammaReal (b : ℝ) u
  let gr := p08GammaReal (r : ℝ) u
  let q := Real.sqrt (r : ℝ)
  let P := p08RectFrobNorm YA * p08RectFrobNorm YB
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hP : 0 ≤ P := mul_nonneg (p08_frob_nonneg _) (p08_frob_nonneg _)
  have hk : 0 ≤ gr * q := mul_nonneg hgr hq
  have hM : p08RectFrobNorm middle.error ≤ gb * P := by
    convert middle.error_le using 1
    simp only [gb, P, p08_frob_transpose]
    ring
  have hMN : p08RectFrobNorm middle.result ≤ (1 + gb) * P := by
    calc
      _ ≤ p08RectFrobNorm
            (p08RectMatMul (p08RectTranspose YA) YB) +
            p08RectFrobNorm middle.error := by
              change p08RectFrobNorm
                (p08RectMatMul (p08RectTranspose YA) YB + middle.error) ≤ _
              exact p08_frob_add_le _ _
      _ ≤ P + gb * P := by
            gcongr
            simpa only [P, p08_frob_transpose] using
              p08_frob_mul_le (p08RectTranspose YA) YB
      _ = (1 + gb) * P := by ring
  have hL : p08RectFrobNorm left.error ≤
      (gr * q) * ((1 + gb) * P) := by
    calc
      _ ≤ (gr * q) * p08RectFrobNorm middle.result := by
            simpa only [gr, q, p08_frob_orthonormal XA hXA] using left.error_le
      _ ≤ (gr * q) * ((1 + gb) * P) := by gcongr
  have hLN : p08RectFrobNorm left.result ≤
      (1 + gr * q) * ((1 + gb) * P) := by
    calc
      _ ≤ p08RectFrobNorm (p08RectMatMul XA middle.result) +
            p08RectFrobNorm left.error := by
              change p08RectFrobNorm
                (p08RectMatMul XA middle.result + left.error) ≤ _
              exact p08_frob_add_le _ _
      _ ≤ (1 + gb) * P + (gr * q) * ((1 + gb) * P) := by
            rw [p08_frob_mul_left_orthonormal XA hXA]
            exact add_le_add hMN hL
      _ = (1 + gr * q) * ((1 + gb) * P) := by ring
  have hF : p08RectFrobNorm final.error ≤
      (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by
    calc
      _ ≤ (gr * q) * p08RectFrobNorm left.result := by
            convert final.error_le using 1
            simp only [gr, q, p08_frob_transpose,
              p08_frob_orthonormal XB hXB]
            ring
      _ ≤ (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by gcongr
  rw [p08_left_trace_error_eq XA YA XB YB middle left final]
  calc
    p08RectFrobNorm
        (p08RectMatMul (p08RectMatMul XA middle.error)
            (p08RectTranspose XB) +
          p08RectMatMul left.error (p08RectTranspose XB) + final.error)
        ≤ (p08RectFrobNorm middle.error +
              p08RectFrobNorm left.error) +
            p08RectFrobNorm final.error := by
              have h1 := p08_frob_add_le
                (p08RectMatMul (p08RectMatMul XA middle.error)
                  (p08RectTranspose XB) +
                  p08RectMatMul left.error (p08RectTranspose XB))
                final.error
              have h2 := p08_frob_add_le
                (p08RectMatMul (p08RectMatMul XA middle.error)
                  (p08RectTranspose XB))
                (p08RectMatMul left.error (p08RectTranspose XB))
              rw [p08_frob_mul_right_orthonormal XB hXB,
                p08_frob_mul_left_orthonormal XA hXA] at h2
              rw [p08_frob_mul_right_orthonormal XB hXB] at h2
              exact h1.trans (add_le_add h2 (le_refl _))
    _ ≤ (gb * P + (gr * q) * ((1 + gb) * P)) +
          (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by
            gcongr
    _ = (gb + (gr * q) * (1 + gb) +
          (gr * q) * (1 + gr * q) * (1 + gb)) * P := by ring

private theorem p08_right_trace_error_le {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P08RectMatrix b r)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (middle : P08RoundedMatMulStage r b r u (p08RectTranspose YA) YB)
    (right : P08RoundedMatMulStage r r b u middle.result
      (p08RectTranspose XB))
    (final : P08RoundedMatMulStage b r b u XA right.result)
    (hgr : 0 ≤ p08GammaReal (r : ℝ) u) :
    p08FrobNorm
        (final.result -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      (p08GammaReal (b : ℝ) u +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u) +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u)) *
        (p08RectFrobNorm YA * p08RectFrobNorm YB) := by
  let gb := p08GammaReal (b : ℝ) u
  let gr := p08GammaReal (r : ℝ) u
  let q := Real.sqrt (r : ℝ)
  let P := p08RectFrobNorm YA * p08RectFrobNorm YB
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hk : 0 ≤ gr * q := mul_nonneg hgr hq
  have hM : p08RectFrobNorm middle.error ≤ gb * P := by
    convert middle.error_le using 1
    simp only [gb, P, p08_frob_transpose]
    ring
  have hMN : p08RectFrobNorm middle.result ≤ (1 + gb) * P := by
    calc
      _ ≤ p08RectFrobNorm
            (p08RectMatMul (p08RectTranspose YA) YB) +
            p08RectFrobNorm middle.error := by
              change p08RectFrobNorm
                (p08RectMatMul (p08RectTranspose YA) YB + middle.error) ≤ _
              exact p08_frob_add_le _ _
      _ ≤ P + gb * P := by
            gcongr
            simpa only [P, p08_frob_transpose] using
              p08_frob_mul_le (p08RectTranspose YA) YB
      _ = (1 + gb) * P := by ring
  have hR : p08RectFrobNorm right.error ≤
      (gr * q) * ((1 + gb) * P) := by
    calc
      _ ≤ (gr * q) * p08RectFrobNorm middle.result := by
            convert right.error_le using 1
            simp only [gr, q, p08_frob_transpose,
              p08_frob_orthonormal XB hXB]
            ring
      _ ≤ (gr * q) * ((1 + gb) * P) := by gcongr
  have hRN : p08RectFrobNorm right.result ≤
      (1 + gr * q) * ((1 + gb) * P) := by
    calc
      _ ≤ p08RectFrobNorm
            (p08RectMatMul middle.result (p08RectTranspose XB)) +
            p08RectFrobNorm right.error := by
              change p08RectFrobNorm
                (p08RectMatMul middle.result (p08RectTranspose XB) +
                  right.error) ≤ _
              exact p08_frob_add_le _ _
      _ ≤ (1 + gb) * P + (gr * q) * ((1 + gb) * P) := by
            rw [p08_frob_mul_right_orthonormal XB hXB]
            exact add_le_add hMN hR
      _ = (1 + gr * q) * ((1 + gb) * P) := by ring
  have hF : p08RectFrobNorm final.error ≤
      (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by
    calc
      _ ≤ (gr * q) * p08RectFrobNorm right.result := by
            convert final.error_le using 1
            simp only [gr, q, p08_frob_orthonormal XA hXA]
      _ ≤ (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by gcongr
  rw [p08_right_trace_error_eq XA YA XB YB middle right final]
  calc
    p08RectFrobNorm
        (p08RectMatMul XA
            (p08RectMatMul middle.error (p08RectTranspose XB)) +
          p08RectMatMul XA right.error + final.error)
        ≤ (p08RectFrobNorm middle.error +
              p08RectFrobNorm right.error) +
            p08RectFrobNorm final.error := by
              have h1 := p08_frob_add_le
                (p08RectMatMul XA
                    (p08RectMatMul middle.error (p08RectTranspose XB)) +
                  p08RectMatMul XA right.error)
                final.error
              have h2 := p08_frob_add_le
                (p08RectMatMul XA
                  (p08RectMatMul middle.error (p08RectTranspose XB)))
                (p08RectMatMul XA right.error)
              rw [p08_frob_mul_left_orthonormal XA hXA,
                p08_frob_mul_right_orthonormal XB hXB] at h2
              rw [p08_frob_mul_left_orthonormal XA hXA] at h2
              exact h1.trans (add_le_add h2 (le_refl _))
    _ ≤ (gb * P + (gr * q) * ((1 + gb) * P)) +
          (gr * q) * ((1 + gr * q) * ((1 + gb) * P)) := by
            gcongr
    _ = (gb + (gr * q) * (1 + gb) +
          (gr * q) * (1 + gr * q) * (1 + gb)) * P := by ring

private theorem p08_scalar_three_stage {t s : ℝ}
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hc : t + 2 * s < 1) :
    t / (1 - t) +
        (s / (1 - s)) * (1 + t / (1 - t)) +
        (s / (1 - s)) * (1 + s / (1 - s)) *
          (1 + t / (1 - t)) ≤
      (t + 2 * s) / (1 - t - 2 * s) := by
  have htd : 0 < 1 - t := by linarith
  have hsd : 0 < 1 - s := by linarith
  have hcd : 0 < 1 - t - 2 * s := by linarith
  have hden : 1 - t - 2 * s ≤ (1 - t) * (1 - s) ^ 2 := by
    have h1 : 0 ≤ (1 - t) * s ^ 2 :=
      mul_nonneg (le_of_lt htd) (sq_nonneg s)
    have h2 : 0 ≤ t * s := mul_nonneg ht hs
    nlinarith
  have hrecip :
      1 / ((1 - t) * (1 - s) ^ 2) ≤
        1 / (1 - t - 2 * s) :=
    one_div_le_one_div_of_le hcd hden
  have hleft :
      1 + (t / (1 - t) +
        (s / (1 - s)) * (1 + t / (1 - t)) +
        (s / (1 - s)) * (1 + s / (1 - s)) *
          (1 + t / (1 - t))) =
        1 / ((1 - t) * (1 - s) ^ 2) := by
    field_simp
    ring
  have hright :
      1 + (t + 2 * s) / (1 - t - 2 * s) =
        1 / (1 - t - 2 * s) := by
    field_simp
    ring
  linarith

private theorem p08_gamma_nonneg {k u : ℝ}
    (hk : 0 ≤ k) (hu : 0 ≤ u) (hvalid : k * u < 1) :
    0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private theorem p08_three_stage_coeff_le {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1) :
    p08GammaReal (b : ℝ) u +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u) +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u) ≤
      p08GammaReal (p08LowRankMatMulCost b r) u := by
  let t : ℝ := (b : ℝ) * u
  let v : ℝ := (r : ℝ) * u
  let q : ℝ := Real.sqrt (r : ℝ)
  let s : ℝ := v * q
  let gb : ℝ := p08GammaReal (b : ℝ) u
  let gr : ℝ := p08GammaReal (r : ℝ) u
  let k : ℝ := gr * q
  let d : ℝ := s / (1 - s)
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hu
  have hv : 0 ≤ v := mul_nonneg (Nat.cast_nonneg _) hu
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hs : 0 ≤ s := mul_nonneg hv hq
  have hc : t + 2 * s < 1 := by
    dsimp [p08LowRankMatMulCost] at hvalid
    dsimp [t, s, v, q]
    nlinarith [hvalid]
  have hvs : v ≤ s := by
    by_cases hr : r = 0
    · subst r
      simp [v, s]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
      have hq1 : 1 ≤ q := (Real.one_le_sqrt).2 hr1
      have hh : 0 ≤ v * (q - 1) :=
        mul_nonneg hv (by linarith)
      dsimp [s]
      nlinarith
  have hvd : 0 < 1 - v := by linarith
  have hsd : 0 < 1 - s := by linarith
  have htd : 0 < 1 - t := by linarith
  have hgb : 0 ≤ gb := p08_gamma_nonneg (Nat.cast_nonneg _) hu (by
    dsimp [t] at htd ⊢
    linarith)
  have hgr : 0 ≤ gr := p08_gamma_nonneg (Nat.cast_nonneg _) hu (by
    dsimp [v] at hvd ⊢
    linarith)
  have hk : 0 ≤ k := mul_nonneg hgr hq
  have hd : 0 ≤ d := div_nonneg hs (le_of_lt hsd)
  have hkd : k ≤ d := by
    have heq : k = s / (1 - v) := by
      dsimp [k, gr, p08GammaReal, s, v]
      ring
    rw [heq]
    apply (div_le_div_iff₀ hvd hsd).2
    have hh : 0 ≤ s * (s - v) :=
      mul_nonneg hs (sub_nonneg.mpr hvs)
    nlinarith
  have hmon :
      gb + k * (1 + gb) + k * (1 + k) * (1 + gb) ≤
        gb + d * (1 + gb) + d * (1 + d) * (1 + gb) := by
    have hpos : 0 ≤ 1 + gb := by linarith
    have hprod : k * (1 + k) ≤ d * (1 + d) := by
      have hh : 0 ≤ (d - k) * (1 + d + k) :=
        mul_nonneg (sub_nonneg.mpr hkd) (by linarith)
      nlinarith
    have h1 := mul_le_mul_of_nonneg_right hkd hpos
    have h2 := mul_le_mul_of_nonneg_right hprod hpos
    nlinarith
  have hscalar := p08_scalar_three_stage ht hs hc
  have hgb_eq : gb = t / (1 - t) := by
    rfl
  have hcost_eq :
      p08GammaReal (p08LowRankMatMulCost b r) u =
        (t + 2 * s) / (1 - t - 2 * s) := by
    dsimp [p08GammaReal, p08LowRankMatMulCost, t, s, v, q]
    congr 1 <;> ring
  dsimp [gb, gr, k] at hmon
  rw [← hgb_eq] at hscalar
  change gb + k * (1 + gb) + k * (1 + k) * (1 + gb) ≤
    p08GammaReal (p08LowRankMatMulCost b r) u
  rw [hcost_eq]
  exact hmon.trans hscalar

private theorem p08_stage_gammas_nonneg {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u)
    (hvalid : p08LowRankMatMulCost b r * u < 1) :
    0 ≤ p08GammaReal (b : ℝ) u ∧
      0 ≤ p08GammaReal (r : ℝ) u := by
  have hb : (b : ℝ) * u < 1 := by
    have hq : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
    have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    dsimp [p08LowRankMatMulCost] at hvalid
    nlinarith [mul_nonneg (mul_nonneg hr hq) hu]
  have hr : (r : ℝ) * u < 1 := by
    by_cases hz : r = 0
    · subst r
      simp
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hq1 : 1 ≤ Real.sqrt (r : ℝ) :=
        (Real.one_le_sqrt).2 hr1
      have hru : 0 ≤ (r : ℝ) * u :=
        mul_nonneg (Nat.cast_nonneg _) hu
      have hx : 0 ≤ ((r : ℝ) * u) *
          (Real.sqrt (r : ℝ) - 1) :=
        mul_nonneg hru (by linarith)
      dsimp [p08LowRankMatMulCost] at hvalid
      nlinarith
  exact ⟨p08_gamma_nonneg (Nat.cast_nonneg _) hu hb,
    p08_gamma_nonneg (Nat.cast_nonneg _) hu hr⟩

private theorem p08_frob_low_rank_left {b r : ℕ}
    (X Y : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix X Y) = p08RectFrobNorm Y := by
  unfold p08FrobNorm p08LowRankMatrix
  rw [p08_frob_mul_left_orthonormal X hX,
    p08_frob_transpose]

private theorem p08_frob_low_rank_right {b r : ℕ}
    (X Y : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) :
    p08FrobNorm (p08LowRankMatrix Y X) = p08RectFrobNorm Y := by
  unfold p08FrobNorm p08LowRankMatrix
  exact p08_frob_mul_right_orthonormal X hX Y

private theorem p08_trace_error_le {b r : ℕ} {u : ℝ}
    (XA YA XB YB : P08RectMatrix b r)
    (hXA : p08OrthonormalColumns XA)
    (hXB : p08OrthonormalColumns XB)
    (trace : P08LowRankMatMulTrace u XA YA XB YB)
    (hgr : 0 ≤ p08GammaReal (r : ℝ) u) :
    p08FrobNorm
        (trace.result -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)) ≤
      (p08GammaReal (b : ℝ) u +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u) +
        (p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)) *
          (1 + p08GammaReal (b : ℝ) u)) *
        (p08RectFrobNorm YA * p08RectFrobNorm YB) := by
  cases trace with
  | leftAssociated middle left final =>
      exact p08_left_trace_error_le XA YA XB YB hXA hXB
        middle left final hgr
  | rightAssociated middle right final =>
      exact p08_right_trace_error_le XA YA XB YB hXA hXB
        middle right final hgr

private theorem p08_matmul_perturb_bound {b : ℕ}
    (C A B EA EB : P08Matrix b) (eA eB : ℝ)
    (hEA : p08FrobNorm EA ≤ eA)
    (hEB : p08FrobNorm EB ≤ eB) :
    p08FrobNorm (C - p08MatMul A B) ≤
      p08FrobNorm
        (C - p08MatMul (A + EA) (B + EB)) +
        (eA * p08FrobNorm B +
          p08FrobNorm A * eB + eA * eB) := by
  have heA : 0 ≤ eA := (p08_frob_nonneg EA).trans hEA
  have heB : 0 ≤ eB := (p08_frob_nonneg EB).trans hEB
  have hEq :
      C - p08MatMul A B =
        (C - p08MatMul (A + EA) (B + EB)) +
          ((p08MatMul EA B + p08MatMul A EB) +
            p08MatMul EA EB) := by
    change C - A * B =
      (C - (A + EA) * (B + EB)) +
        ((EA * B + A * EB) + EA * EB)
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  rw [hEq]
  calc
    p08FrobNorm
        ((C - p08MatMul (A + EA) (B + EB)) +
          ((p08MatMul EA B + p08MatMul A EB) +
            p08MatMul EA EB))
        ≤ p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) +
          p08FrobNorm
            ((p08MatMul EA B + p08MatMul A EB) +
              p08MatMul EA EB) :=
            p08_frob_add_le _ _
    _ ≤ p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) +
          (p08FrobNorm (p08MatMul EA B) +
            p08FrobNorm (p08MatMul A EB) +
            p08FrobNorm (p08MatMul EA EB)) := by
            gcongr
            calc
              _ ≤ p08FrobNorm (p08MatMul EA B + p08MatMul A EB) +
                    p08FrobNorm (p08MatMul EA EB) :=
                    p08_frob_add_le _ _
              _ ≤ p08FrobNorm (p08MatMul EA B) +
                    p08FrobNorm (p08MatMul A EB) +
                    p08FrobNorm (p08MatMul EA EB) := by
                    gcongr
                    exact p08_frob_add_le _ _
    _ ≤ p08FrobNorm (C - p08MatMul (A + EA) (B + EB)) +
          (eA * p08FrobNorm B +
            p08FrobNorm A * eB + eA * eB) := by
            gcongr
            · calc
                p08FrobNorm (p08MatMul EA B) ≤
                    p08FrobNorm EA * p08FrobNorm B :=
                  p08_frob_mul_le EA B
                _ ≤ eA * p08FrobNorm B :=
                  mul_le_mul_of_nonneg_right hEA (p08_frob_nonneg B)
            · calc
                p08FrobNorm (p08MatMul A EB) ≤
                    p08FrobNorm A * p08FrobNorm EB :=
                  p08_frob_mul_le A EB
                _ ≤ p08FrobNorm A * eB :=
                  mul_le_mul_of_nonneg_left hEB (p08_frob_nonneg A)
            · calc
                p08FrobNorm (p08MatMul EA EB) ≤
                    p08FrobNorm EA * p08FrobNorm EB :=
                  p08_frob_mul_le EA EB
                _ ≤ eA * eB := by
                  gcongr
                  exact p08_frob_nonneg EB

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
  let Atilde := p08LowRankMatrix run.XA run.YA
  let Btilde := p08LowRankMatrix run.YB run.XB
  let gammaC := p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
  let eA := run.epsilon * run.betaA
  let eB := run.epsilon * run.betaB
  change
    p08FrobNorm (run.trace.result - p08MatMul Atilde Btilde) ≤
        gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde ∧
      p08FrobNorm (run.trace.result - p08MatMul run.A run.B) ≤
        gammaC * p08FrobNorm run.A * p08FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p08FrobNorm run.B +
              p08FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB)
  have hgr :=
    (p08_stage_gammas_nonneg run.unitRoundoff_nonneg run.gamma_valid).2
  have hcoeff :=
    p08_three_stage_coeff_le run.unitRoundoff_nonneg run.gamma_valid
  have hAtilde :
      p08FrobNorm Atilde = p08RectFrobNorm run.YA :=
    p08_frob_low_rank_left run.XA run.YA run.xA_orthonormal
  have hBtilde :
      p08FrobNorm Btilde = p08RectFrobNorm run.YB :=
    p08_frob_low_rank_right run.XB run.YB run.xB_orthonormal
  have hP : 0 ≤ p08RectFrobNorm run.YA * p08RectFrobNorm run.YB :=
    mul_nonneg (p08_frob_nonneg _) (p08_frob_nonneg _)
  have hFirst :
      p08FrobNorm (run.trace.result - p08MatMul Atilde Btilde) ≤
        gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde := by
    calc
      _ ≤ (p08GammaReal (b : ℝ) run.unitRoundoff +
          (p08GammaReal (r : ℝ) run.unitRoundoff * Real.sqrt (r : ℝ)) *
            (1 + p08GammaReal (b : ℝ) run.unitRoundoff) +
          (p08GammaReal (r : ℝ) run.unitRoundoff * Real.sqrt (r : ℝ)) *
            (1 + p08GammaReal (r : ℝ) run.unitRoundoff *
              Real.sqrt (r : ℝ)) *
            (1 + p08GammaReal (b : ℝ) run.unitRoundoff)) *
          (p08RectFrobNorm run.YA * p08RectFrobNorm run.YB) :=
            p08_trace_error_le run.XA run.YA run.XB run.YB
              run.xA_orthonormal run.xB_orthonormal run.trace hgr
      _ ≤ gammaC *
          (p08RectFrobNorm run.YA * p08RectFrobNorm run.YB) :=
            mul_le_mul_of_nonneg_right hcoeff hP
      _ = gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde := by
            rw [hAtilde, hBtilde]
            ring
  refine ⟨hFirst, ?_⟩
  have heA : 0 ≤ eA :=
    (p08_frob_nonneg run.approximationErrorA).trans
      run.approximationErrorA_le
  have heB : 0 ≤ eB :=
    (p08_frob_nonneg run.approximationErrorB).trans
      run.approximationErrorB_le
  have hcost : 0 ≤ p08LowRankMatMulCost b r := by
    unfold p08LowRankMatMulCost
    positivity
  have hgamma : 0 ≤ gammaC :=
    p08_gamma_nonneg hcost run.unitRoundoff_nonneg run.gamma_valid
  have hAnorm :
      p08FrobNorm Atilde ≤ p08FrobNorm run.A + eA := by
    calc
      p08FrobNorm Atilde =
          p08FrobNorm (run.A + run.approximationErrorA) := by
            exact congrArg p08FrobNorm run.approximationA_eq
      _ ≤ p08FrobNorm run.A +
          p08FrobNorm run.approximationErrorA :=
            p08_frob_add_le _ _
      _ ≤ p08FrobNorm run.A + eA :=
            add_le_add (le_refl _) run.approximationErrorA_le
  have hBnorm :
      p08FrobNorm Btilde ≤ p08FrobNorm run.B + eB := by
    calc
      p08FrobNorm Btilde =
          p08FrobNorm (run.B + run.approximationErrorB) := by
            exact congrArg p08FrobNorm run.approximationB_eq
      _ ≤ p08FrobNorm run.B +
          p08FrobNorm run.approximationErrorB :=
            p08_frob_add_le _ _
      _ ≤ p08FrobNorm run.B + eB :=
            add_le_add (le_refl _) run.approximationErrorB_le
  have hPert :=
    p08_matmul_perturb_bound run.trace.result run.A run.B
      run.approximationErrorA run.approximationErrorB eA eB
      run.approximationErrorA_le run.approximationErrorB_le
  rw [← run.approximationA_eq, ← run.approximationB_eq] at hPert
  have hmult :
      gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde ≤
        gammaC * (p08FrobNorm run.A + eA) *
          (p08FrobNorm run.B + eB) := by
    calc
      _ ≤ gammaC * (p08FrobNorm run.A + eA) *
          p08FrobNorm Btilde := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hAnorm hgamma)
              (p08_frob_nonneg Btilde)
      _ ≤ gammaC * (p08FrobNorm run.A + eA) *
          (p08FrobNorm run.B + eB) := by
            exact mul_le_mul_of_nonneg_left hBnorm
              (mul_nonneg hgamma
                (add_nonneg (p08_frob_nonneg run.A) heA))
  calc
    p08FrobNorm (run.trace.result - p08MatMul run.A run.B)
        ≤ p08FrobNorm (run.trace.result - p08MatMul Atilde Btilde) +
          (eA * p08FrobNorm run.B +
            p08FrobNorm run.A * eB + eA * eB) := hPert
    _ ≤ gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde +
          (eA * p08FrobNorm run.B +
            p08FrobNorm run.A * eB + eA * eB) := by
            exact add_le_add hFirst (le_refl _)
    _ ≤ gammaC * (p08FrobNorm run.A + eA) *
          (p08FrobNorm run.B + eB) +
          (eA * p08FrobNorm run.B +
            p08FrobNorm run.A * eB + eA * eB) := by
            exact add_le_add hmult (le_refl _)
    _ = gammaC * p08FrobNorm run.A * p08FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p08FrobNorm run.B +
              p08FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
            dsimp [eA, eB]
            ring

end VSCLReuse

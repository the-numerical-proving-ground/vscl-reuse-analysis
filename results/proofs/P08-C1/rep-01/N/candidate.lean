import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.Frobenius Matrix

private lemma p08_rect_norm_eq {m n : ℕ} (M : P08RectMatrix m n) :
    p08RectFrobNorm M = ‖M‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def]
  simp [Real.sqrt_eq_rpow]

private lemma p08_rect_mul_eq {m n p : ℕ}
    (M : P08RectMatrix m n) (N : P08RectMatrix n p) :
    p08RectMatMul M N = M * N := by
  ext i j
  rfl

private lemma p08_low_rank_eq {b r : ℕ}
    (X Y : P08RectMatrix b r) :
    p08LowRankMatrix X Y = X * Yᵀ := by
  rw [p08LowRankMatrix, p08_rect_mul_eq]
  rfl

private lemma p08_mat_mul_eq {b : ℕ} (M N : P08Matrix b) :
    p08MatMul M N = M * N := by
  ext i j
  rfl

private lemma p08_ortho_vec_sq {b r : ℕ} (X : P08RectMatrix b r)
    (hX : p08OrthonormalColumns X) (v : Fin r → ℝ) :
    (∑ i : Fin b, (∑ j : Fin r, X i j * v j) ^ 2) =
      ∑ j : Fin r, v j ^ 2 := by
  calc
    _ = ∑ i : Fin b, ∑ j : Fin r, ∑ k : Fin r,
          (X i j * X i k) * (v j * v k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ j : Fin r, ∑ k : Fin r,
          (∑ i : Fin b, X i j * X i k) * (v j * v k) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ j : Fin r, v j ^ 2 := by
      change (∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0) at hX
      simp [hX, sq]

private lemma p08_ortho_mul_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (M : P08RectMatrix r n) :
    p08RectFrobNorm (p08RectMatMul X M) = p08RectFrobNorm M := by
  unfold p08RectFrobNorm p08RectMatMul
  congr 1
  calc
    (∑ i : Fin b, ∑ k : Fin n, (∑ j : Fin r, X i j * M j k) ^ 2) =
        ∑ k : Fin n, ∑ i : Fin b, (∑ j : Fin r, X i j * M j k) ^ 2 :=
      Finset.sum_comm
    _ = ∑ k : Fin n, ∑ j : Fin r, M j k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact p08_ortho_vec_sq X hX (fun j => M j k)
    _ = ∑ j : Fin r, ∑ k : Fin n, M j k ^ 2 := Finset.sum_comm

private lemma p08_ortho_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  congr 1
  calc
    (∑ i : Fin b, ∑ j : Fin r, X i j ^ 2) =
        ∑ j : Fin r, ∑ i : Fin b, X i j ^ 2 := Finset.sum_comm
    _ = ∑ j : Fin r, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [sq, ite_true] using hX j j
    _ = (r : ℝ) := by simp

private lemma p08_ortho_mul_norm' {b r n : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (M : P08RectMatrix r n) : ‖X * M‖ = ‖M‖ := by
  simpa only [p08_rect_norm_eq, p08_rect_mul_eq] using p08_ortho_mul_norm X hX M

private lemma p08_ortho_mul_right_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (M : P08RectMatrix n r) : ‖M * Xᵀ‖ = ‖M‖ := by
  rw [← Matrix.frobenius_norm_transpose (M * Xᵀ)]
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [p08_ortho_mul_norm' X hX Mᵀ]
  exact Matrix.frobenius_norm_transpose M

private lemma p08_ortho_norm' {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖X‖ = Real.sqrt (r : ℝ) := by
  simpa only [p08_rect_norm_eq] using p08_ortho_norm X hX

private lemma p08_approx_norm_left {b r : ℕ}
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖p08LowRankMatrix X Y‖ = ‖Y‖ := by
  rw [p08_low_rank_eq, p08_ortho_mul_norm' X hX]
  exact Matrix.frobenius_norm_transpose Y

private lemma p08_approx_norm_right {b r : ℕ}
    (X Y : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    ‖p08LowRankMatrix Y X‖ = ‖Y‖ := by
  rw [p08_low_rank_eq, p08_ortho_mul_right_norm X hX]

private lemma p08_stage_error_norm {m n p : ℕ} {u : ℝ}
    {M : P08RectMatrix m n} {N : P08RectMatrix n p}
    (stage : P08RoundedMatMulStage m n p u M N) :
    ‖stage.error‖ ≤ p08GammaReal (n : ℝ) u * ‖M‖ * ‖N‖ := by
  simpa only [← p08_rect_norm_eq] using stage.error_le

private lemma p08_stage_result_eq {m n p : ℕ} {u : ℝ}
    {M : P08RectMatrix m n} {N : P08RectMatrix n p}
    (stage : P08RoundedMatMulStage m n p u M N) :
    stage.result = M * N + stage.error := by
  rw [P08RoundedMatMulStage.result, p08_rect_mul_eq]

private lemma p08_cost_bounds (b r : ℕ) :
    (b : ℝ) ≤ p08LowRankMatMulCost b r ∧
      (r : ℝ) ≤ p08LowRankMatMulCost b r := by
  have hs : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hsq : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt hr
  constructor
  · unfold p08LowRankMatMulCost
    nlinarith [mul_nonneg hr hs]
  · by_cases hz : r = 0
    · subst r
      simp [p08LowRankMatMulCost, hb]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hs1 : 1 ≤ Real.sqrt (r : ℝ) := by nlinarith
      unfold p08LowRankMatMulCost
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hs1)]

private lemma p08_gamma_nonneg (k u : ℝ)
    (hk : 0 ≤ k) (hu : 0 ≤ u) (hvalid : k * u < 1) :
    0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private lemma p08_gamma_pair (x z : ℝ)
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hv : x + 2 * z < 1) :
    let a := x / (1 - x)
    let q := z / (1 - z)
    a + q * (1 + a) + q * (1 + q) * (1 + a) ≤
      (x + 2 * z) / (1 - x - 2 * z) := by
  dsimp
  have hxden : 0 < 1 - x := by linarith
  have hzden : 0 < 1 - z := by linarith
  have hcden : 0 < 1 - x - 2 * z := by linarith
  have hpoly : 1 - x - 2 * z ≤ (1 - x) * (1 - z) ^ 2 := by
    have hterm : 0 ≤ z * (2 * x + z * (1 - x)) := by positivity
    nlinarith
  have hrec : 1 / ((1 - x) * (1 - z) ^ 2) ≤
      1 / (1 - x - 2 * z) :=
    one_div_le_one_div_of_le hcden hpoly
  have hxd : x / (1 - x) + 1 = 1 / (1 - x) := by
    field_simp
    ring
  have hzd : z / (1 - z) + 1 = 1 / (1 - z) := by
    field_simp
    ring
  have hcd : (x + 2 * z) / (1 - x - 2 * z) + 1 =
      1 / (1 - x - 2 * z) := by
    field_simp
    ring
  have heq : x / (1 - x) + z / (1 - z) * (1 + x / (1 - x)) +
      z / (1 - z) * (1 + z / (1 - z)) * (1 + x / (1 - x)) + 1 =
      1 / ((1 - x) * (1 - z) ^ 2) := by
    rw [← add_comm 1 (x / (1 - x))] at hxd
    rw [← add_comm 1 (z / (1 - z))] at hzd
    calc
      _ = (1 + x / (1 - x)) * (1 + z / (1 - z)) ^ 2 := by ring
      _ = 1 / ((1 - x) * (1 - z) ^ 2) := by
        rw [hxd, hzd]
        simp only [one_div, mul_inv_rev, inv_pow]
        ring
  linarith

private lemma p08_gamma_cost (b r : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hv : p08LowRankMatMulCost b r * u < 1) :
    let a := p08GammaReal (b : ℝ) u
    let h := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
    a + h * (1 + a) + h * (1 + h) * (1 + a) ≤
      p08GammaReal (p08LowRankMatMulCost b r) u := by
  dsimp
  let s := Real.sqrt (r : ℝ)
  let x := (b : ℝ) * u
  let y := (r : ℝ) * u
  let z := (r : ℝ) * s * u
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hx : 0 ≤ x := mul_nonneg hb hu
  have hy : 0 ≤ y := mul_nonneg hr hu
  have hz : 0 ≤ z := by positivity
  have hcost : p08LowRankMatMulCost b r * u = x + 2 * z := by
    simp only [p08LowRankMatMulCost, x, z, s]
    ring
  have hv' : x + 2 * z < 1 := by rw [← hcost]; exact hv
  have hyz : y ≤ z := by
    by_cases hzero : r = 0
    · simp [y, z, hzero]
    · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      have hsq : s ^ 2 = (r : ℝ) := Real.sq_sqrt hr
      have hs1 : 1 ≤ s := by nlinarith
      have hmul := mul_nonneg hy (sub_nonneg.mpr hs1)
      dsimp [y, z] at *
      nlinarith
  have hxden : 0 < 1 - x := by linarith
  have hyden : 0 < 1 - y := by linarith
  have hzden : 0 < 1 - z := by linarith
  have hq : p08GammaReal (r : ℝ) u * s ≤ z / (1 - z) := by
    have hrec : 1 / (1 - y) ≤ 1 / (1 - z) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    have hmul := mul_le_mul_of_nonneg_left hrec hz
    unfold p08GammaReal
    dsimp [y, z] at *
    convert hmul using 1 <;> ring
  have hnonneg : 0 ≤ p08GammaReal (b : ℝ) u :=
    p08_gamma_nonneg _ _ hb hu (by
      have := (p08_cost_bounds b r).1
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hu])
  have hrvalid : (r : ℝ) * u < 1 := by
    have := (p08_cost_bounds b r).2
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hu]
  have hhn : 0 ≤ p08GammaReal (r : ℝ) u * s :=
    mul_nonneg (p08_gamma_nonneg _ _ hr hu hrvalid) hs
  have hqn : 0 ≤ z / (1 - z) := div_nonneg hz (le_of_lt hzden)
  have hcmp :
      p08GammaReal (b : ℝ) u +
          (p08GammaReal (r : ℝ) u * s) * (1 + p08GammaReal (b : ℝ) u) +
          (p08GammaReal (r : ℝ) u * s) *
            (1 + p08GammaReal (r : ℝ) u * s) *
              (1 + p08GammaReal (b : ℝ) u) ≤
      p08GammaReal (b : ℝ) u +
          (z / (1 - z)) * (1 + p08GammaReal (b : ℝ) u) +
          (z / (1 - z)) * (1 + z / (1 - z)) *
              (1 + p08GammaReal (b : ℝ) u) := by
    gcongr
  have hpair := p08_gamma_pair x z hx hz hv'
  dsimp at hpair
  have haeq : p08GammaReal (b : ℝ) u = x / (1 - x) := rfl
  have hceq : p08GammaReal (p08LowRankMatMulCost b r) u =
      (x + 2 * z) / (1 - x - 2 * z) := by
    unfold p08GammaReal
    rw [hcost]
    congr 1
    ring
  rw [haeq] at hcmp
  rw [haeq, hceq]
  simpa only [s] using hcmp.trans hpair

private lemma p08_trace_bound {b r : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hv : p08LowRankMatMulCost b r * u < 1)
    (XA YA XB YB : P08RectMatrix b r)
    (hXA : p08OrthonormalColumns XA) (hXB : p08OrthonormalColumns XB)
    (trace : P08LowRankMatMulTrace u XA YA XB YB) :
    let a := p08GammaReal (b : ℝ) u
    let h := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
    ‖trace.result - p08MatMul (p08LowRankMatrix XA YA)
        (p08LowRankMatrix YB XB)‖ ≤
      (a + h * (1 + a) + h * (1 + h) * (1 + a)) *
        (‖YA‖ * ‖YB‖) := by
  dsimp
  let a := p08GammaReal (b : ℝ) u
  let h := p08GammaReal (r : ℝ) u * Real.sqrt (r : ℝ)
  let P := ‖YA‖ * ‖YB‖
  have hP : 0 ≤ P := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hb : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hvb : (b : ℝ) * u < 1 := by
    have := (p08_cost_bounds b r).1
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hu]
  have hvr : (r : ℝ) * u < 1 := by
    have := (p08_cost_bounds b r).2
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hu]
  have ha : 0 ≤ a := p08_gamma_nonneg _ _ hb hu hvb
  have hh : 0 ≤ h :=
    mul_nonneg (p08_gamma_nonneg _ _ hr hu hvr) (Real.sqrt_nonneg _)
  cases trace with
  | leftAssociated middle left final =>
    have hm : ‖middle.error‖ ≤ a * P := by
      have hmt := p08_stage_error_norm middle
      change ‖middle.error‖ ≤
        p08GammaReal (b : ℝ) u * ‖YAᵀ‖ * ‖YB‖ at hmt
      rw [Matrix.frobenius_norm_transpose] at hmt
      simpa only [a, P, mul_assoc] using hmt
    have hmiddle : ‖middle.result‖ ≤ (1 + a) * P := by
      rw [p08_stage_result_eq]
      calc
        ‖YAᵀ * YB + middle.error‖ ≤ ‖YAᵀ * YB‖ + ‖middle.error‖ :=
          norm_add_le _ _
        _ ≤ P + a * P := by
          apply add_le_add _ hm
          simpa only [P, Matrix.frobenius_norm_transpose] using
            Matrix.frobenius_norm_mul YAᵀ YB
        _ = (1 + a) * P := by ring
    have hl : ‖left.error‖ ≤ h * (1 + a) * P := by
      calc
        ‖left.error‖ ≤ p08GammaReal (r : ℝ) u * ‖XA‖ * ‖middle.result‖ :=
          p08_stage_error_norm left
        _ = h * ‖middle.result‖ := by
          rw [p08_ortho_norm' XA hXA]
        _ ≤ h * ((1 + a) * P) := mul_le_mul_of_nonneg_left hmiddle hh
        _ = h * (1 + a) * P := by ring
    have hleft : ‖left.result‖ ≤ (1 + h) * (1 + a) * P := by
      rw [p08_stage_result_eq]
      calc
        ‖XA * middle.result + left.error‖ ≤
            ‖XA * middle.result‖ + ‖left.error‖ := norm_add_le _ _
        _ ≤ (1 + a) * P + h * (1 + a) * P := by
          rw [p08_ortho_mul_norm' XA hXA]
          exact add_le_add hmiddle hl
        _ = (1 + h) * (1 + a) * P := by ring
    have hf : ‖final.error‖ ≤ h * (1 + h) * (1 + a) * P := by
      calc
        ‖final.error‖ ≤ p08GammaReal (r : ℝ) u * ‖left.result‖ * ‖XBᵀ‖ :=
          p08_stage_error_norm final
        _ = h * ‖left.result‖ := by
          rw [Matrix.frobenius_norm_transpose, p08_ortho_norm' XB hXB]
          dsimp [h]
          ring
        _ ≤ h * ((1 + h) * (1 + a) * P) :=
          mul_le_mul_of_nonneg_left hleft hh
        _ = h * (1 + h) * (1 + a) * P := by ring
    have herr : final.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
        (XA * middle.error) * XBᵀ + left.error * XBᵀ + final.error := by
      let e1 := middle.error
      let e2 := left.error
      let e3 := final.error
      change (left.result * XBᵀ + e3) -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
          (XA * e1) * XBᵀ + e2 * XBᵀ + e3
      rw [p08_stage_result_eq left]
      have hfirst : XA * middle.result =
          XA * (YAᵀ * YB + middle.error) :=
        congrArg (fun M => XA * M) (p08_stage_result_eq middle)
      rw [hfirst]
      dsimp only [e1, e2, e3]
      simp only [p08_mat_mul_eq, p08_low_rank_eq, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      abel
    change ‖final.result -
      p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)‖ ≤ _
    rw [herr]
    calc
      ‖(XA * middle.error) * XBᵀ + left.error * XBᵀ + final.error‖ ≤
          ‖(XA * middle.error) * XBᵀ‖ + ‖left.error * XBᵀ‖ +
            ‖final.error‖ := by
        linarith [norm_add_le ((XA * middle.error) * XBᵀ + left.error * XBᵀ) final.error,
          norm_add_le ((XA * middle.error) * XBᵀ) (left.error * XBᵀ)]
      _ = ‖middle.error‖ + ‖left.error‖ + ‖final.error‖ := by
        rw [p08_ortho_mul_right_norm XB hXB,
          p08_ortho_mul_norm' XA hXA,
          p08_ortho_mul_right_norm XB hXB]
      _ ≤ a * P + h * (1 + a) * P + h * (1 + h) * (1 + a) * P := by
        exact add_le_add (add_le_add hm hl) hf
      _ = (a + h * (1 + a) + h * (1 + h) * (1 + a)) * P := by ring

  | rightAssociated middle right final =>
    have hm : ‖middle.error‖ ≤ a * P := by
      have hmt := p08_stage_error_norm middle
      change ‖middle.error‖ ≤
        p08GammaReal (b : ℝ) u * ‖YAᵀ‖ * ‖YB‖ at hmt
      rw [Matrix.frobenius_norm_transpose] at hmt
      simpa only [a, P, mul_assoc] using hmt
    have hmiddle : ‖middle.result‖ ≤ (1 + a) * P := by
      rw [p08_stage_result_eq]
      calc
        ‖YAᵀ * YB + middle.error‖ ≤ ‖YAᵀ * YB‖ + ‖middle.error‖ :=
          norm_add_le _ _
        _ ≤ P + a * P := by
          apply add_le_add _ hm
          simpa only [P, Matrix.frobenius_norm_transpose] using
            Matrix.frobenius_norm_mul YAᵀ YB
        _ = (1 + a) * P := by ring
    have he : ‖right.error‖ ≤ h * (1 + a) * P := by
      calc
        ‖right.error‖ ≤ p08GammaReal (r : ℝ) u *
            ‖middle.result‖ * ‖XBᵀ‖ := p08_stage_error_norm right
        _ = h * ‖middle.result‖ := by
          rw [Matrix.frobenius_norm_transpose, p08_ortho_norm' XB hXB]
          dsimp [h]
          ring
        _ ≤ h * ((1 + a) * P) := mul_le_mul_of_nonneg_left hmiddle hh
        _ = h * (1 + a) * P := by ring
    have hright : ‖right.result‖ ≤ (1 + h) * (1 + a) * P := by
      rw [p08_stage_result_eq]
      calc
        ‖middle.result * XBᵀ + right.error‖ ≤
            ‖middle.result * XBᵀ‖ + ‖right.error‖ := norm_add_le _ _
        _ ≤ (1 + a) * P + h * (1 + a) * P := by
          rw [p08_ortho_mul_right_norm XB hXB]
          exact add_le_add hmiddle he
        _ = (1 + h) * (1 + a) * P := by ring
    have hf : ‖final.error‖ ≤ h * (1 + h) * (1 + a) * P := by
      calc
        ‖final.error‖ ≤ p08GammaReal (r : ℝ) u * ‖XA‖ * ‖right.result‖ :=
          p08_stage_error_norm final
        _ = h * ‖right.result‖ := by
          rw [p08_ortho_norm' XA hXA]
        _ ≤ h * ((1 + h) * (1 + a) * P) :=
          mul_le_mul_of_nonneg_left hright hh
        _ = h * (1 + h) * (1 + a) * P := by ring
    have herr : final.result -
        p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
        (XA * middle.error) * XBᵀ + XA * right.error + final.error := by
      let e1 := middle.error
      let e2 := right.error
      let e3 := final.error
      change (XA * right.result + e3) -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
          (XA * e1) * XBᵀ + XA * e2 + e3
      rw [p08_stage_result_eq right]
      change XA * (middle.result * XBᵀ + right.error) + e3 -
          p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB) =
          (XA * e1) * XBᵀ + XA * e2 + e3
      have hfirst : middle.result * XBᵀ =
          (YAᵀ * YB + middle.error) * XBᵀ :=
        congrArg (fun M => M * XBᵀ) (p08_stage_result_eq middle)
      rw [hfirst]
      dsimp only [e1, e2, e3]
      simp only [p08_mat_mul_eq, p08_low_rank_eq, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      abel
    change ‖final.result -
      p08MatMul (p08LowRankMatrix XA YA) (p08LowRankMatrix YB XB)‖ ≤ _
    rw [herr]
    calc
      ‖(XA * middle.error) * XBᵀ + XA * right.error + final.error‖ ≤
          ‖(XA * middle.error) * XBᵀ‖ + ‖XA * right.error‖ +
            ‖final.error‖ := by
        linarith [norm_add_le ((XA * middle.error) * XBᵀ + XA * right.error)
            final.error,
          norm_add_le ((XA * middle.error) * XBᵀ) (XA * right.error)]
      _ = ‖middle.error‖ + ‖right.error‖ + ‖final.error‖ := by
        rw [p08_ortho_mul_right_norm XB hXB,
          p08_ortho_mul_norm' XA hXA,
          p08_ortho_mul_norm' XA hXA]
      _ ≤ a * P + h * (1 + a) * P + h * (1 + h) * (1 + a) * P := by
        exact add_le_add (add_le_add hm he) hf
      _ = (a + h * (1 + a) + h * (1 + h) * (1 + a)) * P := by ring

private lemma p08_perturb_bound {b : ℕ}
    (A B EA EB C : P08Matrix b) (g eA eB : ℝ)
    (hg : 0 ≤ g) (hEA : ‖EA‖ ≤ eA) (hEB : ‖EB‖ ≤ eB)
    (hfirst : ‖C - (A + EA) * (B + EB)‖ ≤
      g * ‖A + EA‖ * ‖B + EB‖) :
    ‖C - A * B‖ ≤ g * ‖A‖ * ‖B‖ +
      (1 + g) * (eA * ‖B‖ + ‖A‖ * eB + eA * eB) := by
  have heA0 : 0 ≤ eA := (norm_nonneg _).trans hEA
  have heB0 : 0 ≤ eB := (norm_nonneg _).trans hEB
  have hAn : ‖A + EA‖ ≤ ‖A‖ + eA :=
    (norm_add_le A EA).trans (add_le_add_right hEA _)
  have hBn : ‖B + EB‖ ≤ ‖B‖ + eB :=
    (norm_add_le B EB).trans (add_le_add_right hEB _)
  have hG : ‖EA * B + A * EB + EA * EB‖ ≤
      eA * ‖B‖ + ‖A‖ * eB + eA * eB := by
    calc
      ‖EA * B + A * EB + EA * EB‖ ≤
          ‖EA * B‖ + ‖A * EB‖ + ‖EA * EB‖ := by
        linarith [norm_add_le (EA * B + A * EB) (EA * EB),
          norm_add_le (EA * B) (A * EB)]
      _ ≤ ‖EA‖ * ‖B‖ + ‖A‖ * ‖EB‖ + ‖EA‖ * ‖EB‖ := by
        exact add_le_add
          (add_le_add (Matrix.frobenius_norm_mul EA B)
            (Matrix.frobenius_norm_mul A EB))
          (Matrix.frobenius_norm_mul EA EB)
      _ ≤ eA * ‖B‖ + ‖A‖ * eB + eA * eB := by
        gcongr
  have hdecomp : C - A * B =
      (C - (A + EA) * (B + EB)) + (EA * B + A * EB + EA * EB) := by
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  rw [hdecomp]
  calc
    ‖C - (A + EA) * (B + EB) + (EA * B + A * EB + EA * EB)‖ ≤
        ‖C - (A + EA) * (B + EB)‖ + ‖EA * B + A * EB + EA * EB‖ :=
      norm_add_le _ _
    _ ≤ g * ‖A + EA‖ * ‖B + EB‖ +
          (eA * ‖B‖ + ‖A‖ * eB + eA * eB) := add_le_add hfirst hG
    _ ≤ g * (‖A‖ + eA) * (‖B‖ + eB) +
          (eA * ‖B‖ + ‖A‖ * eB + eA * eB) := by
      gcongr
    _ = g * ‖A‖ * ‖B‖ +
          (1 + g) * (eA * ‖B‖ + ‖A‖ * eB + eA * eB) := by ring

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
  dsimp
  simp only [p08FrobNorm, p08_rect_norm_eq]
  let At := p08LowRankMatrix run.XA run.YA
  let Bt := p08LowRankMatrix run.YB run.XB
  let g := p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
  let a := p08GammaReal (b : ℝ) run.unitRoundoff
  let h := p08GammaReal (r : ℝ) run.unitRoundoff * Real.sqrt (r : ℝ)
  have hAt : ‖At‖ = ‖run.YA‖ := p08_approx_norm_left run.XA run.YA run.xA_orthonormal
  have hBt : ‖Bt‖ = ‖run.YB‖ := p08_approx_norm_right run.XB run.YB run.xB_orthonormal
  have ht := p08_trace_bound run.unitRoundoff_nonneg run.gamma_valid
    run.XA run.YA run.XB run.YB run.xA_orthonormal run.xB_orthonormal run.trace
  dsimp at ht
  have hc := p08_gamma_cost b r run.unitRoundoff
    run.unitRoundoff_nonneg run.gamma_valid
  dsimp at hc
  have hfirst : ‖run.trace.result - p08MatMul At Bt‖ ≤ g * ‖At‖ * ‖Bt‖ := by
    calc
      ‖run.trace.result - p08MatMul At Bt‖ ≤
          (a + h * (1 + a) + h * (1 + h) * (1 + a)) *
            (‖run.YA‖ * ‖run.YB‖) := ht
      _ = (a + h * (1 + a) + h * (1 + h) * (1 + a)) *
            (‖At‖ * ‖Bt‖) := by rw [hAt, hBt]
      _ ≤ g * (‖At‖ * ‖Bt‖) := by
        exact mul_le_mul_of_nonneg_right hc
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = g * ‖At‖ * ‖Bt‖ := by ring
  constructor
  · exact hfirst
  · have hg : 0 ≤ g :=
      p08_gamma_nonneg _ _
        (by
          have := (p08_cost_bounds b r).1
          exact (Nat.cast_nonneg b).trans this)
        run.unitRoundoff_nonneg run.gamma_valid
    have hEA : ‖run.approximationErrorA‖ ≤ run.epsilon * run.betaA := by
      simpa only [p08FrobNorm, p08_rect_norm_eq] using run.approximationErrorA_le
    have hEB : ‖run.approximationErrorB‖ ≤ run.epsilon * run.betaB := by
      simpa only [p08FrobNorm, p08_rect_norm_eq] using run.approximationErrorB_le
    have hfirst' : ‖run.trace.result -
        (run.A + run.approximationErrorA) *
          (run.B + run.approximationErrorB)‖ ≤
        g * ‖run.A + run.approximationErrorA‖ *
          ‖run.B + run.approximationErrorB‖ := by
      simpa only [At, Bt, run.approximationA_eq,
        run.approximationB_eq, p08_mat_mul_eq] using hfirst
    have hp := p08_perturb_bound run.A run.B run.approximationErrorA
      run.approximationErrorB run.trace.result g
      (run.epsilon * run.betaA) (run.epsilon * run.betaB)
      hg hEA hEB hfirst'
    rw [p08_mat_mul_eq]
    convert hp using 1; ring

end VSCLReuse

import VSCLReuse.P25.Definitions

namespace VSCLReuse

open Filter

/-- P25-C1: the R-quadratic residual-ratio core of Theorem 2.3. -/
theorem p25_c1_choice_two_r_quadratic_core
    (residual : ℕ → ℝ) (B : ℝ)
    (hpos : ∀ k, 0 < residual k) (hB : 0 < B)
    (hstep : ∀ k,
      residual (k + 2) ≤
        ((p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)) *
          residual (k + 1))
    (hsmall :
      2 * p25ResidualRatio residual 0 + 2 * B * residual 0 ≤ 1) :
    let D := 1 / (2 * p25ResidualRatio residual 0)
    1 < D ∧
      p25ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k,
        0 < p25ScaledResidualRatio residual D k ∧
        p25ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0) := by
  -- PROOF_START P25-C1-H001
  let t := p25ResidualRatio residual 0
  let c := 2 * t
  let D := 1 / c
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have htpos : 0 < t := by
    dsimp [t, p25ResidualRatio]
    exact div_pos (hpos 1) (hpos 0)
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hsmall' : c + 2 * B * residual 0 ≤ 1 := hsmall
  have hcle : c ≤ 1 := by nlinarith [mul_pos hB (hpos 0)]
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hDgt : 1 < D := by
    dsimp [D]
    exact (one_lt_div₀ hcpos).2 (by nlinarith [mul_pos hB (hpos 0)])
  have hDc : D * c = 1 := by
    dsimp [D]
    field_simp
  have hqpos (k : ℕ) : 0 < q k := by dsimp [q]; positivity
  have hqsq (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    simp only [q, pow_succ, pow_mul]
  have hratio_pos (k : ℕ) : 0 < p25ResidualRatio residual k := by
    dsimp [p25ResidualRatio]
    exact div_pos (hpos (k + 1)) (hpos k)
  have hscaled_pos (k : ℕ) : 0 < p25ScaledResidualRatio residual D k := by
    exact mul_pos hDpos (hratio_pos k)
  have hratio_step (k : ℕ) :
      p25ResidualRatio residual (k + 1) ≤
        (p25ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [p25ResidualRatio, Nat.add_assoc] using hstep k
  have hratio_mul (k : ℕ) :
      residual (k + 1) = p25ResidualRatio residual k * residual k := by
    dsimp [p25ResidualRatio]
    rw [div_mul_cancel₀]
    exact ne_of_gt (hpos k)
  have hratio_scaled (k : ℕ) :
      p25ResidualRatio residual k =
        c * p25ScaledResidualRatio residual D k := by
    dsimp [p25ScaledResidualRatio]
    calc
      p25ResidualRatio residual k = (D * c) * p25ResidualRatio residual k := by rw [hDc]; ring
      _ = c * (D * p25ResidualRatio residual k) := by ring
  have hbeta0 : p25ScaledResidualRatio residual D 0 = 1 / 2 := by
    dsimp [p25ScaledResidualRatio, t, c] at hDc ⊢
    nlinarith [hDc]
  have hq0 : q 0 = 1 / 2 := by norm_num [q]
  have hres0 : residual 1 ≤ 2 * c * residual 0 * q 1 := by
    rw [hratio_mul 0]
    change t * residual 0 ≤ 2 * c * residual 0 * q 1
    have hq1 : q 1 = 1 / 4 := by norm_num [q]
    rw [hq1]
    dsimp [c]
    convert le_refl (t * residual 0) using 1; ring
  have hind (k : ℕ) :
      p25ScaledResidualRatio residual D k ≤ q k ∧
        residual (k + 1) ≤ 2 * c * residual 0 * q (k + 1) := by
    induction k with
    | zero =>
        constructor
        · rw [hbeta0, hq0]
        · exact hres0
    | succ k ih =>
        rcases ih with ⟨hbeta, hres⟩
        have htauk : p25ResidualRatio residual k ≤ c * q k := by
          rw [hratio_scaled k]
          exact mul_le_mul_of_nonneg_left hbeta hcpos.le
        have hbetanext : p25ScaledResidualRatio residual D (k + 1) ≤ q (k + 1) := by
          calc
            p25ScaledResidualRatio residual D (k + 1) =
                D * p25ResidualRatio residual (k + 1) := rfl
            _ ≤ D * ((p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hratio_step k) hDpos.le
            _ ≤ D * ((c * q k) ^ 2 + B * (2 * c * residual 0 * q (k + 1))) := by
              gcongr
              exact (hratio_pos k).le
            _ = (c + 2 * B * residual 0) * q (k + 1) := by
              rw [hqsq k]
              calc
                D * ((c * q k) ^ 2 + B * (2 * c * residual 0 * (q k) ^ 2)) =
                    (D * c) * ((c + 2 * B * residual 0) * (q k) ^ 2) := by ring
                _ = (c + 2 * B * residual 0) * (q k) ^ 2 := by rw [hDc]; ring
            _ ≤ q (k + 1) := by
              convert mul_le_mul_of_nonneg_right hsmall' (hqpos (k + 1)).le using 1; ring
        have htaunext : p25ResidualRatio residual (k + 1) ≤ c * q (k + 1) := by
          rw [hratio_scaled (k + 1)]
          exact mul_le_mul_of_nonneg_left hbetanext hcpos.le
        constructor
        · exact hbetanext
        · change residual (k + 2) ≤ 2 * c * residual 0 * q (k + 2)
          rw [hratio_mul (k + 1), hqsq (k + 1)]
          calc
            p25ResidualRatio residual (k + 1) * residual (k + 1) ≤
                (c * q (k + 1)) * (2 * c * residual 0 * q (k + 1)) := by
              exact mul_le_mul htaunext hres (hpos (k + 1)).le
                (mul_nonneg hcpos.le (hqpos (k + 1)).le)
            _ = c * (2 * c * residual 0 * (q (k + 1)) ^ 2) := by ring
            _ ≤ 1 * (2 * c * residual 0 * (q (k + 1)) ^ 2) := by
              exact mul_le_mul_of_nonneg_right hcle
                (by exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcpos.le)
                  (hpos 0).le) (sq_nonneg _))
            _ = 2 * c * residual 0 * (q (k + 1)) ^ 2 := by ring
  have hq_tendsto : Tendsto q atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  have hscaled_tendsto : Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0) := by
    apply squeeze_zero (fun k => (hscaled_pos k).le) (fun k => (hind k).1)
    exact hq_tendsto
  change 1 < D ∧
    p25ScaledResidualRatio residual D 0 = 1 / 2 ∧
      (∀ k, 0 < p25ScaledResidualRatio residual D k ∧
        p25ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
      Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0)
  exact ⟨hDgt, hbeta0, (fun k => ⟨hscaled_pos k, (hind k).1⟩), hscaled_tendsto⟩

end VSCLReuse

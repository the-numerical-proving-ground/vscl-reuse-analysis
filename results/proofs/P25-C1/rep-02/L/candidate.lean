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
  let t : ℕ → ℝ := p25ResidualRatio residual
  let D : ℝ := 1 / (2 * t 0)
  let w : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have htpos (k : ℕ) : 0 < t k := by
    change 0 < residual (k + 1) / residual k
    exact div_pos (hpos (k + 1)) (hpos k)
  have htmul (k : ℕ) : t k * residual k = residual (k + 1) := by
    change residual (k + 1) / residual k * residual k = residual (k + 1)
    exact div_mul_cancel₀ _ (ne_of_gt (hpos k))
  have hsmall' : 2 * t 0 + 2 * B * residual 0 ≤ 1 := hsmall
  have htwo : 2 * t 0 < 1 := by
    have hp : 0 < B * residual 0 := mul_pos hB (hpos 0)
    linarith
  have hDpos : 0 < D := by
    dsimp [D]
    exact div_pos (by norm_num) (mul_pos (by norm_num) (htpos 0))
  have hDgt1 : 1 < D := by
    dsimp [D]
    apply (one_lt_div (mul_pos (by norm_num) (htpos 0))).2
    linarith
  have hDmul : 2 * D * t 0 = 1 := by
    dsimp [D]
    field_simp [ne_of_gt (htpos 0)]
  have hwpos (k : ℕ) : 0 < w k := by
    dsimp [w]
    positivity
  have hw_succ (k : ℕ) : w (k + 1) = (w k) ^ 2 := by
    change (1 / 2 : ℝ) ^ (2 ^ (k + 1)) = ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2
    rw [pow_succ, pow_mul]
  have htstep (k : ℕ) : t (k + 1) ≤ (t k) ^ 2 + B * residual (k + 1) := by
    change residual (k + 2) / residual (k + 1) ≤
      (t k) ^ 2 + B * residual (k + 1)
    apply (div_le_iff₀ (hpos (k + 1))).2
    exact hstep k
  have hbeta0 : D * t 0 = 1 / 2 := by
    nlinarith [hDmul]
  have hpair : ∀ k : ℕ,
      D * t k ≤ w k ∧
      D * residual (k + 1) ≤ 2 * residual 0 * w (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [w] using le_of_eq hbeta0
        · have heq : D * residual 1 = (D * t 0) * residual 0 := by
            rw [← htmul 0]
            ring
          rw [heq, hbeta0]
          norm_num [w]
          nlinarith
    | succ k ih =>
        have hsq : (D * t k) ^ 2 ≤ (w k) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg hDpos.le (htpos k).le) ih.1 2
        have hterm1 : D * (t k) ^ 2 ≤ (2 * t 0) * w (k + 1) := by
          calc
            D * (t k) ^ 2 = (2 * D * t 0) * (D * (t k) ^ 2) := by rw [hDmul]; ring
            _ = (2 * t 0) * (D * t k) ^ 2 := by ring
            _ ≤ (2 * t 0) * (w k) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq
                (mul_nonneg (by norm_num) (htpos 0).le)
            _ = (2 * t 0) * w (k + 1) := by rw [hw_succ]
        have hterm2 : D * B * residual (k + 1) ≤
            (2 * B * residual 0) * w (k + 1) := by
          calc
            D * B * residual (k + 1) = B * (D * residual (k + 1)) := by ring
            _ ≤ B * (2 * residual 0 * w (k + 1)) :=
              mul_le_mul_of_nonneg_left ih.2 hB.le
            _ = (2 * B * residual 0) * w (k + 1) := by ring
        have hq : D * t (k + 1) ≤ w (k + 1) := by
          calc
            D * t (k + 1) ≤ D * ((t k) ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (htstep k) hDpos.le
            _ = D * (t k) ^ 2 + D * B * residual (k + 1) := by ring
            _ ≤ (2 * t 0) * w (k + 1) +
                (2 * B * residual 0) * w (k + 1) := add_le_add hterm1 hterm2
            _ = (2 * t 0 + 2 * B * residual 0) * w (k + 1) := by ring
            _ ≤ 1 * w (k + 1) :=
              mul_le_mul_of_nonneg_right hsmall' (hwpos (k + 1)).le
            _ = w (k + 1) := one_mul _
        constructor
        · exact hq
        · have hrle : residual (k + 1) ≤ D * residual (k + 1) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hDgt1.le) (hpos (k + 1)).le]
          calc
            D * residual (k + 2) =
                (D * t (k + 1)) * residual (k + 1) := by
                  rw [← htmul (k + 1)]
                  ring
            _ ≤ w (k + 1) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right hq (hpos (k + 1)).le
            _ ≤ w (k + 1) * (D * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left hrle (hwpos (k + 1)).le
            _ ≤ w (k + 1) * (2 * residual 0 * w (k + 1)) :=
              mul_le_mul_of_nonneg_left ih.2 (hwpos (k + 1)).le
            _ = 2 * residual 0 * w (k + 2) := by
              rw [hw_succ (k + 1)]
              ring
  have hwlim : Tendsto w atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexp : Tendsto (fun n : ℕ => (2 : ℕ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    simpa [w] using hbase.comp hexp
  change 1 < D ∧ p25ScaledResidualRatio residual D 0 = 1 / 2 ∧
    (∀ k, 0 < p25ScaledResidualRatio residual D k ∧
      p25ScaledResidualRatio residual D k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
    Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0)
  refine ⟨hDgt1, ?_, ?_, ?_⟩
  · change D * t 0 = 1 / 2
    exact hbeta0
  · intro k
    constructor
    · change 0 < D * t k
      exact mul_pos hDpos (htpos k)
    · change D * t k ≤ w k
      exact (hpair k).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwlim
    · intro k
      change 0 ≤ D * t k
      exact (mul_pos hDpos (htpos k)).le
    · intro k
      change D * t k ≤ w k
      exact (hpair k).1

end VSCLReuse

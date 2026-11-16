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
  let D : ℝ := 1 / (2 * p25ResidualRatio residual 0)
  let q : ℕ → ℝ := p25ScaledResidualRatio residual D
  let A : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have hrpos (k : ℕ) : 0 < p25ResidualRatio residual k := by
    exact div_pos (hpos (k + 1)) (hpos k)
  have hbrpos : 0 < B * residual 0 := mul_pos hB (hpos 0)
  have htwo_r : 2 * p25ResidualRatio residual 0 < 1 := by
    linarith
  have hDgt : 1 < D := by
    dsimp [D]
    apply (lt_div_iff₀ (mul_pos (by norm_num) (hrpos 0))).2
    simpa using htwo_r
  have hDpos : 0 < D := lt_trans zero_lt_one hDgt
  have hDmul : D * (2 * p25ResidualRatio residual 0) = 1 := by
    dsimp [D]
    field_simp [ne_of_gt (hrpos 0)]
  have hDinv : 1 / D = 2 * p25ResidualRatio residual 0 := by
    apply (div_eq_iff (ne_of_gt hDpos)).2
    nlinarith [hDmul]
  have hcoeff : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hDinv]
    exact hsmall
  have hqpos (k : ℕ) : 0 < q k := mul_pos hDpos (hrpos k)
  have hqzero : q 0 = 1 / 2 := by
    change D * p25ResidualRatio residual 0 = 1 / 2
    nlinarith [hDmul]
  have hApos (k : ℕ) : 0 < A k := by
    dsimp [A]
    positivity
  have hAzero : A 0 = 1 / 2 := by
    simp [A]
  have hAsucc (k : ℕ) : A (k + 1) = (A k) ^ 2 := by
    dsimp [A]
    rw [pow_succ, pow_mul]
  have hresratio (k : ℕ) :
      residual (k + 1) = p25ResidualRatio residual k * residual k := by
    dsimp [p25ResidualRatio]
    field_simp [ne_of_gt (hpos k)]
  have hstep_ratio (k : ℕ) :
      p25ResidualRatio residual (k + 1) ≤
        (p25ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    change residual (k + 2) / residual (k + 1) ≤
      (p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)
    exact (div_le_iff₀ (hpos (k + 1))).2 (hstep k)
  have hquad (k : ℕ) :
      D * (p25ResidualRatio residual k) ^ 2 = (1 / D) * (q k) ^ 2 := by
    change D * (p25ResidualRatio residual k) ^ 2 =
      (1 / D) * (D * p25ResidualRatio residual k) ^ 2
    field_simp [ne_of_gt hDpos]
  have hqstep (k : ℕ) :
      q (k + 1) ≤ (1 / D) * (q k) ^ 2 + B * (D * residual (k + 1)) := by
    calc
      q (k + 1) = D * p25ResidualRatio residual (k + 1) := rfl
      _ ≤ D * ((p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)) :=
        mul_le_mul_of_nonneg_left (hstep_ratio k) hDpos.le
      _ = (1 / D) * (q k) ^ 2 + B * (D * residual (k + 1)) := by
        rw [← hquad k]
        ring
  have hmain : ∀ k, q k ≤ A k ∧ residual k ≤ 2 * residual 0 * A k := by
    intro k
    induction k with
    | zero =>
        constructor
        · rw [hqzero, hAzero]
        · rw [hAzero]
          nlinarith
    | succ k ih =>
        obtain ⟨hqk, hresk⟩ := ih
        have hscaledres : D * residual (k + 1) ≤
            2 * residual 0 * A (k + 1) := by
          have hprod := mul_le_mul hqk hresk (hpos k).le (hApos k).le
          calc
            D * residual (k + 1) = q k * residual k := by
              rw [hresratio k]
              change D * (p25ResidualRatio residual k * residual k) =
                (D * p25ResidualRatio residual k) * residual k
              ring
            _ ≤ A k * (2 * residual 0 * A k) := hprod
            _ = 2 * residual 0 * A (k + 1) := by
              rw [hAsucc]
              ring
        have hsq : (q k) ^ 2 ≤ A (k + 1) := by
          rw [hAsucc]
          nlinarith [mul_nonneg (show 0 ≤ A k - q k by linarith)
            (show 0 ≤ A k + q k by linarith [hqpos k, hApos k])]
        have hqnext : q (k + 1) ≤ A (k + 1) := by
          calc
            q (k + 1) ≤ (1 / D) * (q k) ^ 2 +
                B * (D * residual (k + 1)) := hqstep k
            _ ≤ (1 / D) * A (k + 1) +
                B * (2 * residual 0 * A (k + 1)) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hsq (by positivity))
                (mul_le_mul_of_nonneg_left hscaledres hB.le)
            _ = (1 / D + 2 * B * residual 0) * A (k + 1) := by ring
            _ ≤ A (k + 1) := by
              have hh := mul_nonneg (show 0 ≤ 1 - (1 / D + 2 * B * residual 0) by
                linarith [hcoeff]) (hApos (k + 1)).le
              nlinarith
        have hresnext : residual (k + 1) ≤ 2 * residual 0 * A (k + 1) := by
          have hh := mul_nonneg (show 0 ≤ D - 1 by linarith [hDgt])
            (hpos (k + 1)).le
          nlinarith [hscaledres]
        exact ⟨hqnext, hresnext⟩
  have hAlim : Tendsto A atTop (nhds 0) := by
    have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hexp : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
    exact hpow.comp hexp
  change 1 < D ∧ q 0 = 1 / 2 ∧
    (∀ k, 0 < q k ∧ q k ≤ A k) ∧ Tendsto q atTop (nhds 0)
  refine ⟨hDgt, hqzero, ?_, ?_⟩
  · intro k
    exact ⟨hqpos k, (hmain k).1⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAlim
    · intro k
      exact (hqpos k).le
    · intro k
      exact (hmain k).1

end VSCLReuse

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
  let r : ℕ → ℝ := p25ResidualRatio residual
  let D : ℝ := 1 / (2 * r 0)
  let β : ℕ → ℝ := p25ScaledResidualRatio residual D
  change 1 < D ∧ β 0 = 1 / 2 ∧
    (∀ k, 0 < β k ∧ β k ≤ (1 / 2 : ℝ) ^ (2 ^ k)) ∧
    Tendsto β atTop (nhds 0)
  have hrpos (k : ℕ) : 0 < r k := by
    dsimp [r, p25ResidualRatio]
    exact div_pos (hpos (k + 1)) (hpos k)
  have hden : 0 < 2 * r 0 := mul_pos (by norm_num) (hrpos 0)
  have hDpos : 0 < D := by
    dsimp [D]
    exact one_div_pos.mpr hden
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hDinv : 1 / D = 2 * r 0 := by
    dsimp [D]
    field_simp [ne_of_gt hden]
  have hrlt : 2 * r 0 < 1 := by
    have ht : 0 < 2 * B * residual 0 :=
      mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    linarith
  have hDgt : 1 < D := by
    dsimp [D]
    exact one_lt_one_div hden hrlt
  have hcoeff : 1 / D + 2 * B * residual 0 ≤ 1 := by
    rw [hDinv]
    exact hsmall
  have hβpos (k : ℕ) : 0 < β k := by
    dsimp [β, p25ScaledResidualRatio]
    exact mul_pos hDpos (hrpos k)
  have hβzero : β 0 = 1 / 2 := by
    change (1 / (2 * r 0)) * r 0 = 1 / 2
    field_simp [ne_of_gt (hrpos 0)]
  have hratio_mul (k : ℕ) : r k * residual k = residual (k + 1) := by
    dsimp [r, p25ResidualRatio]
    field_simp [ne_of_gt (hpos k)]
  have hDres (k : ℕ) : D * residual (k + 1) = β k * residual k := by
    rw [← hratio_mul k]
    dsimp [β, p25ScaledResidualRatio]
    ring
  have hratio_step (k : ℕ) : r (k + 1) ≤ r k ^ 2 + B * residual (k + 1) := by
    dsimp [r, p25ResidualRatio]
    exact (div_le_iff₀ (hpos (k + 1))).2 (hstep k)
  have hβstep (k : ℕ) :
      β (k + 1) ≤ (1 / D) * (β k) ^ 2 + B * (D * residual (k + 1)) := by
    have hk := mul_le_mul_of_nonneg_left (hratio_step k) hDpos.le
    calc
      β (k + 1) = D * r (k + 1) := rfl
      _ ≤ D * (r k ^ 2 + B * residual (k + 1)) := hk
      _ = (1 / D) * (β k) ^ 2 + B * (D * residual (k + 1)) := by
        dsimp [β, p25ScaledResidualRatio]
        field_simp
        ring
  have hpowsq (k : ℕ) :
      ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 = (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
    calc
      ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 = (1 / 2 : ℝ) ^ (2 ^ k * 2) := by rw [pow_mul]
      _ = (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by rw [pow_succ]
  have hbound (k : ℕ) :
      β k ≤ (1 / 2 : ℝ) ^ (2 ^ k) ∧
      D * residual (k + 1) ≤
        2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
    induction k with
    | zero =>
        constructor
        · simp [hβzero]
        · calc
            D * residual (0 + 1) = β 0 * residual 0 := hDres 0
            _ = 2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (0 + 1)) := by
              rw [hβzero]
              norm_num
              ring
            _ ≤ _ := le_refl _
    | succ k ih =>
        obtain ⟨hβk, hRk⟩ := ih
        have hsqr : (β k) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 :=
          pow_le_pow_left₀ (hβpos k).le hβk 2
        have hβnext : β (k + 1) ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
          calc
            β (k + 1) ≤ (1 / D) * (β k) ^ 2 + B * (D * residual (k + 1)) :=
              hβstep k
            _ ≤ (1 / D) * ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 +
                  B * (2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1))) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hsqr (one_div_pos.mpr hDpos).le)
                (mul_le_mul_of_nonneg_left hRk hB.le)
            _ = (1 / D + 2 * B * residual 0) *
                  (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
              rw [hpowsq]
              ring
            _ ≤ 1 * (1 / 2 : ℝ) ^ (2 ^ (k + 1)) :=
              mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by norm_num) _)
            _ = _ := one_mul _
        have hresle : residual (k + 1) ≤ D * residual (k + 1) := by
          nlinarith [hDgt, hpos (k + 1)]
        have hRnext :
            D * residual ((k + 1) + 1) ≤
              2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ ((k + 1) + 1)) := by
          calc
            D * residual ((k + 1) + 1) = β (k + 1) * residual (k + 1) :=
              hDres (k + 1)
            _ ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right hβnext (hpos (k + 1)).le
            _ ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) *
                  (D * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left hresle (pow_nonneg (by norm_num) _)
            _ ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) *
                  (2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ (k + 1))) :=
              mul_le_mul_of_nonneg_left hRk (pow_nonneg (by norm_num) _)
            _ = 2 * residual 0 * (1 / 2 : ℝ) ^ (2 ^ ((k + 1) + 1)) := by
              rw [← hpowsq (k + 1)]
              ring
        exact ⟨hβnext, hRnext⟩
  have htwo (k : ℕ) : k ≤ 2 ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hpowpos : 0 < 2 ^ k := pow_pos (by norm_num) _
        omega
  refine ⟨hDgt, hβzero, ?_, ?_⟩
  · intro k
    exact ⟨hβpos k, (hbound k).1⟩
  · have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hpowle (k : ℕ) : (1 / 2 : ℝ) ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num) (htwo k)
    exact squeeze_zero (fun k => (hβpos k).le)
      (fun k => (hbound k).1.trans (hpowle k)) hlim

end VSCLReuse

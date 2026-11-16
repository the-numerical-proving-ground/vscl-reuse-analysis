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
  let a : ℝ := p25ResidualRatio residual 0
  let D : ℝ := 1 / (2 * a)
  let c : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  have ha : 0 < a := by
    dsimp [a, p25ResidualRatio]
    exact div_pos (hpos 1) (hpos 0)
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDtwoa : D * (2 * a) = 1 := by
    simpa [D] using (one_div_mul_cancel (by positivity : (2 * a : ℝ) ≠ 0))
  have hDa : D * a = 1 / 2 := by
    calc
      D * a = (D * (2 * a)) / 2 := by ring
      _ = 1 / 2 := by rw [hDtwoa]
  have hcoef : 2 * a + 2 * B * residual 0 ≤ 1 := hsmall
  have htwoa : 2 * a ≤ 1 := by
    have hbr : 0 ≤ 2 * B * residual 0 := by
      exact mul_nonneg (mul_nonneg (by norm_num) hB.le) (hpos 0).le
    linarith
  have hDgt : 1 < D := by
    dsimp [D]
    apply (lt_div_iff₀ (mul_pos (by norm_num) ha)).2
    have hbr : 0 < 2 * B * residual 0 := by
      exact mul_pos (mul_pos (by norm_num) hB) (hpos 0)
    nlinarith
  have hratio (k : ℕ) :
      residual (k + 1) = p25ResidualRatio residual k * residual k := by
    rw [p25ResidualRatio]
    exact (div_mul_cancel₀ _ (ne_of_gt (hpos k))).symm
  have hstep_ratio (k : ℕ) :
      p25ResidualRatio residual (k + 1) ≤
        (p25ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    change residual (k + 2) / residual (k + 1) ≤ _
    exact (div_le_iff₀ (hpos (k + 1))).2 (hstep k)
  have hscaled (k : ℕ) :
      p25ResidualRatio residual k =
        (2 * a) * p25ScaledResidualRatio residual D k := by
    unfold p25ScaledResidualRatio
    calc
      p25ResidualRatio residual k = 1 * p25ResidualRatio residual k := by ring
      _ = (D * (2 * a)) * p25ResidualRatio residual k := by rw [hDtwoa]
      _ = (2 * a) * (D * p25ResidualRatio residual k) := by ring
  have hcnext (k : ℕ) : c (k + 1) = (c k) ^ 2 := by
    simp only [c, pow_succ, pow_mul]
  have hcpos (k : ℕ) : 0 < c k := by
    dsimp [c]
    positivity
  have hmain : ∀ k : ℕ,
      0 < p25ScaledResidualRatio residual D k ∧
      p25ScaledResidualRatio residual D k ≤ c k ∧
      residual (k + 1) ≤ 4 * a * residual 0 * (c k) ^ 2 := by
    intro k
    induction k with
    | zero =>
        have hb0 : p25ScaledResidualRatio residual D 0 = 1 / 2 := by
          change D * a = 1 / 2
          exact hDa
        have hr0 : residual 1 = a * residual 0 := by
          simpa [a] using hratio 0
        constructor
        · change 0 < D * a
          positivity
        constructor
        · simpa [c] using hb0.le
        · apply le_of_eq
          calc
            residual (0 + 1) = a * residual 0 := hr0
            _ = 4 * a * residual 0 * (c 0) ^ 2 := by norm_num [c]; ring
    | succ k ih =>
        rcases ih with ⟨hbpos, hble, hrbound⟩
        have hsq : (p25ScaledResidualRatio residual D k) ^ 2 ≤ (c k) ^ 2 := by
          nlinarith [sq_nonneg (c k - p25ScaledResidualRatio residual D k)]
        have hscaled_step :
            p25ScaledResidualRatio residual D (k + 1) ≤
              (2 * a) * (p25ScaledResidualRatio residual D k) ^ 2 +
                D * B * residual (k + 1) := by
          change D * p25ResidualRatio residual (k + 1) ≤ _
          calc
            D * p25ResidualRatio residual (k + 1) ≤
                D * ((p25ResidualRatio residual k) ^ 2 + B * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left (hstep_ratio k) hDpos.le
            _ = (2 * a) * (p25ScaledResidualRatio residual D k) ^ 2 +
                  D * B * residual (k + 1) := by
              rw [hscaled k]
              calc
                D * (((2 * a) * p25ScaledResidualRatio residual D k) ^ 2 +
                    B * residual (k + 1)) =
                    (D * (2 * a)) * ((2 * a) *
                      (p25ScaledResidualRatio residual D k) ^ 2) +
                      D * B * residual (k + 1) := by ring
                _ = _ := by rw [hDtwoa]; ring
        have hterm :
            D * B * residual (k + 1) ≤
              (2 * B * residual 0) * (c k) ^ 2 := by
          calc
            D * B * residual (k + 1) ≤
                D * B * (4 * a * residual 0 * (c k) ^ 2) :=
              mul_le_mul_of_nonneg_left hrbound (by positivity)
            _ = (D * (2 * a)) * ((2 * B * residual 0) * (c k) ^ 2) := by ring
            _ = (2 * B * residual 0) * (c k) ^ 2 := by rw [hDtwoa]; ring
        have hbnext :
            p25ScaledResidualRatio residual D (k + 1) ≤ c (k + 1) := by
          calc
            p25ScaledResidualRatio residual D (k + 1) ≤
                (2 * a) * (p25ScaledResidualRatio residual D k) ^ 2 +
                  D * B * residual (k + 1) := hscaled_step
            _ ≤ (2 * a) * (c k) ^ 2 +
                  (2 * B * residual 0) * (c k) ^ 2 :=
              add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity)) hterm
            _ = (2 * a + 2 * B * residual 0) * (c k) ^ 2 := by ring
            _ ≤ 1 * (c k) ^ 2 :=
              mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
            _ = c (k + 1) := by rw [hcnext]; ring
        have ht_next_le :
            p25ResidualRatio residual (k + 1) ≤ (2 * a) * c (k + 1) := by
          rw [hscaled (k + 1)]
          exact mul_le_mul_of_nonneg_left hbnext (by positivity)
        have hrnext :
            residual ((k + 1) + 1) ≤
              4 * a * residual 0 * (c (k + 1)) ^ 2 := by
          calc
            residual ((k + 1) + 1) =
                p25ResidualRatio residual (k + 1) * residual (k + 1) := hratio (k + 1)
            _ ≤ (2 * a) * c (k + 1) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right ht_next_le (hpos (k + 1)).le
            _ ≤ (2 * a) * c (k + 1) *
                  (4 * a * residual 0 * (c k) ^ 2) :=
              mul_le_mul_of_nonneg_left hrbound (by positivity)
            _ = (2 * a) * (4 * a * residual 0 * (c (k + 1)) ^ 2) := by
              rw [hcnext]
              ring
            _ ≤ 1 * (4 * a * residual 0 * (c (k + 1)) ^ 2) :=
              mul_le_mul_of_nonneg_right htwoa
                (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le)
                  (hpos 0).le) (sq_nonneg _))
            _ = 4 * a * residual 0 * (c (k + 1)) ^ 2 := by ring
        refine ⟨?_, hbnext, hrnext⟩
        unfold p25ScaledResidualRatio
        exact mul_pos hDpos (div_pos (hpos (k + 2)) (hpos (k + 1)))
  have hc_tend : Tendsto c atTop (nhds 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hlim : Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc_tend
      (fun k => (hmain k).1.le) (fun k => (hmain k).2.1)
  change 1 < D ∧
    p25ScaledResidualRatio residual D 0 = 1 / 2 ∧
    (∀ k, 0 < p25ScaledResidualRatio residual D k ∧
      p25ScaledResidualRatio residual D k ≤ c k) ∧
    Tendsto (p25ScaledResidualRatio residual D) atTop (nhds 0)
  refine ⟨hDgt, ?_, ?_, hlim⟩
  · change D * a = 1 / 2
    exact hDa
  · intro k
    exact ⟨(hmain k).1, (hmain k).2.1⟩

end VSCLReuse

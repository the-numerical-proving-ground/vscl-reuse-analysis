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
  let β : ℕ → ℝ := p25ScaledResidualRatio residual D
  let q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (2 ^ k)
  change 1 < D ∧ β 0 = 1 / 2 ∧
    (∀ k, 0 < β k ∧ β k ≤ q k) ∧ Tendsto β atTop (nhds 0)
  have hratio_pos (k : ℕ) : 0 < p25ResidualRatio residual k := by
    exact div_pos (hpos (k + 1)) (hpos k)
  have htwopos : 0 < 2 * p25ResidualRatio residual 0 := by
    exact mul_pos (by norm_num) (hratio_pos 0)
  have hDpos : 0 < D := by
    dsimp [D]
    exact one_div_pos.mpr htwopos
  have hDgt : 1 < D := by
    dsimp [D]
    apply (lt_div_iff₀ htwopos).2
    have hBr : 0 < B * residual 0 := mul_pos hB (hpos 0)
    nlinarith [hsmall]
  have hβzero : β 0 = 1 / 2 := by
    dsimp [β, p25ScaledResidualRatio, D]
    field_simp [ne_of_gt (hratio_pos 0)]
  have hcoef : (2 * p25ResidualRatio residual 0) * D = 1 := by
    have hh : D * p25ResidualRatio residual 0 = 1 / 2 := hβzero
    nlinarith
  have hratio_mul (k : ℕ) :
      p25ResidualRatio residual k * residual k = residual (k + 1) := by
    exact div_mul_cancel₀ _ (ne_of_gt (hpos k))
  have hratio_step (k : ℕ) :
      p25ResidualRatio residual (k + 1) ≤
        (p25ResidualRatio residual k) ^ 2 + B * residual (k + 1) := by
    apply (div_le_iff₀ (hpos (k + 1))).2
    simpa [p25ResidualRatio, Nat.add_assoc] using hstep k
  have hβ_step (k : ℕ) :
      β (k + 1) ≤
        (2 * p25ResidualRatio residual 0) * (β k) ^ 2 +
          B * D * residual (k + 1) := by
    have hh := mul_le_mul_of_nonneg_left (hratio_step k) hDpos.le
    have halg :
        D * (p25ResidualRatio residual k) ^ 2 =
          (2 * p25ResidualRatio residual 0) *
            (D * p25ResidualRatio residual k) ^ 2 := by
      calc
        D * (p25ResidualRatio residual k) ^ 2 =
            ((2 * p25ResidualRatio residual 0) * D) * D *
              (p25ResidualRatio residual k) ^ 2 := by rw [hcoef]; ring
        _ = _ := by ring
    dsimp [β, p25ScaledResidualRatio]
    calc
      D * p25ResidualRatio residual (k + 1) ≤
          D * ((p25ResidualRatio residual k) ^ 2 +
            B * residual (k + 1)) := hh
      _ = _ := by rw [mul_add, halg]; ring
  have hq_pos (k : ℕ) : 0 < q k := by
    dsimp [q]
    positivity
  have hq_step (k : ℕ) : q (k + 1) = (q k) ^ 2 := by
    dsimp [q]
    rw [pow_succ (2 : ℕ) k, pow_mul]
  have hDres_one :
      D * residual 1 = 2 * residual 0 * q 1 := by
    have hh : D * residual 1 = β 0 * residual 0 := by
      dsimp [β, p25ScaledResidualRatio]
      rw [← hratio_mul 0]
      ring
    rw [hh, hβzero]
    norm_num [q]
    ring
  have hpair : ∀ k : ℕ,
      β k ≤ q k ∧ D * residual (k + 1) ≤ 2 * residual 0 * q (k + 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simpa [q] using le_of_eq hβzero
        · simpa using le_of_eq hDres_one
    | succ k ih =>
        rcases ih with ⟨hβk, hrk⟩
        have hβpos : 0 ≤ β k := by
          dsimp [β, p25ScaledResidualRatio]
          exact le_of_lt (mul_pos hDpos (hratio_pos k))
        have hsq : (β k) ^ 2 ≤ (q k) ^ 2 :=
          (sq_le_sq₀ hβpos (hq_pos k).le).2 hβk
        have hterm1 :
            (2 * p25ResidualRatio residual 0) * (β k) ^ 2 ≤
              (2 * p25ResidualRatio residual 0) * q (k + 1) := by
          rw [hq_step]
          exact mul_le_mul_of_nonneg_left hsq htwopos.le
        have hterm2 :
            B * D * residual (k + 1) ≤
              (2 * B * residual 0) * q (k + 1) := by
          have hh := mul_le_mul_of_nonneg_left hrk hB.le
          nlinarith
        have hβnext : β (k + 1) ≤ q (k + 1) := by
          have hc :
              (2 * p25ResidualRatio residual 0 + 2 * B * residual 0) *
                  q (k + 1) ≤ q (k + 1) := by
            have hh := mul_le_mul_of_nonneg_right hsmall (hq_pos (k + 1)).le
            nlinarith
          nlinarith [hβ_step k, hterm1, hterm2]
        constructor
        · exact hβnext
        · have hres_le : residual (k + 1) ≤ D * residual (k + 1) := by
            nlinarith [hDgt, hpos (k + 1)]
          have hres_eq :
              D * residual (k + 2) = β (k + 1) * residual (k + 1) := by
            dsimp [β, p25ScaledResidualRatio]
            convert congrArg (D * ·) (hratio_mul (k + 1)).symm using 1; ring
          calc
            D * residual ((k + 1) + 1) =
                β (k + 1) * residual (k + 1) := by simpa [Nat.add_assoc] using hres_eq
            _ ≤ q (k + 1) * residual (k + 1) :=
              mul_le_mul_of_nonneg_right hβnext (hpos (k + 1)).le
            _ ≤ q (k + 1) * (D * residual (k + 1)) :=
              mul_le_mul_of_nonneg_left hres_le (hq_pos (k + 1)).le
            _ ≤ q (k + 1) * (2 * residual 0 * q (k + 1)) :=
              mul_le_mul_of_nonneg_left hrk (hq_pos (k + 1)).le
            _ = 2 * residual 0 * q ((k + 1) + 1) := by rw [hq_step]; ring
  have hq_tend : Tendsto q atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℕ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).comp h2
  refine ⟨hDgt, hβzero, ?_, ?_⟩
  · intro k
    constructor
    · dsimp [β, p25ScaledResidualRatio]
      exact mul_pos hDpos (hratio_pos k)
    · exact (hpair k).1
  · exact squeeze_zero
      (fun k => le_of_lt (mul_pos hDpos (hratio_pos k)))
      (fun k => (hpair k).1) hq_tend

end VSCLReuse

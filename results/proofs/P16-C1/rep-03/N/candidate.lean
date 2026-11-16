import VSCLReuse.P16.Definitions

namespace VSCLReuse

private noncomputable def p16Energy {k q : ℕ} (X : P16Coupling k q) : ℝ :=
  ∑ i, ∑ j, X i j ^ 2

private lemma p16_energy_nonneg {k q : ℕ} (X : P16Coupling k q) :
    0 ≤ p16Energy X := by
  unfold p16Energy
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

private lemma p16_vecnormsq_nonneg {n : ℕ} (v : P16Vector n) :
    0 ≤ p16VecNormSq v := by
  unfold p16VecNormSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma p16_vecnormsq_smul {n : ℕ} (c : ℝ) (v : P16Vector n) :
    p16VecNormSq (c • v) = c ^ 2 * p16VecNormSq v := by
  simp only [p16VecNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

private lemma p16_matvec_energy_bound {k q : ℕ} (X : P16Coupling k q)
    (v : P16Vector q) :
    p16VecNormSq (p16MatVec X v) ≤ p16Energy X * p16VecNormSq v := by
  unfold p16VecNormSq p16MatVec p16Energy
  calc
    ∑ i, (∑ j, X i j * v j) ^ 2 ≤
        ∑ i, (∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ j, v j ^ 2 := by
      rw [Finset.sum_mul]

private lemma p16_cross_bound {k q : ℕ} (X : P16Coupling k q)
    (c : ℝ) (u : P16Vector k) (v : P16Vector q) :
    2 * c * (∑ i, u i * p16MatVec X v i) ≤
      p16Energy X * p16VecNormSq u + c ^ 2 * p16VecNormSq v := by
  have hcol (j : Fin q) :
      (∑ i, X i j * u i) ^ 2 ≤ (∑ i, X i j ^ 2) * p16VecNormSq u := by
    simpa only [p16VecNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => X i j) u)
  have hcols :
      (∑ j, (∑ i, X i j * u i) ^ 2) ≤
        p16Energy X * p16VecNormSq u := by
    calc
      _ ≤ ∑ j, (∑ i, X i j ^ 2) * p16VecNormSq u := by
        exact Finset.sum_le_sum fun j _ => hcol j
      _ = (∑ j, ∑ i, X i j ^ 2) * p16VecNormSq u := by
        rw [Finset.sum_mul]
      _ = p16Energy X * p16VecNormSq u := by
        rw [Finset.sum_comm]
        rfl
  have hcross :
      (∑ i, u i * p16MatVec X v i) =
        ∑ j, v j * (∑ i, X i j * u i) := by
    unfold p16MatVec
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpoint (j : Fin q) :
      2 * (c * v j) * (∑ i, X i j * u i) ≤
        (c * v j) ^ 2 + (∑ i, X i j * u i) ^ 2 := by
    nlinarith [sq_nonneg (c * v j - ∑ i, X i j * u i)]
  calc
    2 * c * (∑ i, u i * p16MatVec X v i) =
        ∑ j, 2 * (c * v j) * (∑ i, X i j * u i) := by
      rw [hcross]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ j, ((c * v j) ^ 2 + (∑ i, X i j * u i) ^ 2) := by
      exact Finset.sum_le_sum fun j _ => hpoint j
    _ = c ^ 2 * p16VecNormSq v +
          ∑ j, (∑ i, X i j * u i) ^ 2 := by
      simp only [Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum, p16VecNormSq]
    _ ≤ c ^ 2 * p16VecNormSq v +
          p16Energy X * p16VecNormSq u := by
      exact add_le_add_right hcols _
    _ = _ := by ring

private lemma p16_linear_energy_bound {k q : ℕ} (X : P16Coupling k q)
    (c : ℝ) (u : P16Vector k) (v : P16Vector q) :
    p16VecNormSq (fun i => c * u i + p16MatVec X v i) ≤
      (c ^ 2 + p16Energy X) * (p16VecNormSq u + p16VecNormSq v) := by
  have hcross := p16_cross_bound X c u v
  have hmv := p16_matvec_energy_bound X v
  have hident :
      p16VecNormSq (fun i => c * u i + p16MatVec X v i) =
        c ^ 2 * p16VecNormSq u +
          2 * c * (∑ i, u i * p16MatVec X v i) +
          p16VecNormSq (p16MatVec X v) := by
    simp only [p16VecNormSq, add_sq, Finset.sum_add_distrib,
      mul_pow, Finset.mul_sum]
    ring
  rw [hident]
  calc
    _ ≤ c ^ 2 * p16VecNormSq u +
          (p16Energy X * p16VecNormSq u + c ^ 2 * p16VecNormSq v) +
          p16Energy X * p16VecNormSq v := by
      gcongr
    _ = _ := by ring

private lemma p16_w1_energy_bound {k q : ℕ} (X : P16Coupling k q) (α : ℝ) :
    P16SquaredGainBound (p16W1 X α) (1 + p16Energy X + α ^ 2) := by
  intro u v
  change p16VecNormSq (u + p16MatVec X v) + p16VecNormSq (α • v) ≤
    (1 + p16Energy X + α ^ 2) *
      (p16VecNormSq u + p16VecNormSq v)
  have hu : p16VecNormSq (u + p16MatVec X v) =
      p16VecNormSq (fun i => 1 * u i + p16MatVec X v i) := by
    congr 1
    funext i
    simp
  rw [hu, p16_vecnormsq_smul]
  have hlin : p16VecNormSq (fun i => 1 * u i + p16MatVec X v i) ≤
      (1 + p16Energy X) * (p16VecNormSq u + p16VecNormSq v) := by
    simpa using p16_linear_energy_bound X 1 u v
  calc
    _ ≤ (1 + p16Energy X) * (p16VecNormSq u + p16VecNormSq v) +
          α ^ 2 * p16VecNormSq v := add_le_add_left hlin _
    _ ≤ _ := by
      have h := mul_nonneg (sq_nonneg α) (p16_vecnormsq_nonneg u)
      nlinarith

private lemma p16_w2_energy_bound {k q : ℕ} (X : P16Coupling k q) (α : ℝ) :
    P16SquaredGainBound (p16W2 X α) (1 + p16Energy X + α ^ 2) := by
  intro u v
  change p16VecNormSq (α • u - p16MatVec X v) + p16VecNormSq v ≤
    (1 + p16Energy X + α ^ 2) *
      (p16VecNormSq u + p16VecNormSq v)
  have hu : p16VecNormSq (α • u - p16MatVec X v) =
      p16VecNormSq (fun i => (-α) * u i + p16MatVec X v i) := by
    unfold p16VecNormSq
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hu]
  have hlin : p16VecNormSq (fun i => (-α) * u i + p16MatVec X v i) ≤
      (α ^ 2 + p16Energy X) * (p16VecNormSq u + p16VecNormSq v) := by
    simpa only [neg_sq] using p16_linear_energy_bound X (-α) u v
  calc
    _ ≤ (α ^ 2 + p16Energy X) * (p16VecNormSq u + p16VecNormSq v) +
          p16VecNormSq v := add_le_add_left hlin _
    _ ≤ _ := by
      have h := p16_vecnormsq_nonneg u
      nlinarith

private lemma p16_energy_budget {k q : ℕ} (data : P16Theorem32Data k q) :
    p16Energy data.X + data.alpha ^ 2 ≤
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
  calc
    p16Energy data.X + data.alpha ^ 2 ≤
        p16Energy data.X + ∑ i, ∑ j, data.ratio i j ^ 2 := by
      exact add_le_add_right data.alpha_sq_le _
    _ = ∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2) := by
      simp only [p16Energy, Finset.sum_add_distrib]
    _ ≤ ∑ i : Fin k, ∑ j : Fin q, data.f ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => (data.p_lt_f i j).le
    _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
      simp
      ring

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hgSq_pos : 0 < gSq := by
    dsimp [gSq]
    positivity
  have hbase : 1 + p16Energy data.X + data.alpha ^ 2 ≤ gSq := by
    dsimp [gSq]
    have h := p16_energy_budget data
    linarith
  have hW1 : P16SquaredGainBound (p16W1 data.X data.alpha) gSq := by
    intro u v
    have hpair : 0 ≤ p16PairNormSq u v :=
      add_nonneg (p16_vecnormsq_nonneg u) (p16_vecnormsq_nonneg v)
    exact (p16_w1_energy_bound data.X data.alpha u v).trans
      (mul_le_mul_of_nonneg_right hbase hpair)
  have hW2 : P16SquaredGainBound (p16W2 data.X data.alpha) gSq := by
    intro u v
    have hpair : 0 ≤ p16PairNormSq u v :=
      add_nonneg (p16_vecnormsq_nonneg u) (p16_vecnormsq_nonneg v)
    exact (p16_w2_energy_bound data.X data.alpha u v).trans
      (mul_le_mul_of_nonneg_right hbase hpair)
  have htop := data.hornJohnson_top gSq hgSq_pos.le hW1
  have htail := data.hornJohnson_tail gSq hgSq_pos.le hW2
  have hfactor : 0 < p16StrongFactor k q data.f := by
    exact Real.sqrt_pos.2 hgSq_pos
  constructor
  · intro i
    apply (div_le_iff₀ hfactor).2
    simpa only [p16StrongFactor] using htop i
  · intro j
    simpa only [p16StrongFactor] using htail j

end VSCLReuse

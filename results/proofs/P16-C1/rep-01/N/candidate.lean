import VSCLReuse.P16.Definitions

namespace VSCLReuse

private theorem p16_matVec_sq_le {k q : ℕ}
    (X : P16Coupling k q) (v : P16Vector q) :
    p16VecNormSq (p16MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq v := by
  simp only [p16VecNormSq, p16MatVec]
  calc
    (∑ i, (∑ j, X i j * v j) ^ 2) ≤
        ∑ i, (∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          simpa using
            (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
              (fun j ↦ X i j) v)
    _ = (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      rw [Finset.sum_mul]

private theorem p16_dot_swap {k q : ℕ}
    (X : P16Coupling k q) (u : P16Vector k) (v : P16Vector q) :
    (∑ i, u i * p16MatVec X v i) =
      ∑ j, v j * p16MatVec X.transpose u j := by
  simp only [p16MatVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem p16_cross_le {k q : ℕ}
    (X : P16Coupling k q) (u : P16Vector k) (v : P16Vector q) (a : ℝ) :
    2 * a * (∑ i, u i * p16MatVec X v i) ≤
      (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq u + a ^ 2 * p16VecNormSq v := by
  have htranspose := p16_matVec_sq_le X.transpose u
  have hsum : (∑ j, ∑ i, X.transpose j i ^ 2) =
      ∑ i, ∑ j, X i j ^ 2 := by
    simp only [Matrix.transpose_apply]
    rw [Finset.sum_comm]
  rw [hsum] at htranspose
  calc
    2 * a * (∑ i, u i * p16MatVec X v i) =
        ∑ j, 2 * a * v j * p16MatVec X.transpose u j := by
          rw [p16_dot_swap, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ ≤ ∑ j, ((p16MatVec X.transpose u j) ^ 2 + a ^ 2 * v j ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (p16MatVec X.transpose u j - a * v j)]
    _ = p16VecNormSq (p16MatVec X.transpose u) + a ^ 2 * p16VecNormSq v := by
      simp only [p16VecNormSq, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq u + a ^ 2 * p16VecNormSq v := by
      gcongr

private theorem p16_vec_add_sq {n : ℕ} (u w : P16Vector n) :
    p16VecNormSq (u + w) =
      p16VecNormSq u + 2 * (∑ i, u i * w i) + p16VecNormSq w := by
  simp only [p16VecNormSq, Pi.add_apply]
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

private theorem p16_vec_sub_sq {n : ℕ} (u w : P16Vector n) :
    p16VecNormSq (u - w) =
      p16VecNormSq u - 2 * (∑ i, u i * w i) + p16VecNormSq w := by
  simp only [p16VecNormSq, Pi.sub_apply]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

private theorem p16_vec_smul_sq {n : ℕ} (a : ℝ) (u : P16Vector n) :
    p16VecNormSq (a • u) = a ^ 2 * p16VecNormSq u := by
  simp only [p16VecNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

private theorem p16_vec_sq_nonneg {n : ℕ} (u : P16Vector n) :
    0 ≤ p16VecNormSq u := by
  exact Finset.sum_nonneg (fun i hi ↦ sq_nonneg (u i))

private theorem p16_w1_gain {k q : ℕ} (X : P16Coupling k q) (α : ℝ) :
    P16SquaredGainBound (p16W1 X α)
      (1 + (∑ i, ∑ j, X i j ^ 2) + α ^ 2) := by
  intro u v
  change p16VecNormSq (u + p16MatVec X v) + p16VecNormSq (α • v) ≤
    (1 + (∑ i, ∑ j, X i j ^ 2) + α ^ 2) *
      (p16VecNormSq u + p16VecNormSq v)
  rw [p16_vec_add_sq, p16_vec_smul_sq]
  have hcross := p16_cross_le X u v 1
  have hx := p16_matVec_sq_le X v
  have hu := p16_vec_sq_nonneg u
  nlinarith [mul_nonneg (sq_nonneg α) hu]

private theorem p16_w2_gain {k q : ℕ} (X : P16Coupling k q) (α : ℝ) :
    P16SquaredGainBound (p16W2 X α)
      (1 + (∑ i, ∑ j, X i j ^ 2) + α ^ 2) := by
  intro u v
  change p16VecNormSq (α • u - p16MatVec X v) + p16VecNormSq v ≤
    (1 + (∑ i, ∑ j, X i j ^ 2) + α ^ 2) *
      (p16VecNormSq u + p16VecNormSq v)
  rw [p16_vec_sub_sq, p16_vec_smul_sq]
  have hdot :
      (∑ i, (α • u) i * p16MatVec X v i) =
        α * (∑ i, u i * p16MatVec X v i) := by
    calc
      _ = ∑ i, α * (u i * p16MatVec X v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hdot]
  have hcross := p16_cross_le X u v (-α)
  have hx := p16_matVec_sq_le X v
  have hu := p16_vec_sq_nonneg u
  nlinarith

private theorem p16_gain_mono {k q : ℕ}
    {W : P16Vector k → P16Vector q → P16Vector k × P16Vector q}
    {gSq hSq : ℝ} (hg : P16SquaredGainBound W gSq) (hgh : gSq ≤ hSq) :
    P16SquaredGainBound W hSq := by
  intro u v
  exact (hg u v).trans
    (mul_le_mul_of_nonneg_right hgh
      (add_nonneg (p16_vec_sq_nonneg u) (p16_vec_sq_nonneg v)))

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hgSq : 0 ≤ gSq := by
    dsimp [gSq]
    positivity
  have hsum_add :
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) =
        (∑ i, ∑ j, data.X i j ^ 2) +
          (∑ i, ∑ j, data.ratio i j ^ 2) := by
    simp only [Finset.sum_add_distrib]
  have hsum_bound :
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
        data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    calc
      _ ≤ ∑ (_i : Fin k), ∑ (_j : Fin q), data.f ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact le_of_lt (data.p_lt_f i j)
      _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        ring
  rw [hsum_add] at hsum_bound
  have hgain_sq :
      1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤ gSq := by
    dsimp [gSq]
    linarith [data.alpha_sq_le]
  have hw1 : P16SquaredGainBound (p16W1 data.X data.alpha) gSq :=
    p16_gain_mono (p16_w1_gain data.X data.alpha) hgain_sq
  have hw2 : P16SquaredGainBound (p16W2 data.X data.alpha) gSq :=
    p16_gain_mono (p16_w2_gain data.X data.alpha) hgain_sq
  have hfactor_pos : 0 < p16StrongFactor k q data.f := by
    unfold p16StrongFactor
    exact Real.sqrt_pos.2 (by dsimp [gSq] at hgSq ⊢; positivity)
  constructor
  · intro i
    apply (div_le_iff₀ hfactor_pos).2
    simpa [p16StrongFactor, gSq] using data.hornJohnson_top gSq hgSq hw1 i
  · intro j
    simpa [p16StrongFactor, gSq] using data.hornJohnson_tail gSq hgSq hw2 j

end VSCLReuse

import VSCLReuse.P16.Definitions

namespace VSCLReuse

private lemma p16_vecNormSq_nonneg {n : ℕ} (u : P16Vector n) :
    0 ≤ p16VecNormSq u := by
  unfold p16VecNormSq
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (u i))

private lemma p16_matVec_energy {k q : ℕ} (X : P16Coupling k q)
    (v : P16Vector q) :
    p16VecNormSq (p16MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq v := by
  unfold p16VecNormSq p16MatVec
  calc
    (∑ i, (∑ j, X i j * v j) ^ 2) ≤
        ∑ i, (∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa using (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
        (X i) v)
    _ = (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      rw [Finset.sum_mul]

private lemma p16_vec_add_energy {k q : ℕ}
    (u z : P16Vector k) (v : P16Vector q) (S : ℝ)
    (hS : 0 ≤ S) (hz : p16VecNormSq z ≤ S * p16VecNormSq v) :
    p16VecNormSq (u + z) ≤
      (1 + S) * (p16VecNormSq u + p16VecNormSq v) := by
  let U := p16VecNormSq u
  let V := p16VecNormSq v
  let B := p16VecNormSq z
  let c : ℝ := ∑ i, u i * z i
  have hU : 0 ≤ U := p16_vecNormSq_nonneg u
  have hV : 0 ≤ V := p16_vecNormSq_nonneg v
  have hB : 0 ≤ B := p16_vecNormSq_nonneg z
  have hCS : c ^ 2 ≤ U * B := by
    simpa [c, U, B, p16VecNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) u z)
  have hc : c ^ 2 ≤ (S * U) * V := by
    have hm := mul_le_mul_of_nonneg_left hz hU
    nlinarith [hCS]
  have hSU : 0 ≤ S * U := mul_nonneg hS hU
  have hcross : 2 * c ≤ S * U + V := by
    nlinarith [sq_nonneg (S * U - V)]
  have hadd : p16VecNormSq (u + z) = U + 2 * c + B := by
    simp only [p16VecNormSq, Pi.add_apply, add_sq, Finset.sum_add_distrib]
    dsimp [U, B, c]
    simp only [p16VecNormSq]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  rw [hadd]
  dsimp [U, V, B] at *
  nlinarith [hz]

private lemma p16_vec_neg_energy {n : ℕ} (u : P16Vector n) :
    p16VecNormSq (-u) = p16VecNormSq u := by
  simp [p16VecNormSq]

private lemma p16_gain_bound {k q : ℕ} (X : P16Coupling k q) (alpha : ℝ)
    : P16SquaredGainBound (p16W1 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg (fun j hj => sq_nonneg (X i j))
  have hvec := p16_vec_add_energy u (p16MatVec X v) v S hS
    (p16_matVec_energy X v)
  dsimp [p16W1, p16PairNormSq]
  have hscale : p16VecNormSq (alpha • v) = alpha ^ 2 * p16VecNormSq v := by
    simp [p16VecNormSq, Finset.mul_sum, mul_pow]
  rw [hscale]
  have hv : 0 ≤ p16VecNormSq v := p16_vecNormSq_nonneg v
  have hu : 0 ≤ p16VecNormSq u := p16_vecNormSq_nonneg u
  dsimp [S] at hvec
  nlinarith [sq_nonneg alpha]

private lemma p16_gain_bound_two {k q : ℕ} (X : P16Coupling k q) (alpha : ℝ) :
    P16SquaredGainBound (p16W2 X alpha)
      (1 + (∑ i, ∑ j, X i j ^ 2) + alpha ^ 2) := by
  intro u v
  let S : ℝ := ∑ i, ∑ j, X i j ^ 2
  let U := p16VecNormSq u
  let V := p16VecNormSq v
  let z := -(p16MatVec X v)
  let a := alpha • u
  let B := p16VecNormSq z
  let c : ℝ := ∑ i, a i * z i
  have hS : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro i hi
    exact Finset.sum_nonneg (fun j hj => sq_nonneg (X i j))
  have hU : 0 ≤ U := p16_vecNormSq_nonneg u
  have hV : 0 ≤ V := p16_vecNormSq_nonneg v
  have hB : 0 ≤ B := p16_vecNormSq_nonneg z
  have hBe : B ≤ S * V := by
    simpa only [B, z, p16_vec_neg_energy, S, V] using
      (p16_matVec_energy X v)
  have hAe : p16VecNormSq a = alpha ^ 2 * U := by
    simp [a, U, p16VecNormSq, Finset.mul_sum, mul_pow]
  have hCS : c ^ 2 ≤ p16VecNormSq a * B := by
    simpa [c, B, p16VecNormSq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k)) a z)
  have hc : c ^ 2 ≤ (S * U) * (alpha ^ 2 * V) := by
    have hm := mul_le_mul_of_nonneg_left hBe (mul_nonneg (sq_nonneg alpha) hU)
    rw [hAe] at hCS
    nlinarith [hCS]
  have hcross : 2 * c ≤ S * U + alpha ^ 2 * V := by
    nlinarith [sq_nonneg (S * U - alpha ^ 2 * V), mul_nonneg hS hU,
      mul_nonneg (sq_nonneg alpha) hV]
  have hadd : p16VecNormSq (a + z) =
      p16VecNormSq a + 2 * c + B := by
    simp only [p16VecNormSq, Pi.add_apply, add_sq, Finset.sum_add_distrib]
    dsimp [c, B]
    simp only [p16VecNormSq]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  change p16VecNormSq (a + z) + V ≤ (1 + S + alpha ^ 2) * (U + V)
  rw [hadd, hAe]
  nlinarith [hBe, hcross, mul_nonneg hS hU]

private lemma p16_gain_mono {k q : ℕ}
    (W : P16Vector k → P16Vector q → P16Vector k × P16Vector q)
    {a b : ℝ} (hab : a ≤ b) (ha : P16SquaredGainBound W a) :
    P16SquaredGainBound W b := by
  intro u v
  exact (ha u v).trans (mul_le_mul_of_nonneg_right hab
    (add_nonneg (p16_vecNormSq_nonneg u) (p16_vecNormSq_nonneg v)))

private lemma p16_strength_bound {k q : ℕ} (data : P16Theorem32Data k q) :
    (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤
      data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
  calc
    (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤
        (∑ i, ∑ j, data.X i j ^ 2) +
          (∑ i, ∑ j, data.ratio i j ^ 2) :=
      by nlinarith [data.alpha_sq_le]
    _ = ∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ ∑ i, ∑ j, data.f ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_lt (data.p_lt_f i j)
    _ = data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
      simp [mul_comm, mul_left_comm]

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let g : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hg : 0 ≤ g := by
    dsimp [g]
    positivity
  have hstrength := p16_strength_bound data
  have hcompare :
      1 + (∑ i, ∑ j, data.X i j ^ 2) + data.alpha ^ 2 ≤ g := by
    dsimp [g]
    nlinarith [hstrength]
  have hgain1 : P16SquaredGainBound (p16W1 data.X data.alpha) g :=
    p16_gain_mono (p16W1 data.X data.alpha) hcompare
      (p16_gain_bound data.X data.alpha)
  have hgain2 : P16SquaredGainBound (p16W2 data.X data.alpha) g :=
    p16_gain_mono (p16W2 data.X data.alpha) hcompare
      (p16_gain_bound_two data.X data.alpha)
  have hroot : 0 < Real.sqrt g := Real.sqrt_pos.2 (by
    dsimp [g]
    positivity)
  have hfactor : p16StrongFactor k q data.f = Real.sqrt g := rfl
  constructor
  · intro i
    rw [hfactor]
    exact (div_le_iff₀ hroot).2 (data.hornJohnson_top g hg hgain1 i)
  · intro j
    rw [hfactor]
    exact data.hornJohnson_tail g hg hgain2 j

end VSCLReuse

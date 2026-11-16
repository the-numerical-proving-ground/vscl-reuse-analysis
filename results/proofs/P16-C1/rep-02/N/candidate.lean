import VSCLReuse.P16.Definitions

namespace VSCLReuse

private theorem p16_matvec_sq_le {k q : ℕ} (X : P16Coupling k q)
    (v : P16Vector q) :
    (∑ i, p16MatVec X v i ^ 2) ≤
      (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
  calc
    (∑ i, p16MatVec X v i ^ 2) ≤
        ∑ i, (∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [p16MatVec] using
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v)
    _ = (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
      rw [Finset.sum_mul]

private theorem p16_gain_core {k q : ℕ}
    (u : P16Vector k) (v : P16Vector q) (t : P16Vector k)
    (a b S : ℝ) (hS : 0 ≤ S)
    (ht : (∑ i, t i ^ 2) ≤ S * (∑ j, v j ^ 2)) :
    (∑ i, (a * u i + t i) ^ 2) + (∑ j, (b * v j) ^ 2) ≤
      (a ^ 2 + b ^ 2 + S) * ((∑ i, u i ^ 2) + (∑ j, v j ^ 2)) := by
  let U : ℝ := ∑ i, u i ^ 2
  let V : ℝ := ∑ j, v j ^ 2
  let T : ℝ := ∑ i, t i ^ 2
  let D : ℝ := ∑ i, u i * t i
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i hi => sq_nonneg (u i))
  have hV : 0 ≤ V := Finset.sum_nonneg (fun j hj => sq_nonneg (v j))
  have hD : D ^ 2 ≤ U * T :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u t
  have hT : T ≤ S * V := ht
  have hDS : D ^ 2 ≤ U * (S * V) :=
    hD.trans (mul_le_mul_of_nonneg_left hT hU)
  have hYoung : 2 * (a * D) ≤ S * U + a ^ 2 * V := by
    have hsq : (a * D) ^ 2 ≤ (S * U) * (a ^ 2 * V) := by
      calc
        (a * D) ^ 2 = a ^ 2 * D ^ 2 := by ring
        _ ≤ a ^ 2 * (U * (S * V)) :=
          mul_le_mul_of_nonneg_left hDS (sq_nonneg a)
        _ = (S * U) * (a ^ 2 * V) := by ring
    have hx : 0 ≤ S * U := mul_nonneg hS hU
    have hy : 0 ≤ a ^ 2 * V := mul_nonneg (sq_nonneg a) hV
    nlinarith [sq_nonneg (S * U - a ^ 2 * V)]
  have hfirst : (∑ i, (a * u i + t i) ^ 2) = a ^ 2 * U + 2 * a * D + T := by
    calc
      _ = ∑ i, (a ^ 2 * u i ^ 2 + 2 * a * (u i * t i) + t i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = a ^ 2 * U + 2 * a * D + T := by
        simp only [U, D, T, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsecond : (∑ j, (b * v j) ^ 2) = b ^ 2 * V := by
    simp only [mul_pow, ← Finset.mul_sum, V]
  rw [hfirst, hsecond]
  nlinarith [mul_nonneg (sq_nonneg b) hU]

private theorem p16_entry_sum_le {k q : ℕ}
    (X ratio : P16Coupling k q) (f : ℝ)
    (h : ∀ i j, X i j ^ 2 + ratio i j ^ 2 < f ^ 2) :
    (∑ i, ∑ j, X i j ^ 2) + (∑ i, ∑ j, ratio i j ^ 2) ≤
      f ^ 2 * (k : ℝ) * (q : ℝ) := by
  calc
    (∑ i, ∑ j, X i j ^ 2) + (∑ i, ∑ j, ratio i j ^ 2) =
        ∑ i, ∑ j, (X i j ^ 2 + ratio i j ^ 2) := by
      simp [Finset.sum_add_distrib]
    _ ≤ ∑ (_i : Fin k), ∑ (_j : Fin q), f ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_lt (h i j)
    _ = f ^ 2 * (k : ℝ) * (q : ℝ) := by
      simp [mul_comm, mul_left_comm]

private theorem p16_w1_gain {k q : ℕ} (X : P16Coupling k q) (alpha : ℝ) :
    P16SquaredGainBound (p16W1 X alpha)
      (1 + alpha ^ 2 + (∑ i, ∑ j, X i j ^ 2)) := by
  intro u v
  have hS : 0 ≤ (∑ i, ∑ j, X i j ^ 2) :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg (X i j)))
  have h := p16_gain_core u v (p16MatVec X v) 1 alpha
    (∑ i, ∑ j, X i j ^ 2) hS (p16_matvec_sq_le X v)
  simpa [p16PairNormSq, p16VecNormSq, p16W1, Pi.add_apply, smul_eq_mul,
    mul_comm, mul_left_comm] using h

private theorem p16_w2_gain {k q : ℕ} (X : P16Coupling k q) (alpha : ℝ) :
    P16SquaredGainBound (p16W2 X alpha)
      (alpha ^ 2 + 1 + (∑ i, ∑ j, X i j ^ 2)) := by
  intro u v
  have hS : 0 ≤ (∑ i, ∑ j, X i j ^ 2) :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg (X i j)))
  have ht : (∑ i, (-p16MatVec X v i) ^ 2) ≤
      (∑ i, ∑ j, X i j ^ 2) * (∑ j, v j ^ 2) := by
    simpa only [Even.neg_pow, even_two] using p16_matvec_sq_le X v
  have h := p16_gain_core u v (fun i => -p16MatVec X v i) alpha 1
    (∑ i, ∑ j, X i j ^ 2) hS ht
  simpa [p16PairNormSq, p16VecNormSq, p16W2, Pi.sub_apply, sub_eq_add_neg,
    smul_eq_mul, mul_comm, mul_left_comm] using h

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let gSq : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hg : 0 ≤ gSq := by
    dsimp [gSq]
    positivity
  have hgpos : 0 < gSq := by
    dsimp [gSq]
    positivity
  have hentries := p16_entry_sum_le data.X data.ratio data.f data.p_lt_f
  have hsmall1 :
      1 + data.alpha ^ 2 + (∑ i, ∑ j, data.X i j ^ 2) ≤ gSq := by
    dsimp [gSq]
    linarith [data.alpha_sq_le]
  have hsmall2 :
      data.alpha ^ 2 + 1 + (∑ i, ∑ j, data.X i j ^ 2) ≤ gSq := by
    linarith [hsmall1]
  have hpair (u : P16Vector k) (v : P16Vector q) :
      0 ≤ p16PairNormSq u v := by
    simp only [p16PairNormSq, p16VecNormSq]
    positivity
  have hgain1 : P16SquaredGainBound (p16W1 data.X data.alpha) gSq := by
    intro u v
    exact (p16_w1_gain data.X data.alpha u v).trans
      (mul_le_mul_of_nonneg_right hsmall1 (hpair u v))
  have hgain2 : P16SquaredGainBound (p16W2 data.X data.alpha) gSq := by
    intro u v
    exact (p16_w2_gain data.X data.alpha u v).trans
      (mul_le_mul_of_nonneg_right hsmall2 (hpair u v))
  have hfactor : 0 < p16StrongFactor k q data.f := by
    exact Real.sqrt_pos.2 hgpos
  constructor
  · intro i
    apply (div_le_iff₀ hfactor).2
    simpa [p16StrongFactor, gSq] using
      (data.hornJohnson_top gSq hg hgain1 i)
  · intro j
    simpa [p16StrongFactor, gSq] using
      (data.hornJohnson_tail gSq hg hgain2 j)

end VSCLReuse

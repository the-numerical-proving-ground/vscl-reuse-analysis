import VSCLReuse.P16.Definitions

namespace VSCLReuse

private theorem p16_normSq_nonneg {n : ℕ} (u : P16Vector n) :
    0 ≤ p16VecNormSq u := by
  unfold p16VecNormSq
  positivity

private theorem p16_normSq_add {n : ℕ} (u w : P16Vector n) :
    p16VecNormSq (u + w) =
      p16VecNormSq u + 2 * (∑ i, u i * w i) + p16VecNormSq w := by
  simp only [p16VecNormSq, Pi.add_apply]
  simp_rw [add_sq]
  simp only [Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  ring_nf

private theorem p16_normSq_sub {n : ℕ} (u w : P16Vector n) :
    p16VecNormSq (u - w) =
      p16VecNormSq u - 2 * (∑ i, u i * w i) + p16VecNormSq w := by
  simp only [p16VecNormSq, Pi.sub_apply]
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  ring_nf

private theorem p16_normSq_smul {n : ℕ} (a : ℝ) (u : P16Vector n) :
    p16VecNormSq (a • u) = a ^ 2 * p16VecNormSq u := by
  simp only [p16VecNormSq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

private theorem p16_matvec_normSq_le {k q : ℕ}
    (X : P16Coupling k q) (v : P16Vector q) :
    p16VecNormSq (p16MatVec X v) ≤
      (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq v := by
  calc
    p16VecNormSq (p16MatVec X v) =
        ∑ i, (∑ j, X i j * v j) ^ 2 := rfl
    _ ≤ ∑ i, (∑ j, X i j ^ 2) * p16VecNormSq v := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i, ∑ j, X i j ^ 2) * p16VecNormSq v := by
      rw [Finset.sum_mul]

private theorem p16_young_of_sq {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) :
    2 * c ≤ a + b := by
  nlinarith [sq_nonneg (a - b)]

private theorem p16_gain_bound {k q : ℕ}
    (X : P16Coupling k q) (a g : ℝ)
    (ha : a ^ 2 ≤ g) :
    P16SquaredGainBound (p16W1 X a)
      (1 + (∑ i, ∑ j, X i j ^ 2) + g) ∧
    P16SquaredGainBound (p16W2 X a)
      (1 + (∑ i, ∑ j, X i j ^ 2) + g) := by
  constructor <;> intro u v
  · let U := p16VecNormSq u
    let V := p16VecNormSq v
    let T := p16VecNormSq (p16MatVec X v)
    let S := ∑ i, ∑ j, X i j ^ 2
    let C := ∑ i, u i * p16MatVec X v i
    have hU : 0 ≤ U := p16_normSq_nonneg u
    have hV : 0 ≤ V := p16_normSq_nonneg v
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hT : T ≤ S * V := p16_matvec_normSq_le X v
    have hC : C ^ 2 ≤ U * T :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (p16MatVec X v)
    have hCT : C ^ 2 ≤ (S * U) * V := by
      have h := mul_le_mul_of_nonneg_left hT hU
      nlinarith only [hC, h]
    have hY : 2 * C ≤ S * U + V :=
      p16_young_of_sq (mul_nonneg hS hU) hV hCT
    have hExp : p16PairNormSq (p16W1 X a u v).1 (p16W1 X a u v).2 =
        U + 2 * C + T + a ^ 2 * V := by
      change p16VecNormSq (u + p16MatVec X v) +
        p16VecNormSq (a • v) = _
      rw [p16_normSq_add, p16_normSq_smul]
    rw [hExp]
    change U + 2 * C + T + a ^ 2 * V ≤
      (1 + S + g) * (U + V)
    have hag : 0 ≤ g - a ^ 2 := sub_nonneg.mpr ha
    have hgU : 0 ≤ g * U := mul_nonneg (le_trans (sq_nonneg a) ha) hU
    have hgaV : 0 ≤ (g - a ^ 2) * V := mul_nonneg hag hV
    nlinarith only [hT, hY, hgU, hgaV]
  · let U := p16VecNormSq u
    let V := p16VecNormSq v
    let T := p16VecNormSq (p16MatVec X v)
    let S := ∑ i, ∑ j, X i j ^ 2
    let C := ∑ i, u i * p16MatVec X v i
    have hU : 0 ≤ U := p16_normSq_nonneg u
    have hV : 0 ≤ V := p16_normSq_nonneg v
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hT : T ≤ S * V := p16_matvec_normSq_le X v
    have hC : C ^ 2 ≤ U * T :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u (p16MatVec X v)
    have hCT : C ^ 2 ≤ (S * U) * V := by
      have h := mul_le_mul_of_nonneg_left hT hU
      nlinarith only [hC, h]
    have hScale : (-a * C) ^ 2 ≤ (S * U) * (a ^ 2 * V) := by
      have h := mul_le_mul_of_nonneg_left hCT (sq_nonneg a)
      nlinarith only [h]
    have hY : 2 * (-a * C) ≤ S * U + a ^ 2 * V :=
      p16_young_of_sq (mul_nonneg hS hU)
        (mul_nonneg (sq_nonneg a) hV) hScale
    have hExp : p16PairNormSq (p16W2 X a u v).1 (p16W2 X a u v).2 =
        a ^ 2 * U - 2 * a * C + T + V := by
      change p16VecNormSq (a • u - p16MatVec X v) +
        p16VecNormSq v = _
      rw [p16_normSq_sub, p16_normSq_smul]
      have hcross : (∑ i, (a • u) i * p16MatVec X v i) = a * C := by
        dsimp [C]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcross]
      ring
    rw [hExp]
    change a ^ 2 * U - 2 * a * C + T + V ≤
      (1 + S + g) * (U + V)
    have hag : 0 ≤ g - a ^ 2 := sub_nonneg.mpr ha
    have hgaU : 0 ≤ (g - a ^ 2) * U := mul_nonneg hag hU
    have hgaV : 0 ≤ (g - a ^ 2) * V := mul_nonneg hag hV
    nlinarith only [hT, hY, hgaU, hgaV, hU]

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let S : ℝ := ∑ i, ∑ j, data.X i j ^ 2
  let G : ℝ := ∑ i, ∑ j, data.ratio i j ^ 2
  let H : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hrow (i : Fin k) :
      (∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
        (q : ℝ) * data.f ^ 2 := by
    calc
      (∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
          ∑ _j : Fin q, data.f ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact le_of_lt (data.p_lt_f i j)
      _ = (q : ℝ) * data.f ^ 2 := by simp
  have htotal :
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
        (k : ℝ) * ((q : ℝ) * data.f ^ 2) := by
    calc
      (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) ≤
          ∑ _i : Fin k, (q : ℝ) * data.f ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact hrow i
      _ = (k : ℝ) * ((q : ℝ) * data.f ^ 2) := by simp
  have hsum : S + G ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) := by
    have hsplit :
        (∑ i, ∑ j, (data.X i j ^ 2 + data.ratio i j ^ 2)) = S + G := by
      dsimp [S, G]
      simp only [Finset.sum_add_distrib]
    rw [hsplit] at htotal
    nlinarith only [htotal]
  have hGH : 1 + S + G ≤ H := by
    dsimp [H]
    linarith only [hsum]
  have hG : data.alpha ^ 2 ≤ G := data.alpha_sq_le
  have hGain := p16_gain_bound data.X data.alpha G hG
  have hInput (u : P16Vector k) (v : P16Vector q) :
      0 ≤ p16PairNormSq u v :=
    add_nonneg (p16_normSq_nonneg u) (p16_normSq_nonneg v)
  have hGainTop : P16SquaredGainBound (p16W1 data.X data.alpha) H := by
    intro u v
    exact (hGain.1 u v).trans (mul_le_mul_of_nonneg_right hGH (hInput u v))
  have hGainTail : P16SquaredGainBound (p16W2 data.X data.alpha) H := by
    intro u v
    exact (hGain.2 u v).trans (mul_le_mul_of_nonneg_right hGH (hInput u v))
  have hHpos : 0 < H := by
    dsimp [H]
    positivity
  have hHnonneg : 0 ≤ H := le_of_lt hHpos
  constructor
  · intro i
    change data.sigmaMTop i / Real.sqrt H ≤ data.sigmaA i
    exact (div_le_iff₀ (Real.sqrt_pos.2 hHpos)).2
      (data.hornJohnson_top H hHnonneg hGainTop i)
  · intro j
    change data.sigmaC j ≤ data.sigmaMTail j * Real.sqrt H
    exact data.hornJohnson_tail H hHnonneg hGainTail j

end VSCLReuse

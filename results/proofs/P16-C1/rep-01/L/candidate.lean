import VSCLReuse.P16.Definitions

namespace VSCLReuse

private lemma p16_matvec_sq_le {k q : ℕ} (X : P16Coupling k q)
    (v : P16Vector q) :
    p16VecNormSq (p16MatVec X v) ≤
      (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) * p16VecNormSq v := by
  unfold p16VecNormSq p16MatVec
  calc
    (∑ i : Fin k, (∑ j : Fin q, X i j * v j) ^ 2)
        ≤ ∑ i : Fin k, (∑ j : Fin q, X i j ^ 2) *
            (∑ j : Fin q, v j ^ 2) := by
              apply Finset.sum_le_sum
              intro i hi
              exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (X i) v
    _ = (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) *
          (∑ j : Fin q, v j ^ 2) := by rw [Finset.sum_mul]

private lemma p16_dot_sq_le {k : ℕ} (u z : P16Vector k) :
    (∑ i : Fin k, u i * z i) ^ 2 ≤ p16VecNormSq u * p16VecNormSq z := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u z

private lemma p16_two_mul_le_add {a b x : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : x ^ 2 ≤ a * b) :
    2 * x ≤ a + b := by
  have hs : x ≤ Real.sqrt (a * b) := Real.le_sqrt_of_sq_le hx
  have ham := two_mul_le_add_of_sq_eq_mul ha hb
    (Real.sq_sqrt (mul_nonneg ha hb))
  linarith

private lemma p16_block_arith {U V S Z D α T : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hS : 0 ≤ S)
    (hZ : Z ≤ S * V) (hD : D ^ 2 ≤ U * Z)
    (hα : α ^ 2 ≤ T) :
    U + 2 * D + Z + α ^ 2 * V ≤ (1 + S + T) * (U + V) ∧
    α ^ 2 * U - 2 * α * D + Z + V ≤ (1 + S + T) * (U + V) := by
  have hDS : D ^ 2 ≤ (S * U) * V := by
    calc
      D ^ 2 ≤ U * Z := hD
      _ ≤ U * (S * V) := mul_le_mul_of_nonneg_left hZ hU
      _ = (S * U) * V := by ring
  have hcross1 : 2 * D ≤ S * U + V :=
    p16_two_mul_le_add (mul_nonneg hS hU) hV hDS
  have hcross2 : -(2 * α * D) ≤ S * U + α ^ 2 * V := by
    have hsq : (-α * D) ^ 2 ≤ (S * U) * (α ^ 2 * V) := by
      calc
        (-α * D) ^ 2 = α ^ 2 * D ^ 2 := by ring
        _ ≤ α ^ 2 * ((S * U) * V) :=
          mul_le_mul_of_nonneg_left hDS (sq_nonneg α)
        _ = (S * U) * (α ^ 2 * V) := by ring
    have h := p16_two_mul_le_add (mul_nonneg hS hU)
      (mul_nonneg (sq_nonneg α) hV) hsq
    nlinarith
  have hSV : 0 ≤ S * V - Z := sub_nonneg.mpr hZ
  have hTV : 0 ≤ (T - α ^ 2) * (U + V) :=
    mul_nonneg (sub_nonneg.mpr hα) (add_nonneg hU hV)
  have hαU : 0 ≤ α ^ 2 * U := mul_nonneg (sq_nonneg α) hU
  constructor <;> nlinarith

private lemma p16_vec_add_sq {k : ℕ} (u z : P16Vector k) :
    p16VecNormSq (u + z) =
      p16VecNormSq u + 2 * (∑ i : Fin k, u i * z i) + p16VecNormSq z := by
  simp only [p16VecNormSq, Pi.add_apply]
  simp_rw [show ∀ i : Fin k,
    (u i + z i) ^ 2 = u i ^ 2 + 2 * (u i * z i) + z i ^ 2 from
      fun i => by ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma p16_vec_smul_sq {k : ℕ} (α : ℝ) (u : P16Vector k) :
    p16VecNormSq (α • u) = α ^ 2 * p16VecNormSq u := by
  simp only [p16VecNormSq, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_pow]
  rw [Finset.mul_sum]

private lemma p16_vec_smul_sub_sq {k : ℕ} (α : ℝ)
    (u z : P16Vector k) :
    p16VecNormSq (α • u - z) =
      α ^ 2 * p16VecNormSq u -
        2 * α * (∑ i : Fin k, u i * z i) + p16VecNormSq z := by
  simp only [p16VecNormSq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ i : Fin k,
    (α * u i - z i) ^ 2 =
      α ^ 2 * u i ^ 2 - (2 * α) * (u i * z i) + z i ^ 2 from
      fun i => by ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

private lemma p16_vec_sq_nonneg {k : ℕ} (u : P16Vector k) :
    0 ≤ p16VecNormSq u := by
  unfold p16VecNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (u i))

private lemma p16_gain_bounds {k q : ℕ} (X : P16Coupling k q)
    (α T : ℝ)
    (hα : α ^ 2 ≤ T) :
    P16SquaredGainBound (p16W1 X α)
      (1 + (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) + T) ∧
    P16SquaredGainBound (p16W2 X α)
      (1 + (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) + T) := by
  have hS : 0 ≤ (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) := by
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => sq_nonneg (X i j)))
  constructor
  · intro u v
    have hcore := p16_block_arith
      (p16_vec_sq_nonneg u) (p16_vec_sq_nonneg v) hS
      (p16_matvec_sq_le X v)
      (p16_dot_sq_le u (p16MatVec X v)) hα
    change p16VecNormSq (u + p16MatVec X v) + p16VecNormSq (α • v) ≤
      (1 + (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) + T) *
        (p16VecNormSq u + p16VecNormSq v)
    rw [p16_vec_add_sq, p16_vec_smul_sq]
    exact hcore.1
  · intro u v
    have hcore := p16_block_arith
      (p16_vec_sq_nonneg u) (p16_vec_sq_nonneg v) hS
      (p16_matvec_sq_le X v)
      (p16_dot_sq_le u (p16MatVec X v)) hα
    change p16VecNormSq (α • u - p16MatVec X v) + p16VecNormSq v ≤
      (1 + (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) + T) *
        (p16VecNormSq u + p16VecNormSq v)
    rw [p16_vec_smul_sub_sq]
    exact hcore.2

private lemma p16_entry_sum_bound {k q : ℕ}
    (X ratio : P16Coupling k q) (f : ℝ)
    (h : ∀ i j, X i j ^ 2 + ratio i j ^ 2 < f ^ 2) :
    (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) +
      (∑ i : Fin k, ∑ j : Fin q, ratio i j ^ 2) ≤
        f ^ 2 * (k : ℝ) * (q : ℝ) := by
  calc
    (∑ i : Fin k, ∑ j : Fin q, X i j ^ 2) +
        (∑ i : Fin k, ∑ j : Fin q, ratio i j ^ 2) =
      ∑ i : Fin k, ∑ j : Fin q, (X i j ^ 2 + ratio i j ^ 2) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ ∑ i : Fin k, ∑ _j : Fin q, f ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact le_of_lt (h i j)
    _ = f ^ 2 * (k : ℝ) * (q : ℝ) := by
      simp
      ring

/-- P16-C1: the two strong rank-revealing bounds in Theorem 3.2. -/
theorem p16_c1_theorem3_2 {k q : ℕ} (data : P16Theorem32Data k q) :
    (∀ i, data.sigmaMTop i / p16StrongFactor k q data.f ≤ data.sigmaA i) ∧
    (∀ j, data.sigmaC j ≤
      data.sigmaMTail j * p16StrongFactor k q data.f) := by
  -- PROOF_START P16-C1-H001
  let T : ℝ := ∑ i : Fin k, ∑ j : Fin q, data.ratio i j ^ 2
  let S : ℝ := ∑ i : Fin k, ∑ j : Fin q, data.X i j ^ 2
  let G : ℝ := 1 + data.f ^ 2 * (k : ℝ) * (q : ℝ)
  have hST : S + T ≤ data.f ^ 2 * (k : ℝ) * (q : ℝ) :=
    p16_entry_sum_bound data.X data.ratio data.f data.p_lt_f
  have hgain := p16_gain_bounds data.X data.alpha T data.alpha_sq_le
  have hSG : 1 + S + T ≤ G := by dsimp [G] ; linarith
  have hGpos : 0 < G := by
    dsimp [G]
    positivity
  have hG : 0 ≤ G := le_of_lt hGpos
  have hgain1 : P16SquaredGainBound (p16W1 data.X data.alpha) G := by
    intro u v
    exact (hgain.1 u v).trans
      (mul_le_mul_of_nonneg_right hSG
        (add_nonneg (p16_vec_sq_nonneg u) (p16_vec_sq_nonneg v)))
  have hgain2 : P16SquaredGainBound (p16W2 data.X data.alpha) G := by
    intro u v
    exact (hgain.2 u v).trans
      (mul_le_mul_of_nonneg_right hSG
        (add_nonneg (p16_vec_sq_nonneg u) (p16_vec_sq_nonneg v)))
  have htop := data.hornJohnson_top G hG hgain1
  have htail := data.hornJohnson_tail G hG hgain2
  have hsqrt_pos : 0 < Real.sqrt G := Real.sqrt_pos.2 hGpos
  constructor
  · intro i
    change data.sigmaMTop i / Real.sqrt G ≤ data.sigmaA i
    exact (div_le_iff₀ hsqrt_pos).2 (htop i)
  · intro j
    change data.sigmaC j ≤ data.sigmaMTail j * Real.sqrt G
    exact htail j

end VSCLReuse

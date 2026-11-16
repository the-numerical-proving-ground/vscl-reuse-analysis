import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

/-- P35-C1: Theorem 4.1, equations (4.6)--(4.7). -/
theorem p35_c1_loss_of_biorthogonality
    (k : ℕ)
    (T C Delta D F G K L N M : P35Matrix (k + 1))
    (a b z w : P35Vector (k + 1))
    (beta gamma theta : ℝ)
    (ha : a (Fin.last k) = 0)
    (hb : b (Fin.last k) = 0)
    (hmaster :
      gamma • p35Outer (p35LastBasis k) a -
          beta • p35Outer b (p35LastBasis k) =
        (C * T - T * C) + (Delta * T - T * Delta) +
          (D * T - T * D) + (F - G))
    (hDelta : Delta * T - T * Delta = K - L)
    (herror : F - G = N - M)
    (hCT : p35StrictLower (C * T - T * C))
    (hDT : p35StrictUpper (D * T - T * D))
    (hK : p35StrictLower K) (hL : p35StrictUpper L)
    (hN : p35StrictLower N) (hM : p35StrictUpper M)
    (hz : T *ᵥ z = theta • z)
    (hw : w ᵥ* T = theta • w)
    (hgamma : gamma * (w ⬝ᵥ p35LastBasis k) ≠ 0)
    (hbeta : beta * (p35LastBasis k ⬝ᵥ z) ≠ 0) :
    a ⬝ᵥ z =
        (w ⬝ᵥ ((K + N) *ᵥ z)) /
          (gamma * (w ⬝ᵥ p35LastBasis k)) ∧
      w ⬝ᵥ b =
        (w ⬝ᵥ ((L + M) *ᵥ z)) /
          (beta * (p35LastBasis k ⬝ᵥ z)) := by
  -- PROOF_START P35-C1-H001
  have hleft_low : p35StrictLower (gamma • p35Outer (p35LastBasis k) a) := by
    intro i j hij
    by_cases hi : i = Fin.last k
    · have hj : j = Fin.last k := le_antisymm (Fin.le_last j) (hi ▸ hij)
      simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hi, hj, ha]
    · simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hi]
  have hright_up : p35StrictUpper (beta • p35Outer b (p35LastBasis k)) := by
    intro i j hji
    by_cases hj : j = Fin.last k
    · have hi : i = Fin.last k := le_antisymm (Fin.le_last i) (hj ▸ hji)
      simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hi, hj, hb]
    · simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hj]
  have hentry (i j : Fin (k + 1)) :
      (gamma • p35Outer (p35LastBasis k) a) i j -
        (beta • p35Outer b (p35LastBasis k)) i j =
      ((C * T - T * C) i j + (K i j - L i j)) +
        (D * T - T * D) i j + (N i j - M i j) := by
    have h := congrArg (fun X : P35Matrix (k + 1) => X i j) hmaster
    simpa only [hDelta, herror, Matrix.add_apply, Matrix.sub_apply] using h
  have hlow : gamma • p35Outer (p35LastBasis k) a =
      (C * T - T * C) + K + N := by
    ext i j
    simp only [Matrix.add_apply]
    by_cases hij : i ≤ j
    · rw [hleft_low i j hij, hCT i j hij, hK i j hij, hN i j hij]
      norm_num
    · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
      have h := hentry i j
      rw [hright_up i j hji, hDT i j hji, hL i j hji, hM i j hji] at h
      linarith
  have hupp : beta • p35Outer b (p35LastBasis k) =
      L + M - (D * T - T * D) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    by_cases hji : j ≤ i
    · have hdt0 : (D * T) i j - (T * D) i j = 0 :=
        hDT i j hji
      rw [hright_up i j hji, hdt0, hL i j hji, hM i j hji]
      norm_num
    · have hij : i ≤ j := le_of_lt (lt_of_not_ge hji)
      have h := hentry i j
      rw [hleft_low i j hij, hCT i j hij, hK i j hij, hN i j hij] at h
      simp only [Matrix.sub_apply] at h
      linarith
  have hcomm (X : P35Matrix (k + 1)) :
      w ⬝ᵥ ((X * T - T * X) *ᵥ z) = 0 := by
    calc
      w ⬝ᵥ ((X * T - T * X) *ᵥ z) =
          w ⬝ᵥ (X *ᵥ (T *ᵥ z)) - w ⬝ᵥ (T *ᵥ (X *ᵥ z)) := by
            rw [Matrix.sub_mulVec, dotProduct_sub,
              ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = theta * (w ⬝ᵥ (X *ᵥ z)) - theta * (w ⬝ᵥ (X *ᵥ z)) := by
        rw [hz, Matrix.mulVec_smul, dotProduct_smul]
        rw [Matrix.dotProduct_mulVec w T, hw, smul_dotProduct]
        simp only [smul_eq_mul]
      _ = 0 := sub_self _
  have hrank_low :
      w ⬝ᵥ ((gamma • p35Outer (p35LastBasis k) a) *ᵥ z) =
        (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_smul, p35Outer,
      Matrix.vecMul_vecMulVec, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have hrank_up :
      w ⬝ᵥ ((beta • p35Outer b (p35LastBasis k)) *ᵥ z) =
        (beta * (p35LastBasis k ⬝ᵥ z)) * (w ⬝ᵥ b) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_smul, p35Outer,
      Matrix.vecMul_vecMulVec, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  have hlow' : gamma • p35Outer (p35LastBasis k) a =
      (C * T - T * C) + (K + N) := by
    rw [hlow]
    abel
  have hlow_scalar :
      (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) =
        w ⬝ᵥ ((K + N) *ᵥ z) := by
    have h := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hlow'
    dsimp only at h
    rw [Matrix.add_mulVec, dotProduct_add, hcomm C, zero_add,
      hrank_low] at h
    exact h
  have hupp_scalar :
      (beta * (p35LastBasis k ⬝ᵥ z)) * (w ⬝ᵥ b) =
        w ⬝ᵥ ((L + M) *ᵥ z) := by
    have h := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hupp
    dsimp only at h
    rw [Matrix.sub_mulVec, dotProduct_sub, hcomm D, sub_zero,
      hrank_up] at h
    exact h
  constructor
  · rw [eq_div_iff hgamma]
    nlinarith [hlow_scalar]
  · rw [eq_div_iff hbeta]
    nlinarith [hupp_scalar]

end VSCLReuse

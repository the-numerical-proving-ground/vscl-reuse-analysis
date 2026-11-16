import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

private theorem p35_split_lower_upper {n : ℕ}
    {A B C D : P35Matrix n}
    (hA : p35StrictLower A) (hB : p35StrictUpper B)
    (hC : p35StrictLower C) (hD : p35StrictUpper D)
    (h : A + B = C + D) : A = C ∧ B = D := by
  have hAC : A = C := by
    ext i j
    by_cases hij : i ≤ j
    · rw [hA i j hij, hC i j hij]
    · have hji : j ≤ i := le_of_not_ge hij
      have he := congrArg (fun X : P35Matrix n => X i j) h
      simpa [Matrix.add_apply, hB i j hji, hD i j hji] using he
  refine ⟨hAC, ?_⟩
  rw [hAC] at h
  exact add_left_cancel h

private theorem p35_outer_scalar {n : ℕ}
    (u v w z : P35Vector n) (c : ℝ) :
    w ⬝ᵥ ((c • p35Outer u v) *ᵥ z) =
      (c * (w ⬝ᵥ u)) * (v ⬝ᵥ z) := by
  rw [dotProduct_mulVec, vecMul_smul]
  simp [p35Outer, vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, mul_assoc]

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
  have hX : p35StrictLower (gamma • p35Outer (p35LastBasis k) a) := by
    intro i j hij
    by_cases hi : i = Fin.last k
    · have hj : j = Fin.last k :=
        le_antisymm (Fin.le_last j) (by simpa [hi] using hij)
      simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi, hj, ha]
    · simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi]
  have hY : p35StrictUpper (-(beta • p35Outer b (p35LastBasis k))) := by
    intro i j hji
    by_cases hj : j = Fin.last k
    · have hi : i = Fin.last k :=
        le_antisymm (Fin.le_last i) (by simpa [hj] using hji)
      simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi, hj, hb]
    · simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hj]
  have hLow : p35StrictLower ((C * T - T * C) + (K + N)) := by
    intro i j hij
    simp only [Matrix.add_apply, hCT i j hij, hK i j hij,
      hN i j hij, add_zero]
  have hUp : p35StrictUpper ((D * T - T * D) - (L + M)) := by
    intro i j hji
    simp only [Matrix.sub_apply, Matrix.add_apply, hDT i j hji,
      hL i j hji, hM i j hji, add_zero, sub_zero]
  have hgroup :
      (gamma • p35Outer (p35LastBasis k) a) +
          (-(beta • p35Outer b (p35LastBasis k))) =
        ((C * T - T * C) + (K + N)) +
          ((D * T - T * D) - (L + M)) := by
    calc
      _ = gamma • p35Outer (p35LastBasis k) a -
            beta • p35Outer b (p35LastBasis k) := by abel
      _ = (C * T - T * C) + (Delta * T - T * Delta) +
            (D * T - T * D) + (F - G) := hmaster
      _ = _ := by rw [hDelta, herror]; abel
  obtain ⟨hlower, hupper⟩ :=
    p35_split_lower_upper hX hY hLow hUp hgroup
  have hupper' :
      beta • p35Outer b (p35LastBasis k) =
        (L + M) - (D * T - T * D) := by
    calc
      _ = -(-(beta • p35Outer b (p35LastBasis k))) := by abel
      _ = -((D * T - T * D) - (L + M)) := by rw [hupper]
      _ = _ := by abel
  have hcomm (A : P35Matrix (k + 1)) :
      w ⬝ᵥ ((A * T - T * A) *ᵥ z) = 0 := by
    calc
      _ = w ⬝ᵥ (A *ᵥ (T *ᵥ z)) -
          w ⬝ᵥ (T *ᵥ (A *ᵥ z)) := by
            rw [sub_mulVec, dotProduct_sub, mulVec_mulVec, mulVec_mulVec]
      _ = w ⬝ᵥ (A *ᵥ (theta • z)) -
          (theta • w) ⬝ᵥ (A *ᵥ z) := by
            rw [hz, dotProduct_mulVec w T (A *ᵥ z), hw]
      _ = 0 := by rw [mulVec_smul, dotProduct_smul, smul_dotProduct]; exact sub_self _
  have hfirst :
      (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) =
        w ⬝ᵥ ((K + N) *ᵥ z) := by
    have hs := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hlower
    change w ⬝ᵥ ((gamma • p35Outer (p35LastBasis k) a) *ᵥ z) =
      w ⬝ᵥ (((C * T - T * C) + (K + N)) *ᵥ z) at hs
    rw [p35_outer_scalar, add_mulVec, dotProduct_add, hcomm C, zero_add] at hs
    exact hs
  have hsecond :
      (beta * (w ⬝ᵥ b)) * (p35LastBasis k ⬝ᵥ z) =
        w ⬝ᵥ ((L + M) *ᵥ z) := by
    have hs := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hupper'
    change w ⬝ᵥ ((beta • p35Outer b (p35LastBasis k)) *ᵥ z) =
      w ⬝ᵥ (((L + M) - (D * T - T * D)) *ᵥ z) at hs
    rw [p35_outer_scalar, sub_mulVec, dotProduct_sub, hcomm D, sub_zero] at hs
    exact hs
  constructor
  · apply (eq_div_iff hgamma).2
    calc
      (a ⬝ᵥ z) * (gamma * (w ⬝ᵥ p35LastBasis k)) =
          (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) := by ring
      _ = _ := hfirst
  · apply (eq_div_iff hbeta).2
    calc
      (w ⬝ᵥ b) * (beta * (p35LastBasis k ⬝ᵥ z)) =
          (beta * (w ⬝ᵥ b)) * (p35LastBasis k ⬝ᵥ z) := by ring
      _ = _ := hsecond

end VSCLReuse

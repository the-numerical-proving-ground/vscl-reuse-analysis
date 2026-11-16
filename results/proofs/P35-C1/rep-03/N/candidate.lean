import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

private theorem p35_split_triangular {n : ℕ}
    (A B C D : P35Matrix n)
    (hA : p35StrictLower A) (hB : p35StrictUpper B)
    (hC : p35StrictLower C) (hD : p35StrictUpper D)
    (h : A + B = C + D) : A = C ∧ B = D := by
  constructor
  · ext i j
    by_cases hij : i ≤ j
    · rw [hA i j hij, hC i j hij]
    · have hji : j ≤ i := le_of_not_ge hij
      have he := congrArg (fun X : P35Matrix n => X i j) h
      simpa [Matrix.add_apply, hB i j hji, hD i j hji] using he
  · ext i j
    by_cases hji : j ≤ i
    · rw [hB i j hji, hD i j hji]
    · have hij : i ≤ j := le_of_not_ge hji
      have he := congrArg (fun X : P35Matrix n => X i j) h
      simpa [Matrix.add_apply, hA i j hij, hC i j hij] using he

private theorem p35_commutator_contract {n : ℕ}
    (A T : P35Matrix n) (z w : P35Vector n) (theta : ℝ)
    (hz : T *ᵥ z = theta • z) (hw : w ᵥ* T = theta • w) :
    w ⬝ᵥ ((A * T - T * A) *ᵥ z) = 0 := by
  calc
    w ⬝ᵥ ((A * T - T * A) *ᵥ z) =
        w ⬝ᵥ (A *ᵥ (T *ᵥ z)) - (w ᵥ* T) ⬝ᵥ (A *ᵥ z) := by
          rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
            dotProduct_mulVec w T (A *ᵥ z)]
    _ = 0 := by rw [hz, hw, mulVec_smul, dotProduct_smul, smul_dotProduct]; ring

private theorem p35_outer_contract {n : ℕ}
    (u v z w : P35Vector n) (r : ℝ) :
    w ⬝ᵥ ((r • p35Outer u v) *ᵥ z) =
      r * (w ⬝ᵥ u) * (v ⬝ᵥ z) := by
  rw [dotProduct_mulVec, vecMul_smul, p35Outer, vecMul_vecMulVec,
    smul_dotProduct, smul_dotProduct]
  simp only [smul_eq_mul]
  ring

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
  have hOuterLower : p35StrictLower (gamma • p35Outer (p35LastBasis k) a) := by
    intro i j hij
    by_cases hi : i = Fin.last k
    · subst i
      have hj : j = Fin.last k := le_antisymm (Fin.le_last j) hij
      subst j
      simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, ha]
    · simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hi]
  have hOuterUpper : p35StrictUpper (-beta • p35Outer b (p35LastBasis k)) := by
    intro i j hji
    by_cases hj : j = Fin.last k
    · subst j
      have hi : i = Fin.last k := le_antisymm (Fin.le_last i) hji
      subst i
      simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hb]
    · simp [p35Outer, p35LastBasis, Matrix.vecMulVec_apply, hj]
  have hLower : p35StrictLower ((C * T - T * C) + K + N) := by
    intro i j hij
    simp [Matrix.add_apply, hCT i j hij, hK i j hij, hN i j hij]
  have hUpper : p35StrictUpper ((D * T - T * D) - L - M) := by
    intro i j hji
    simp [Matrix.sub_apply, hDT i j hji, hL i j hji, hM i j hji]
  have hsum :
      (gamma • p35Outer (p35LastBasis k) a) +
          (-beta • p35Outer b (p35LastBasis k)) =
        ((C * T - T * C) + K + N) + ((D * T - T * D) - L - M) := by
    have hm := hmaster
    rw [hDelta, herror] at hm
    calc
      _ = (C * T - T * C) + (K - L) + (D * T - T * D) + (N - M) := by
        simpa only [sub_eq_add_neg, neg_smul] using hm
      _ = _ := by abel
  obtain ⟨hlower, hupper⟩ := p35_split_triangular
    _ _ _ _ hOuterLower hOuterUpper hLower hUpper hsum
  have hc := p35_commutator_contract C T z w theta hz hw
  have hd := p35_commutator_contract D T z w theta hz hw
  have hleft :
      (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) =
        w ⬝ᵥ ((K + N) *ᵥ z) := by
    have he := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hlower
    change w ⬝ᵥ ((gamma • p35Outer (p35LastBasis k) a) *ᵥ z) =
      w ⬝ᵥ (((C * T - T * C) + K + N) *ᵥ z) at he
    rw [p35_outer_contract] at he
    simp only [add_mulVec, dotProduct_add, hc, zero_add] at he
    simpa only [add_mulVec, dotProduct_add] using he
  have hright :
      (beta * (p35LastBasis k ⬝ᵥ z)) * (w ⬝ᵥ b) =
        w ⬝ᵥ ((L + M) *ᵥ z) := by
    have he := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hupper
    change w ⬝ᵥ (((-beta) • p35Outer b (p35LastBasis k)) *ᵥ z) =
      w ⬝ᵥ (((D * T - T * D) - L - M) *ᵥ z) at he
    simp only [sub_mulVec, dotProduct_sub, p35_outer_contract] at he
    have hd' : w ⬝ᵥ ((D * T) *ᵥ z) - w ⬝ᵥ ((T * D) *ᵥ z) = 0 := by
      simpa only [sub_mulVec, dotProduct_sub] using hd
    simp only [add_mulVec, dotProduct_add]
    nlinarith [he, hd']
  constructor
  · exact (eq_div_iff hgamma).2 (by nlinarith [hleft])
  · exact (eq_div_iff hbeta).2 (by nlinarith [hright])

end VSCLReuse

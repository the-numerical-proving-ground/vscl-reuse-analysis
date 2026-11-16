import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

private lemma p35_lower_upper_separate {n : ℕ}
    (A B X Y : P35Matrix n)
    (hA : p35StrictLower A) (hB : p35StrictUpper B)
    (hX : p35StrictLower X) (hY : p35StrictUpper Y)
    (h : A - B = X - Y) : A = X ∧ B = Y := by
  have hAX : A = X := by
    ext i j
    by_cases hij : i ≤ j
    · rw [hA i j hij, hX i j hij]
    · have hji : j ≤ i := le_of_not_ge hij
      have he := congrArg (fun Z : P35Matrix n => Z i j) h
      simp only [Matrix.sub_apply, hB i j hji, hY i j hji, sub_zero] at he
      exact he
  constructor
  · exact hAX
  · rw [hAX] at h
    exact sub_right_inj.mp h

private lemma p35_commutator_pairing_zero {n : ℕ}
    (T X : P35Matrix n) (z w : P35Vector n) (theta : ℝ)
    (hz : T *ᵥ z = theta • z) (hw : w ᵥ* T = theta • w) :
    w ⬝ᵥ ((X * T - T * X) *ᵥ z) = 0 := by
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [dotProduct_sub, hz, Matrix.mulVec_smul, dotProduct_smul]
  rw [Matrix.dotProduct_mulVec w T (X *ᵥ z), hw, smul_dotProduct]
  simp

private lemma p35_pair_outer {n : ℕ}
    (u v z w : P35Vector n) (c : ℝ) :
    w ⬝ᵥ ((c • p35Outer u v) *ᵥ z) =
      c * (w ⬝ᵥ u) * (v ⬝ᵥ z) := by
  simp [p35Outer, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm]

private lemma p35_lower_outer_last {k : ℕ}
    (a : P35Vector (k + 1)) (c : ℝ)
    (ha : a (Fin.last k) = 0) :
    p35StrictLower (c • p35Outer (p35LastBasis k) a) := by
  intro i j hij
  by_cases hi : i = Fin.last k
  · have hj : j = Fin.last k := le_antisymm (Fin.le_last j) (hi ▸ hij)
    simp [Matrix.smul_apply, p35Outer, Matrix.vecMulVec_apply,
      p35LastBasis, hi, hj, ha]
  · simp [Matrix.smul_apply, p35Outer, Matrix.vecMulVec_apply,
      p35LastBasis, hi]

private lemma p35_upper_outer_last {k : ℕ}
    (b : P35Vector (k + 1)) (c : ℝ)
    (hb : b (Fin.last k) = 0) :
    p35StrictUpper (c • p35Outer b (p35LastBasis k)) := by
  intro i j hji
  by_cases hj : j = Fin.last k
  · have hi : i = Fin.last k := le_antisymm (Fin.le_last i) (hj ▸ hji)
    simp [Matrix.smul_apply, p35Outer, Matrix.vecMulVec_apply,
      p35LastBasis, hi, hj, hb]
  · simp [Matrix.smul_apply, p35Outer, Matrix.vecMulVec_apply,
      p35LastBasis, hj]

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
  have hX : p35StrictLower ((C * T - T * C + K) + N) := by
    intro i j hij
    simp [Matrix.add_apply, hCT i j hij, hK i j hij, hN i j hij]
  have hY : p35StrictUpper ((-(D * T - T * D) + L) + M) := by
    intro i j hji
    simp only [Matrix.add_apply, Matrix.neg_apply, hDT i j hji,
      hL i j hji, hM i j hji, neg_zero, zero_add]
  have hsep :
      gamma • p35Outer (p35LastBasis k) a = (C * T - T * C + K) + N ∧
      beta • p35Outer b (p35LastBasis k) = (-(D * T - T * D) + L) + M := by
    apply p35_lower_upper_separate
      (gamma • p35Outer (p35LastBasis k) a)
      (beta • p35Outer b (p35LastBasis k))
      ((C * T - T * C + K) + N)
      ((-(D * T - T * D) + L) + M)
    · exact p35_lower_outer_last a gamma ha
    · exact p35_upper_outer_last b beta hb
    · exact hX
    · exact hY
    · calc
        gamma • p35Outer (p35LastBasis k) a -
            beta • p35Outer b (p35LastBasis k) =
          (C * T - T * C) + (Delta * T - T * Delta) +
            (D * T - T * D) + (F - G) := hmaster
        _ = ((C * T - T * C + K) + N) -
            ((-(D * T - T * D) + L) + M) := by
          rw [hDelta, herror]
          abel
  have hfirst :
      gamma * (w ⬝ᵥ p35LastBasis k) * (a ⬝ᵥ z) =
        w ⬝ᵥ ((K + N) *ᵥ z) := by
    calc
      gamma * (w ⬝ᵥ p35LastBasis k) * (a ⬝ᵥ z) =
          w ⬝ᵥ ((gamma • p35Outer (p35LastBasis k) a) *ᵥ z) :=
        (p35_pair_outer (p35LastBasis k) a z w gamma).symm
      _ = w ⬝ᵥ (((C * T - T * C + K) + N) *ᵥ z) := by rw [hsep.1]
      _ = w ⬝ᵥ ((K + N) *ᵥ z) := by
        simp [Matrix.add_mulVec, dotProduct_add,
          p35_commutator_pairing_zero T C z w theta hz hw]
  have hsecond :
      beta * (p35LastBasis k ⬝ᵥ z) * (w ⬝ᵥ b) =
        w ⬝ᵥ ((L + M) *ᵥ z) := by
    calc
      beta * (p35LastBasis k ⬝ᵥ z) * (w ⬝ᵥ b) =
          w ⬝ᵥ ((beta • p35Outer b (p35LastBasis k)) *ᵥ z) := by
        rw [p35_pair_outer]
        ring
      _ = w ⬝ᵥ (((-(D * T - T * D) + L) + M) *ᵥ z) := by rw [hsep.2]
      _ = w ⬝ᵥ ((L + M) *ᵥ z) := by
        simp only [Matrix.add_mulVec, Matrix.neg_mulVec, dotProduct_add,
          dotProduct_neg, p35_commutator_pairing_zero T D z w theta hz hw,
          neg_zero, zero_add]
  constructor
  · apply (eq_div_iff hgamma).2
    simpa [mul_comm] using hfirst
  · apply (eq_div_iff hbeta).2
    simpa [mul_comm] using hsecond

end VSCLReuse

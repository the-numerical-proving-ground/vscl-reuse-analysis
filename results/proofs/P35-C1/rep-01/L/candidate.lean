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
  let e := p35LastBasis k
  let A := p35Outer e a
  let B := p35Outer b e
  let X := C * T - T * C
  let Y := D * T - T * D
  have hA : p35StrictLower A := by
    intro i j hij
    by_cases hi : i = Fin.last k
    · have hj : j = Fin.last k := le_antisymm (Fin.le_last j) (hi ▸ hij)
      simp [A, e, p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi, hj, ha]
    · simp [A, e, p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi]
  have hB : p35StrictUpper B := by
    intro i j hji
    by_cases hj : j = Fin.last k
    · have hi : i = Fin.last k := le_antisymm (Fin.le_last i) (hj ▸ hji)
      simp [B, e, p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi, hj, hb]
    · simp [B, e, p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hj]
  have hm : gamma • A - beta • B = X + (K - L) + Y + (N - M) := by
    simpa [A, B, X, Y, e, hDelta, herror] using hmaster
  have hlow : gamma • A = X + K + N := by
    ext i j
    have hmij := congrArg (fun Q : P35Matrix (k + 1) => Q i j) hm
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hmij ⊢
    by_cases hij : i ≤ j
    · have haij := hA i j hij
      have hxij := hCT i j hij
      have hkij := hK i j hij
      have hnij := hN i j hij
      change X i j = 0 at hxij
      simp [haij, hxij, hkij, hnij]
    · have hji : j ≤ i := le_of_not_ge hij
      have hbij := hB i j hji
      have hyij := hDT i j hji
      have hlij := hL i j hji
      have hmij' := hM i j hji
      change Y i j = 0 at hyij
      simp only [hbij, hyij, hlij, hmij', mul_zero, sub_zero, add_zero] at hmij
      linarith
  have hupp : beta • B = -Y + L + M := by
    calc
      beta • B = gamma • A - (gamma • A - beta • B) := by abel
      _ = -Y + L + M := by rw [hm, hlow]; abel
  have hcomm (Q : P35Matrix (k + 1)) :
      w ⬝ᵥ ((Q * T - T * Q) *ᵥ z) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hz, Matrix.dotProduct_mulVec w T (Q *ᵥ z), hw,
      Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp
  have houterA : w ⬝ᵥ (A *ᵥ z) = (w ⬝ᵥ e) * (a ⬝ᵥ z) := by
    simp [A, p35Outer, Matrix.vecMulVec_mulVec, dotProduct_smul, smul_eq_mul,
      mul_comm]
  have houterB : w ⬝ᵥ (B *ᵥ z) = (w ⬝ᵥ b) * (e ⬝ᵥ z) := by
    simp [B, p35Outer, Matrix.vecMulVec_mulVec, dotProduct_smul, smul_eq_mul,
      mul_comm]
  have hscalarA :
      gamma * (w ⬝ᵥ e) * (a ⬝ᵥ z) = w ⬝ᵥ ((K + N) *ᵥ z) := by
    have h := congrArg (fun Q : P35Matrix (k + 1) => w ⬝ᵥ (Q *ᵥ z)) hlow
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.add_mulVec, dotProduct_add, houterA] at h
    have hc : w ⬝ᵥ (X *ᵥ z) = 0 := hcomm C
    simp only [X] at hc
    rw [hc, zero_add] at h
    calc
      gamma * (w ⬝ᵥ e) * (a ⬝ᵥ z) = gamma * ((w ⬝ᵥ e) * (a ⬝ᵥ z)) := by ring
      _ = w ⬝ᵥ ((K + N) *ᵥ z) := by
        rw [Matrix.add_mulVec, dotProduct_add]
        exact h
  have hscalarB :
      beta * (e ⬝ᵥ z) * (w ⬝ᵥ b) = w ⬝ᵥ ((L + M) *ᵥ z) := by
    have h := congrArg (fun Q : P35Matrix (k + 1) => w ⬝ᵥ (Q *ᵥ z)) hupp
    simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.add_mulVec, dotProduct_add, houterB] at h
    have hc : w ⬝ᵥ (Y *ᵥ z) = 0 := hcomm D
    rw [Matrix.neg_mulVec z Y, dotProduct_neg, hc] at h
    simp only [neg_zero, zero_add] at h
    calc
      beta * (e ⬝ᵥ z) * (w ⬝ᵥ b) = beta * ((w ⬝ᵥ b) * (e ⬝ᵥ z)) := by ring
      _ = w ⬝ᵥ ((L + M) *ᵥ z) := by
        rw [Matrix.add_mulVec, dotProduct_add]
        exact h
  constructor
  · apply (eq_div_iff hgamma).2
    simpa [e, mul_comm, mul_left_comm, mul_assoc] using hscalarA
  · apply (eq_div_iff hbeta).2
    simpa [e, mul_comm, mul_left_comm, mul_assoc] using hscalarB

end VSCLReuse

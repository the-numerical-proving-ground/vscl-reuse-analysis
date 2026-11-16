import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

private lemma p35_separate_triangles {n : ℕ}
    {A B U V : P35Matrix n}
    (hA : p35StrictLower A) (hB : p35StrictLower B)
    (hU : p35StrictUpper U) (hV : p35StrictUpper V)
    (h : A + U = B + V) : A = B ∧ U = V := by
  constructor
  · ext i j
    rcases le_total i j with hij | hji
    · exact (hA i j hij).trans (hB i j hij).symm
    · have he := congrArg (fun X : P35Matrix n => X i j) h
      simp only [Matrix.add_apply, hU i j hji, hV i j hji, add_zero] at he
      exact he
  · ext i j
    rcases le_total i j with hij | hji
    · have he := congrArg (fun X : P35Matrix n => X i j) h
      simp only [Matrix.add_apply, hA i j hij, hB i j hij, zero_add] at he
      exact he
    · exact (hU i j hji).trans (hV i j hji).symm

private lemma p35_outer_last_lower (k : ℕ) (a : P35Vector (k + 1))
    (ha : a (Fin.last k) = 0) (gamma : ℝ) :
    p35StrictLower (gamma • p35Outer (p35LastBasis k) a) := by
  intro i j hij
  by_cases hi : i = Fin.last k
  · subst i
    have hj : j = Fin.last k := Fin.le_last j |>.antisymm hij
    subst j
    simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, ha]
  · simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hi]

private lemma p35_outer_last_upper (k : ℕ) (b : P35Vector (k + 1))
    (hb : b (Fin.last k) = 0) (beta : ℝ) :
    p35StrictUpper (-(beta • p35Outer b (p35LastBasis k))) := by
  intro i j hji
  by_cases hj : j = Fin.last k
  · subst j
    have hi : i = Fin.last k := Fin.le_last i |>.antisymm hji
    subst i
    simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hb]
  · simp [p35Outer, Matrix.vecMulVec_apply, p35LastBasis, hj]

private lemma p35_commutator_eval {n : ℕ}
    (T X : P35Matrix n) (z w : P35Vector n) (theta : ℝ)
    (hz : T *ᵥ z = theta • z) (hw : w ᵥ* T = theta • w) :
    w ⬝ᵥ ((X * T - T * X) *ᵥ z) = 0 := by
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [dotProduct_sub, hz, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.dotProduct_mulVec w T (X *ᵥ z), hw,
    smul_dotProduct]
  exact sub_self _

private lemma p35_left_outer_eval {n : ℕ}
    (e a z w : P35Vector n) (gamma : ℝ) :
    w ⬝ᵥ ((gamma • p35Outer e a) *ᵥ z) =
      (gamma * (w ⬝ᵥ e)) * (a ⬝ᵥ z) := by
  rw [Matrix.smul_mulVec, dotProduct_smul,
    Matrix.dotProduct_mulVec]
  simp [p35Outer, Matrix.vecMul_vecMulVec, smul_dotProduct,
    smul_eq_mul, mul_assoc]

private lemma p35_right_outer_eval {n : ℕ}
    (e b z w : P35Vector n) (beta : ℝ) :
    w ⬝ᵥ ((beta • p35Outer b e) *ᵥ z) =
      (beta * (e ⬝ᵥ z)) * (w ⬝ᵥ b) := by
  rw [Matrix.smul_mulVec, dotProduct_smul,
    Matrix.dotProduct_mulVec]
  simp [p35Outer, Matrix.vecMul_vecMulVec, smul_dotProduct,
    smul_eq_mul, mul_comm, mul_left_comm]

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
  have hrl : p35StrictLower (gamma • p35Outer (p35LastBasis k) a) :=
    p35_outer_last_lower k a ha gamma
  have hru : p35StrictUpper (-(beta • p35Outer b (p35LastBasis k))) :=
    p35_outer_last_upper k b hb beta
  have hcl : p35StrictLower ((C * T - T * C) + (K + N)) := by
    intro i j hij
    simp [Matrix.add_apply, hCT i j hij, hK i j hij, hN i j hij]
  have hcu : p35StrictUpper ((D * T - T * D) - L - M) := by
    intro i j hji
    simp [Matrix.sub_apply, hDT i j hji, hL i j hji, hM i j hji]
  have hsplit :
      gamma • p35Outer (p35LastBasis k) a +
          -(beta • p35Outer b (p35LastBasis k)) =
        ((C * T - T * C) + (K + N)) +
          ((D * T - T * D) - L - M) := by
    calc
      _ = gamma • p35Outer (p35LastBasis k) a -
            beta • p35Outer b (p35LastBasis k) := by abel
      _ = (C * T - T * C) + (Delta * T - T * Delta) +
            (D * T - T * D) + (F - G) := hmaster
      _ = ((C * T - T * C) + (K + N)) +
            ((D * T - T * D) - L - M) := by
        rw [hDelta, herror]
        abel
  obtain ⟨hlower, hupper⟩ :=
    p35_separate_triangles hrl hcl hru hcu hsplit
  have hupper' :
      beta • p35Outer b (p35LastBasis k) =
        -(D * T - T * D) + (L + M) := by
    calc
      _ = -(-(beta • p35Outer b (p35LastBasis k))) := by simp
      _ = -((D * T - T * D) - L - M) := by rw [hupper]
      _ = -(D * T - T * D) + (L + M) := by abel
  have hleft :
      (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) =
        w ⬝ᵥ ((K + N) *ᵥ z) := by
    have h := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hlower
    change w ⬝ᵥ ((gamma • p35Outer (p35LastBasis k) a) *ᵥ z) =
      w ⬝ᵥ (((C * T - T * C) + (K + N)) *ᵥ z) at h
    rw [p35_left_outer_eval, Matrix.add_mulVec, dotProduct_add,
      p35_commutator_eval T C z w theta hz hw, zero_add] at h
    exact h
  have hright :
      (beta * (p35LastBasis k ⬝ᵥ z)) * (w ⬝ᵥ b) =
        w ⬝ᵥ ((L + M) *ᵥ z) := by
    have h := congrArg (fun X : P35Matrix (k + 1) => w ⬝ᵥ (X *ᵥ z)) hupper'
    change w ⬝ᵥ ((beta • p35Outer b (p35LastBasis k)) *ᵥ z) =
      w ⬝ᵥ ((-(D * T - T * D) + (L + M)) *ᵥ z) at h
    rw [p35_right_outer_eval, Matrix.add_mulVec, Matrix.neg_mulVec,
      dotProduct_add, dotProduct_neg,
      p35_commutator_eval T D z w theta hz hw] at h
    simpa using h
  constructor
  · apply (eq_div_iff hgamma).2
    calc
      (a ⬝ᵥ z) * (gamma * (w ⬝ᵥ p35LastBasis k)) =
          (gamma * (w ⬝ᵥ p35LastBasis k)) * (a ⬝ᵥ z) := by ring
      _ = w ⬝ᵥ ((K + N) *ᵥ z) := hleft
  · apply (eq_div_iff hbeta).2
    calc
      (w ⬝ᵥ b) * (beta * (p35LastBasis k ⬝ᵥ z)) =
          (beta * (p35LastBasis k ⬝ᵥ z)) * (w ⬝ᵥ b) := by ring
      _ = w ⬝ᵥ ((L + M) *ᵥ z) := hright

end VSCLReuse

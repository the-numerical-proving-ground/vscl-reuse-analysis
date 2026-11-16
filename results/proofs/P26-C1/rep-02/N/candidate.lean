import VSCLReuse.P26.Definitions

namespace VSCLReuse

private lemma p26FrobeniusSq_trace {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p26FrobeniusSq M = (M.transpose * M).trace := by
  simp only [p26FrobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]

private lemma p26FrobeniusSq_orthogonal {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  rw [p26FrobeniusSq_trace, p26FrobeniusSq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    ((Q * (M.transpose * Q.transpose)) * (Q * M * Q.transpose)).trace =
        (Q * (M.transpose * M) * Q.transpose).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q.transpose Q (M * Q.transpose), hQtQ, Matrix.one_mul]
    _ = (M.transpose * M).trace := by
      rw [Matrix.trace_mul_cycle]
      simp [hQtQ]

private lemma p26_scalar_projection (a b : ℝ) (hb : 0 ≤ b) :
    (a - max a 0) ^ 2 ≤ (a - b) ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _
  · have ha' : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    rw [max_eq_right ha']
    nlinarith [sq_nonneg b, mul_nonneg (neg_nonneg.mpr ha') hb]

private lemma p26_diagonal_projection {n : ℕ}
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i, 0 ≤ C i i) :
    p26FrobeniusSq
      (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
    p26FrobeniusSq (Matrix.diagonal lambda - C) := by
  unfold p26FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa using p26_scalar_projection (lambda i) (C i i) (hC i)
  · simp only [Matrix.sub_apply, Matrix.diagonal_apply, if_neg hij,
      zero_sub]
    simpa using sq_nonneg (-C i j)

/-- P26-C1: the weighted positive-semidefinite projection formula of Theorem 3.2. -/
theorem p26_c1_weighted_psd_projection
    (n : ℕ)
    (A S Sinv Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ)
    (hSsymm : S.transpose = S)
    (hSinvSymm : Sinv.transpose = Sinv)
    (hSInv : S * Sinv = 1)
    (hInvS : Sinv * S = 1)
    (hQtQ : Q.transpose * Q = 1)
    (hQQt : Q * Q.transpose = 1)
    (hSpectral : S * A * S = Q * Matrix.diagonal lambda * Q.transpose) :
    let X := p26WeightedPsdProjection Sinv Q lambda
    X.PosSemidef ∧
      (∀ Z : Matrix (Fin n) (Fin n) ℝ,
        Z.PosSemidef →
          p26WeightedFrobeniusSq S (A - X) ≤
            p26WeightedFrobeniusSq S (A - Z)) ∧
      ∀ i, A i i ≤ X i i := by
  -- PROOF_START P26-C1-H001
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let Dp : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let P : Matrix (Fin n) (Fin n) ℝ := Q * Dp * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * P * Sinv
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ,
      Z.PosSemidef →
        p26WeightedFrobeniusSq S (A - X) ≤
          p26WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i
  have hDp : Dp.PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hP : P.PosSemidef := by
    simpa only [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hDp.mul_mul_conjTranspose_same Q
  have hX : X.PosSemidef := by
    simpa only [X, Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using
      hP.mul_mul_conjTranspose_same Sinv
  have hSX : S * X * S = P := by
    calc
      S * X * S = (S * Sinv) * P * (Sinv * S) := by
        dsimp [X]
        simp only [Matrix.mul_assoc]
      _ = P := by rw [hSInv, hInvS]; simp
  have hA : Sinv * (S * A * S) * Sinv = A := by
    calc
      Sinv * (S * A * S) * Sinv = (Sinv * S) * A * (S * Sinv) := by
        simp only [Matrix.mul_assoc]
      _ = A := by rw [hInvS, hSInv]; simp
  have hDiffD : (Dp - D).PosSemidef := by
    rw [show Dp - D = Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) by
      simp only [Dp, D, Matrix.diagonal_sub]]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (le_max_left _ _)
  have hDiffP : (P - S * A * S).PosSemidef := by
    have heq : P - S * A * S = Q * (Dp - D) * Q.transpose := by
      rw [hSpectral]
      dsimp [P, D]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [heq]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hDiffD.mul_mul_conjTranspose_same Q
  have hDiffX : (X - A).PosSemidef := by
    have heq : X - A = Sinv * (P - S * A * S) * Sinv := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hA]
    rw [heq]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using
      hDiffP.mul_mul_conjTranspose_same Sinv
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * (S * Z * S) * Q
    have hSZ : (S * Z * S).PosSemidef := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using
        hZ.mul_mul_conjTranspose_same S
    have hC : C.PosSemidef := by
      simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_transpose] using
        hSZ.mul_mul_conjTranspose_same Q.transpose
    have hQC : Q * C * Q.transpose = S * Z * S := by
      calc
        Q * C * Q.transpose = (Q * Q.transpose) * (S * Z * S) *
            (Q * Q.transpose) := by
              dsimp [C]
              simp only [Matrix.mul_assoc]
        _ = S * Z * S := by rw [hQQt]; simp
    have hresX : S * (A - X) * S = Q * (D - Dp) * Q.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSX, hSpectral]
      dsimp [P, D]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    have hresZ : S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSpectral, ← hQC]
      dsimp [D]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    unfold p26WeightedFrobeniusSq
    rw [hresX, hresZ, p26FrobeniusSq_orthogonal Q (D - Dp) hQtQ,
      p26FrobeniusSq_orthogonal Q (D - C) hQtQ]
    exact p26_diagonal_projection lambda C (fun i => hC.diag_nonneg)
  · intro i
    have hi := hDiffX.diag_nonneg (i := i)
    simpa only [Matrix.sub_apply] using (sub_nonneg.mp hi)

end VSCLReuse

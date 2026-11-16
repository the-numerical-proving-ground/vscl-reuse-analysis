import VSCLReuse.P26.Definitions

namespace VSCLReuse

private lemma p26FrobeniusSq_eq_trace (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    p26FrobeniusSq M = Matrix.trace (M.transpose * M) := by
  simp only [p26FrobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]

private lemma p26FrobeniusSq_orthogonal_congr (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  rw [p26FrobeniusSq_eq_trace, p26FrobeniusSq_eq_trace]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    Matrix.trace ((Q * (M.transpose * Q.transpose)) * (Q * M * Q.transpose))
        = Matrix.trace (Q * (M.transpose * (Q.transpose * Q) * M) * Q.transpose) := by
            congr 1
            noncomm_ring
    _ = Matrix.trace (Q * (M.transpose * M) * Q.transpose) := by
      rw [hQtQ]
      simp
    _ = Matrix.trace (M.transpose * M) := by
      rw [Matrix.trace_mul_cycle]
      simp [hQtQ]

private lemma p26_scalar_sq_min (a b : ℝ) (hb : 0 ≤ b) :
    (a - max a 0) ^ 2 ≤ (a - b) ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    nlinarith [sq_nonneg (a - b)]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [max_eq_right ha']
    nlinarith [mul_nonneg (neg_nonneg.mpr ha') hb, sq_nonneg b]

private lemma p26FrobeniusSq_diagonal_min (n : ℕ)
    (lambda : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) :
    p26FrobeniusSq
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p26FrobeniusSq (Matrix.diagonal lambda - B) := by
  unfold p26FrobeniusSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simpa using p26_scalar_sq_min (lambda i) (B i i) hB.diag_nonneg
  · simp only [Matrix.sub_apply, Matrix.diagonal_apply, if_neg hij,
      sub_zero, zero_sub]
    simpa using sq_nonneg (-B i j)

private lemma p26_psd_congr (n : ℕ)
    (T B : Matrix (Fin n) (Fin n) ℝ) (hT : T.transpose = T)
    (hB : B.PosSemidef) : (T * B * T).PosSemidef := by
  simpa [Matrix.conjTranspose, hT] using hB.mul_mul_conjTranspose_same T

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
  let P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let C : Matrix (Fin n) (Fin n) ℝ := Q * P * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := Sinv * C * Sinv
  have hP : P.PosSemidef := by
    dsimp [P]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hPD : (P - D).PosSemidef := by
    dsimp [P, D]
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (le_max_left _ _)
  have hC : C.PosSemidef := by
    dsimp [C]
    simpa [Matrix.conjTranspose] using hP.mul_mul_conjTranspose_same Q
  have hX : X.PosSemidef := p26_psd_congr n Sinv C hSinvSymm hC
  have hA : A = Sinv * (Q * D * Q.transpose) * Sinv := by
    have hA' : A = Sinv * (S * A * S) * Sinv := by
      calc
        A = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]; simp
        _ = Sinv * (S * A * S) * Sinv := by noncomm_ring
    rw [hA', hSpectral]
  have hXA : X - A = Sinv * (Q * (P - D) * Q.transpose) * Sinv := by
    rw [hA]
    dsimp [X, C]
    noncomm_ring
  have hXApsd : (X - A).PosSemidef := by
    rw [hXA]
    have hQPD : (Q * (P - D) * Q.transpose).PosSemidef := by
      simpa [Matrix.conjTranspose] using hPD.mul_mul_conjTranspose_same Q
    exact p26_psd_congr n Sinv _ hSinvSymm hQPD
  have hSX : S * X * S = Q * P * Q.transpose := by
    dsimp [X, C]
    calc
      S * (Sinv * (Q * P * Q.transpose) * Sinv) * S =
          (S * Sinv) * (Q * P * Q.transpose) * (Sinv * S) := by noncomm_ring
      _ = Q * P * Q.transpose := by rw [hSInv, hInvS]; simp
  have hAX : S * (A - X) * S = Q * (D - P) * Q.transpose := by
    calc
      S * (A - X) * S = S * A * S - S * X * S := by noncomm_ring
      _ = Q * D * Q.transpose - Q * P * Q.transpose := by rw [hSpectral, hSX]
      _ = Q * (D - P) * Q.transpose := by noncomm_ring
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p26WeightedFrobeniusSq S (A - X) ≤
        p26WeightedFrobeniusSq S (A - Z)) ∧
      ∀ i, A i i ≤ X i i
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let B : Matrix (Fin n) (Fin n) ℝ := Q.transpose * (S * Z * S) * Q
    have hSZpsd : (S * Z * S).PosSemidef := p26_psd_congr n S Z hSsymm hZ
    have hB : B.PosSemidef := by
      dsimp [B]
      simpa [Matrix.conjTranspose] using
        hSZpsd.mul_mul_conjTranspose_same Q.transpose
    have hSZ : S * Z * S = Q * B * Q.transpose := by
      dsimp [B]
      calc
        S * Z * S = (Q * Q.transpose) * (S * Z * S) * (Q * Q.transpose) := by
          rw [hQQt]
          simp
        _ = Q * (Q.transpose * (S * Z * S) * Q) * Q.transpose := by
          noncomm_ring
    have hAZ : S * (A - Z) * S = Q * (D - B) * Q.transpose := by
      calc
        S * (A - Z) * S = S * A * S - S * Z * S := by noncomm_ring
        _ = Q * D * Q.transpose - Q * B * Q.transpose := by rw [hSpectral, hSZ]
        _ = Q * (D - B) * Q.transpose := by noncomm_ring
    unfold p26WeightedFrobeniusSq
    rw [hAX, hAZ, p26FrobeniusSq_orthogonal_congr n Q (D - P) hQtQ,
      p26FrobeniusSq_orthogonal_congr n Q (D - B) hQtQ]
    exact p26FrobeniusSq_diagonal_min n lambda B hB
  · intro i
    have hi := hXApsd.diag_nonneg (i := i)
    simp only [Matrix.sub_apply] at hi
    linarith

end VSCLReuse

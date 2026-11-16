import VSCLReuse.P26.Definitions

namespace VSCLReuse

private theorem p26_frob_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    p26FrobeniusSq M = (M.transpose * M).trace := by
  classical
  simp only [p26FrobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

private theorem p26_frob_orthogonal {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  classical
  rw [p26_frob_eq_trace, p26_frob_eq_trace]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (Q * (M.transpose * Q.transpose) * (Q * M * Q.transpose)).trace =
        (Q * (M.transpose * M) * Q.transpose).trace := by
          calc
            _ = (Q * M.transpose * (Q.transpose * Q) * M * Q.transpose).trace := by
              simp only [Matrix.mul_assoc]
            _ = _ := by rw [hQtQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (M.transpose * M).trace := by
      rw [Matrix.trace_mul_comm (Q * (M.transpose * M)) Q.transpose]
      simp only [← Matrix.mul_assoc, hQtQ, Matrix.one_mul]

private theorem p26_scalar_projection (x y : ℝ) (hy : 0 ≤ y) :
    (x - max x 0) ^ 2 ≤ (x - y) ^ 2 := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, sub_self]
    simpa using sq_nonneg (x - y)
  · rw [max_eq_right hx, sub_zero]
    nlinarith [sq_nonneg y, mul_nonneg (neg_nonneg.mpr hx) hy]

private theorem p26_diagonal_projection {n : ℕ} (lambda : Fin n → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : C.PosSemidef) :
    p26FrobeniusSq (Matrix.diagonal lambda -
      Matrix.diagonal (fun i => max (lambda i) 0)) ≤
    p26FrobeniusSq (Matrix.diagonal lambda - C) := by
  classical
  unfold p26FrobeniusSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simpa [Matrix.sub_apply, Matrix.diagonal_apply] using
      p26_scalar_projection (lambda i) (C i i) hC.diag_nonneg
  · simp [Matrix.sub_apply, hij, sq_nonneg]

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
  classical
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let E : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => max (lambda i) 0)
  let P : Matrix (Fin n) (Fin n) ℝ := Q * E * Q.transpose
  let X : Matrix (Fin n) (Fin n) ℝ := p26WeightedPsdProjection Sinv Q lambda
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p26WeightedFrobeniusSq S (A - X) ≤
      p26WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i
  have hEpos : E.PosSemidef := by
    dsimp [E]
    exact Matrix.PosSemidef.diagonal (by intro i; exact le_max_right _ _)
  have hEDpos : (E - D).PosSemidef := by
    have hdiag : E - D = Matrix.diagonal (fun i => max (lambda i) 0 - lambda i) := by
      simp [D, E, Matrix.diagonal_sub]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal (by
      intro i
      exact sub_nonneg.mpr (le_max_left _ _))
  have hPpos : P.PosSemidef := by
    simpa [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hEpos.mul_mul_conjTranspose_same Q
  have hXpos : X.PosSemidef := by
    have h := hPpos.mul_mul_conjTranspose_same Sinv
    simpa [X, p26WeightedPsdProjection, p26SpectralPositivePart, P,
      Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h
  have hSXS : S * X * S = P := by
    dsimp [X, p26WeightedPsdProjection, p26SpectralPositivePart, P]
    calc
      S * (Sinv * (Q * E * Q.transpose) * Sinv) * S =
          (S * Sinv) * (Q * E * Q.transpose) * (Sinv * S) := by
            simp only [Matrix.mul_assoc]
      _ = Q * E * Q.transpose := by rw [hSInv, hInvS]; simp
  have hSAS : S * A * S = Q * D * Q.transpose := hSpectral
  have hQback (M : Matrix (Fin n) (Fin n) ℝ) :
      Q * (Q.transpose * M * Q) * Q.transpose = M := by
    calc
      Q * (Q.transpose * M * Q) * Q.transpose =
          (Q * Q.transpose) * M * (Q * Q.transpose) := by
            simp only [Matrix.mul_assoc]
      _ = M := by rw [hQQt]; simp
  have hSAX : S * (A - X) * S = Q * (D - E) * Q.transpose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hSAS, hSXS]
    simp only [P, Matrix.mul_sub, Matrix.sub_mul]
  have hXminusA : X - A = Sinv * (Q * (E - D) * Q.transpose) * Sinv := by
    have hAX : S * (X - A) * S = Q * (E - D) * Q.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSXS, hSAS]
      simp only [P, Matrix.mul_sub, Matrix.sub_mul]
    calc
      X - A = Sinv * (S * (X - A) * S) * Sinv := by
        symm
        calc
          Sinv * (S * (X - A) * S) * Sinv =
              (Sinv * S) * (X - A) * (S * Sinv) := by
                simp only [Matrix.mul_assoc]
          _ = X - A := by rw [hInvS, hSInv]; simp
      _ = _ := by rw [hAX]
  refine ⟨hXpos, ?_, ?_⟩
  · intro Z hZ
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * (S * Z * S) * Q
    have hSZpos : (S * Z * S).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using
        hZ.conjTranspose_mul_mul_same S
    have hCpos : C.PosSemidef := by
      simpa [C, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hSZpos.conjTranspose_mul_mul_same Q
    have hSZ : S * Z * S = Q * C * Q.transpose := by
      simpa [C] using (hQback (S * Z * S)).symm
    have hSAZ : S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hSAS, hSZ]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    calc
      p26WeightedFrobeniusSq S (A - X) = p26FrobeniusSq (D - E) := by
        rw [p26WeightedFrobeniusSq, hSAX]
        exact p26_frob_orthogonal Q (D - E) hQtQ
      _ ≤ p26FrobeniusSq (D - C) := by
        simpa [D, E] using p26_diagonal_projection lambda C hCpos
      _ = p26WeightedFrobeniusSq S (A - Z) := by
        rw [p26WeightedFrobeniusSq, hSAZ]
        exact (p26_frob_orthogonal Q (D - C) hQtQ).symm
  · intro i
    have hdiff : (X - A).PosSemidef := by
      have h := (hEDpos.mul_mul_conjTranspose_same Q).mul_mul_conjTranspose_same Sinv
      simpa [hXminusA, Matrix.conjTranspose_eq_transpose_of_trivial,
        hSinvSymm] using h
    have hi := hdiff.diag_nonneg (i := i)
    simpa [Matrix.sub_apply] using hi

end VSCLReuse

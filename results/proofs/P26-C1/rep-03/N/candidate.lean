import VSCLReuse.P26.Definitions

namespace VSCLReuse

private lemma p26_frob_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    p26FrobeniusSq M = (M.transpose * M).trace := by
  simp only [p26FrobeniusSq, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]

private lemma p26_frob_orthogonal {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  rw [p26_frob_trace, p26_frob_trace]
  calc
    ((Q * M * Q.transpose).transpose * (Q * M * Q.transpose)).trace =
        (Q * (M.transpose * M) * Q.transpose).trace := by
      congr 1
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      calc
        Q * (M.transpose * Q.transpose) * (Q * M * Q.transpose) =
            Q * M.transpose * (Q.transpose * Q) * M * Q.transpose := by
              simp only [Matrix.mul_assoc]
        _ = Q * (M.transpose * M) * Q.transpose := by rw [hQtQ]; simp [Matrix.mul_assoc]
    _ = (M.transpose * M).trace := by
      rw [Matrix.trace_mul_cycle Q (M.transpose * M) Q.transpose, hQtQ, one_mul]

private lemma p26_orthogonal_recover {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    Q.transpose * (Q * M * Q.transpose) * Q = M := by
  calc
    _ = (Q.transpose * Q) * M * (Q.transpose * Q) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hQtQ]; simp

private lemma p26_scalar_sq_le (a y : ℝ) (hy : 0 ≤ y) :
    (a - max a 0)^2 ≤ (a - y)^2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    simpa using sq_nonneg (a - y)
  · have hna : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    rw [max_eq_right hna]
    nlinarith [mul_nonneg (neg_nonneg.mpr hna) hy, sq_nonneg y]

private lemma p26_frob_diag_min {n : ℕ}
    (lambda : Fin n → ℝ) (Y : Matrix (Fin n) (Fin n) ℝ)
    (hY : Y.PosSemidef) :
    p26FrobeniusSq (Matrix.diagonal lambda -
      Matrix.diagonal (fun i => max (lambda i) 0)) ≤
      p26FrobeniusSq (Matrix.diagonal lambda - Y) := by
  unfold p26FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [Matrix.sub_apply] using p26_scalar_sq_le (lambda i) (Y i i) hY.diag_nonneg
  · simpa [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij] using
      sq_nonneg (Y i j)

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
  let X : Matrix (Fin n) (Fin n) ℝ := p26WeightedPsdProjection Sinv Q lambda
  have hP : P.PosSemidef := by
    change (Matrix.diagonal (fun i => max (lambda i) 0)).PosSemidef
    exact Matrix.PosSemidef.diagonal (fun i => le_max_right (lambda i) 0)
  have hPD : (P - D).PosSemidef := by
    change (Matrix.diagonal (fun i => max (lambda i) 0) -
      Matrix.diagonal lambda).PosSemidef
    rw [Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (le_max_left (lambda i) 0))
  have hQP : (Q * P * Q.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hP.mul_mul_conjTranspose_same Q
  have hQPD : (Q * (P - D) * Q.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hPD.mul_mul_conjTranspose_same Q
  have hXpos : X.PosSemidef := by
    have h := hQP.conjTranspose_mul_mul_same Sinv
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm,
      X, p26WeightedPsdProjection, p26SpectralPositivePart, P] using h
  have hXN : (Sinv * (Q * (P - D) * Q.transpose) * Sinv).PosSemidef := by
    have h := hQPD.conjTranspose_mul_mul_same Sinv
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSinvSymm] using h
  have hAcong : A = Sinv * (Q * D * Q.transpose) * Sinv := by
    calc
      A = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]; simp
      _ = Sinv * (S * A * S) * Sinv := by simp only [Matrix.mul_assoc]
      _ = Sinv * (Q * D * Q.transpose) * Sinv := by rw [hSpectral]
  have hDiff : X - A = Sinv * (Q * (P - D) * Q.transpose) * Sinv := by
    rw [hAcong]
    change Sinv * (Q * P * Q.transpose) * Sinv -
      Sinv * (Q * D * Q.transpose) * Sinv =
      Sinv * (Q * (P - D) * Q.transpose) * Sinv
    simp only [Matrix.mul_sub, Matrix.sub_mul]
  have hSX : S * X * S = Q * P * Q.transpose := by
    change S * (Sinv * (Q * P * Q.transpose) * Sinv) * S =
      Q * P * Q.transpose
    calc
      S * (Sinv * (Q * P * Q.transpose) * Sinv) * S =
          (S * Sinv) * (Q * P * Q.transpose) * (Sinv * S) := by
            simp only [Matrix.mul_assoc]
      _ = Q * P * Q.transpose := by rw [hSInv, hInvS]; simp
  have hBasisA : Q.transpose * (S * A * S) * Q = D := by
    rw [hSpectral]
    exact p26_orthogonal_recover Q D hQtQ
  have hBasisX : Q.transpose * (S * X * S) * Q = P := by
    rw [hSX]
    exact p26_orthogonal_recover Q P hQtQ
  have hBasisSub (M : Matrix (Fin n) (Fin n) ℝ) :
      Q.transpose * (S * (A - M) * S) * Q =
        D - Q.transpose * (S * M * S) * Q := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, hBasisA]
  have hBX : Q.transpose * (S * (A - X) * S) * Q = D - P := by
    rw [hBasisSub X, hBasisX]
  have hmin : ∀ Z : Matrix (Fin n) (Fin n) ℝ,
      Z.PosSemidef →
      p26WeightedFrobeniusSq S (A - X) ≤
        p26WeightedFrobeniusSq S (A - Z) := by
    intro Z hZ
    let Y : Matrix (Fin n) (Fin n) ℝ := Q.transpose * (S * Z * S) * Q
    have hSZS : (S * Z * S).PosSemidef := by
      have h := hZ.conjTranspose_mul_mul_same S
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hSsymm] using h
    have hY : Y.PosSemidef := by
      have h := hSZS.conjTranspose_mul_mul_same Q
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Y] using h
    unfold p26WeightedFrobeniusSq
    calc
      p26FrobeniusSq (S * (A - X) * S) =
          p26FrobeniusSq (Q.transpose * (S * (A - X) * S) * Q) := by
            simpa using (p26_frob_orthogonal Q.transpose
              (S * (A - X) * S) (by simpa using hQQt)).symm
      _ = p26FrobeniusSq (D - P) := by rw [hBX]
      _ ≤ p26FrobeniusSq (D - Y) := by
        exact p26_frob_diag_min lambda Y hY
      _ = p26FrobeniusSq (Q.transpose * (S * (A - Z) * S) * Q) := by
        rw [hBasisSub Z]
      _ = p26FrobeniusSq (S * (A - Z) * S) := by
        simpa using p26_frob_orthogonal Q.transpose
          (S * (A - Z) * S) (by simpa using hQQt)
  have hdiag : ∀ i, A i i ≤ X i i := by
    intro i
    have h := hXN.diag_nonneg (i := i)
    rw [← hDiff] at h
    exact sub_nonneg.mp h
  exact ⟨hXpos, hmin, hdiag⟩

end VSCLReuse

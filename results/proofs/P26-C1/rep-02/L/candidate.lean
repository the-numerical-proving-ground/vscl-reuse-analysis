import VSCLReuse.P26.Definitions
import NumStability.Analysis.MatrixAlgebra

namespace VSCLReuse

private theorem p26_frob_mul_orthogonal_left (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    p26FrobeniusSq (Q * M) = p26FrobeniusSq M := by
  have hQ : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i j) hQtQ
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply] using h
    · intro i j
      have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i j) hQQt
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply] using h
  exact NumStability.frobNormSq_orthogonal_left Q M hQ

private theorem p26_frob_mul_orthogonal_right (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    p26FrobeniusSq (M * Q.transpose) = p26FrobeniusSq M := by
  have hQ : NumStability.IsOrthogonal n Q := by
    constructor
    · intro i j
      have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i j) hQtQ
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply] using h
    · intro i j
      have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i j) hQQt
      simpa [NumStability.matTranspose, NumStability.idMatrix,
        Matrix.mul_apply] using h
  exact NumStability.frobNormSq_orthogonal_right M Q.transpose hQ.transpose

private theorem p26_scalar_projection_sq_le (a z : ℝ) (hz : 0 ≤ z) :
    (a - max a 0) ^ 2 ≤ (a - z) ^ 2 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha]
    have haz : a * z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha hz
    nlinarith [sq_nonneg z]
  · rw [max_eq_left ha]
    nlinarith [sq_nonneg (a - z)]

private theorem p26_frob_diagonal_projection_le (n : ℕ)
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : C.PosSemidef) :
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
    simpa [Matrix.sub_apply, Matrix.diagonal_apply] using
      p26_scalar_projection_sq_le (lambda i) (C i i) hC.diag_nonneg
  · have hz :
        (Matrix.diagonal lambda - Matrix.diagonal (fun i => max (lambda i) 0)) i j = 0 := by
      simp [Matrix.sub_apply, hij]
    rw [hz]
    simpa using sq_nonneg ((Matrix.diagonal lambda - C) i j)

private theorem p26_psd_congruence (n : ℕ)
    (B M : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.transpose = B) (hM : M.PosSemidef) :
    (B * M * B).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hB] using
    hM.conjTranspose_mul_mul_same B

private theorem p26_psd_orthogonal_congruence (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    (Q * M * Q.transpose).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hM.mul_mul_conjTranspose_same Q

private theorem p26_inverse_congruence (n : ℕ)
    (B C M : Matrix (Fin n) (Fin n) ℝ)
    (hBC : B * C = 1) (hCB : C * B = 1) :
    B * (C * M * C) * B = M := by
  calc
    B * (C * M * C) * B = (B * C) * M * (C * B) := by noncomm_ring
    _ = M := by rw [hBC, hCB]; simp

private theorem p26_orthogonal_inverse_congruence (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQQt : Q * Q.transpose = 1) :
    Q * (Q.transpose * M * Q) * Q.transpose = M := by
  calc
    Q * (Q.transpose * M * Q) * Q.transpose =
        (Q * Q.transpose) * M * (Q * Q.transpose) := by noncomm_ring
    _ = M := by rw [hQQt]; simp

private theorem p26_frob_orthogonal_congruence (n : ℕ)
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) (hQQt : Q * Q.transpose = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  rw [p26_frob_mul_orthogonal_right n Q (Q * M) hQtQ hQQt,
    p26_frob_mul_orthogonal_left n Q M hQtQ hQQt]

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
  dsimp only
  let P : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0)
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal lambda
  let N : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => max (lambda i) 0 - lambda i)
  let X : Matrix (Fin n) (Fin n) ℝ := p26WeightedPsdProjection Sinv Q lambda
  have hP : P.PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun i => le_max_right (lambda i) 0)
  have hN : N.PosSemidef := by
    exact Matrix.PosSemidef.diagonal
      (fun i => sub_nonneg.mpr (le_max_left (lambda i) 0))
  have hXdef : X = Sinv * (Q * P * Q.transpose) * Sinv := by
    rfl
  have hX : X.PosSemidef := by
    rw [hXdef]
    exact p26_psd_congruence n Sinv (Q * P * Q.transpose) hSinvSymm
      (p26_psd_orthogonal_congruence n Q P hP)
  have hA : A = Sinv * (Q * D * Q.transpose) * Sinv := by
    calc
      A = Sinv * (S * A * S) * Sinv :=
        (p26_inverse_congruence n Sinv S A hInvS hSInv).symm
      _ = Sinv * (Q * D * Q.transpose) * Sinv := by rw [hSpectral]
  have hND : N = P - D := by
    ext i j
    by_cases hij : i = j <;>
      simp [N, P, D, Matrix.sub_apply, hij]
  have hXA : X - A = Sinv * (Q * N * Q.transpose) * Sinv := by
    rw [hXdef, hA, hND]
    noncomm_ring
  have hXApsd : (X - A).PosSemidef := by
    rw [hXA]
    exact p26_psd_congruence n Sinv (Q * N * Q.transpose) hSinvSymm
      (p26_psd_orthogonal_congruence n Q N hN)
  have hSX : S * X * S = Q * P * Q.transpose := by
    rw [hXdef]
    exact p26_inverse_congruence n S Sinv (Q * P * Q.transpose) hSInv hInvS
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * (S * Z * S) * Q
    have hSZ : (S * Z * S).PosSemidef :=
      p26_psd_congruence n S Z hSsymm hZ
    have hC : C.PosSemidef := by
      dsimp [C]
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hSZ.conjTranspose_mul_mul_same Q
    have hCZ : Q * C * Q.transpose = S * Z * S := by
      exact p26_orthogonal_inverse_congruence n Q (S * Z * S) hQQt
    have hleft : S * (A - X) * S = Q * (D - P) * Q.transpose := by
      calc
        S * (A - X) * S = S * A * S - S * X * S := by noncomm_ring
        _ = Q * D * Q.transpose - Q * P * Q.transpose := by
          rw [hSpectral, hSX]
        _ = Q * (D - P) * Q.transpose := by noncomm_ring
    have hright : S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      calc
        S * (A - Z) * S = S * A * S - S * Z * S := by noncomm_ring
        _ = Q * D * Q.transpose - Q * C * Q.transpose := by
          rw [hSpectral, hCZ]
        _ = Q * (D - C) * Q.transpose := by noncomm_ring
    calc
      p26WeightedFrobeniusSq S (A - X) = p26FrobeniusSq (D - P) := by
        rw [p26WeightedFrobeniusSq, hleft]
        exact p26_frob_orthogonal_congruence n Q (D - P) hQtQ hQQt
      _ ≤ p26FrobeniusSq (D - C) :=
        p26_frob_diagonal_projection_le n lambda C hC
      _ = p26WeightedFrobeniusSq S (A - Z) := by
        rw [p26WeightedFrobeniusSq, hright]
        exact (p26_frob_orthogonal_congruence n Q (D - C) hQtQ hQQt).symm
  · intro i
    have hi : 0 ≤ (X - A) i i := hXApsd.diag_nonneg
    simpa [Matrix.sub_apply] using sub_nonneg.mp hi

end VSCLReuse

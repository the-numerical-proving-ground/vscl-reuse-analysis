import VSCLReuse.P26.Definitions

namespace VSCLReuse

private theorem p26_frob_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    p26FrobeniusSq M = Matrix.trace (M.transpose * M) := by
  simp only [p26FrobeniusSq, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  rw [Finset.sum_comm]

private theorem p26_frob_orthogonal {n : ℕ}
    (Q M : Matrix (Fin n) (Fin n) ℝ)
    (hQtQ : Q.transpose * Q = 1) :
    p26FrobeniusSq (Q * M * Q.transpose) = p26FrobeniusSq M := by
  rw [p26_frob_trace, p26_frob_trace]
  have h : (Q * M * Q.transpose).transpose * (Q * M * Q.transpose) =
      Q * (M.transpose * M) * Q.transpose := by
    calc
      _ = Q * (M.transpose * (Q.transpose * Q) * M) * Q.transpose := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = _ := by rw [hQtQ]; simp [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_cycle, hQtQ, Matrix.one_mul]

private theorem p26_psd_congr {n : ℕ}
    (T M : Matrix (Fin n) (Fin n) ℝ)
    (hT : T.transpose = T) (hM : M.PosSemidef) :
    (T * M * T).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hT] using
    hM.mul_mul_conjTranspose_same T

private theorem p26_scalar_best (a c : ℝ) (hc : 0 ≤ c) :
    (a - max a 0) ^ 2 ≤ (a - c) ^ 2 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha]
    nlinarith [sq_nonneg (a - c)]
  · have ha' : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    rw [max_eq_right ha']
    nlinarith [sq_nonneg c, mul_nonneg (neg_nonneg.mpr ha') hc]

private theorem p26_diagonal_best {n : ℕ}
    (lambda : Fin n → ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i, 0 ≤ C i i) :
    p26FrobeniusSq (Matrix.diagonal lambda -
      Matrix.diagonal (fun i => max (lambda i) 0)) ≤
    p26FrobeniusSq (Matrix.diagonal lambda - C) := by
  unfold p26FrobeniusSq
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa [Matrix.sub_apply, Matrix.diagonal_apply_eq] using
      p26_scalar_best (lambda i) (C i i) (hC i)
  · simp only [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij,
      zero_sub, neg_zero]
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
  let X : Matrix (Fin n) (Fin n) ℝ := p26WeightedPsdProjection Sinv Q lambda
  change X.PosSemidef ∧
    (∀ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef →
      p26WeightedFrobeniusSq S (A - X) ≤
        p26WeightedFrobeniusSq S (A - Z)) ∧
    ∀ i, A i i ≤ X i i
  have hDp : Dp.PosSemidef := by
    change (Matrix.diagonal (fun i => max (lambda i) 0)).PosSemidef
    apply Matrix.PosSemidef.diagonal
    intro i
    exact le_max_right _ _
  have hP : P.PosSemidef := by
    simpa [P, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hDp.mul_mul_conjTranspose_same Q
  have hXexpr : X = Sinv * P * Sinv := by
    rfl
  have hX : X.PosSemidef := by
    rw [hXexpr]
    exact p26_psd_congr Sinv P hSinvSymm hP
  have hSX : S * X * S = P := by
    calc
      S * X * S = (S * Sinv) * P * (Sinv * S) := by
        rw [hXexpr]
        simp only [Matrix.mul_assoc]
      _ = P := by rw [hSInv, hInvS]; simp
  have hAexpr : A = Sinv * (Q * D * Q.transpose) * Sinv := by
    calc
      A = (Sinv * S) * A * (S * Sinv) := by rw [hInvS, hSInv]; simp
      _ = Sinv * (S * A * S) * Sinv := by simp only [Matrix.mul_assoc]
      _ = Sinv * (Q * D * Q.transpose) * Sinv := by rw [hSpectral]
  have hDn : (Dp - D).PosSemidef := by
    change (Matrix.diagonal (fun i => max (lambda i) 0) -
      Matrix.diagonal lambda).PosSemidef
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact sub_nonneg.mpr (le_max_left _ _)
  have hDiff : (X - A).PosSemidef := by
    have hSpecDiff : (Q * (Dp - D) * Q.transpose).PosSemidef := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hDn.mul_mul_conjTranspose_same Q
    have hDiffEq : X - A = Sinv * (Q * (Dp - D) * Q.transpose) * Sinv := by
      rw [hXexpr, hAexpr]
      dsimp [P]
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    rw [hDiffEq]
    exact p26_psd_congr Sinv _ hSinvSymm hSpecDiff
  refine ⟨hX, ?_, ?_⟩
  · intro Z hZ
    let B : Matrix (Fin n) (Fin n) ℝ := S * Z * S
    let C : Matrix (Fin n) (Fin n) ℝ := Q.transpose * B * Q
    have hB : B.PosSemidef := by
      exact p26_psd_congr S Z hSsymm hZ
    have hC : C.PosSemidef := by
      simpa [C, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hB.mul_mul_conjTranspose_same Q.transpose
    have hBexpr : B = Q * C * Q.transpose := by
      calc
        B = (Q * Q.transpose) * B * (Q * Q.transpose) := by
          rw [hQQt]; simp
        _ = Q * C * Q.transpose := by
          dsimp [C]
          simp only [Matrix.mul_assoc]
    have hRX : S * (A - X) * S = Q * (D - Dp) * Q.transpose := by
      calc
        S * (A - X) * S = S * A * S - S * X * S := by
          simp only [Matrix.mul_sub, Matrix.sub_mul]
        _ = Q * (D - Dp) * Q.transpose := by
          rw [hSpectral, hSX]
          dsimp [P, D]
          simp only [Matrix.mul_sub, Matrix.sub_mul]
    have hRZ : S * (A - Z) * S = Q * (D - C) * Q.transpose := by
      calc
        S * (A - Z) * S = S * A * S - B := by
          dsimp [B]
          simp only [Matrix.mul_sub, Matrix.sub_mul]
        _ = Q * (D - C) * Q.transpose := by
          rw [hSpectral, hBexpr]
          dsimp [D]
          simp only [Matrix.mul_sub, Matrix.sub_mul]
    change p26FrobeniusSq (S * (A - X) * S) ≤
      p26FrobeniusSq (S * (A - Z) * S)
    rw [hRX, hRZ, p26_frob_orthogonal Q (D - Dp) hQtQ,
      p26_frob_orthogonal Q (D - C) hQtQ]
    exact p26_diagonal_best lambda C (fun i => hC.diag_nonneg)
  · intro i
    have h := hDiff.diag_nonneg (i := i)
    simpa [Matrix.sub_apply] using sub_nonneg.mp h

end VSCLReuse

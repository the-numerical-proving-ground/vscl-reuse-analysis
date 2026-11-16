import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private lemma p23_abs_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A + B) i j ≤ p23AbsMatrix A i j + p23AbsMatrix B i j := by
  exact nnnorm_add_le (A i j) (B i j)

private lemma p23_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A * B) i j ≤ (p23AbsMatrix A * p23AbsMatrix B) i j := by
  simp only [p23AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ l : Fin n, A i l * B l j‖₊ ≤ ∑ l : Fin n, ‖A i l * B l j‖₊ :=
      nnnorm_sum_le _ _
    _ = ∑ l : Fin n, ‖A i l‖₊ * ‖B l j‖₊ := by simp only [nnnorm_mul]

private lemma p23_mul_mono {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAC : ∀ i j, A i j ≤ C i j) (hBD : ∀ i j, B i j ≤ D i j) :
    ∀ i j, (A * B) i j ≤ (C * D) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun l _ => mul_le_mul' (hAC i l) (hBD l j)

private lemma p23_abs_pow_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAB : ∀ i j, p23AbsMatrix A i j ≤ B i j) :
    ∀ k i j, p23AbsMatrix (A ^ k) i j ≤ (B ^ k) i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [p23AbsMatrix, h]
  | succ k ih =>
      intro i j
      calc
        p23AbsMatrix (A ^ (k + 1)) i j = p23AbsMatrix (A ^ k * A) i j := by rw [pow_succ]
        _ ≤ (p23AbsMatrix (A ^ k) * p23AbsMatrix A) i j := p23_abs_mul_le _ _ _ _
        _ ≤ (B ^ k * B) i j := p23_mul_mono _ _ _ _ (ih) hAB i j
        _ = (B ^ (k + 1)) i j := by rw [pow_succ]

private lemma p23_strict_pow_apply_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ≥0)
    (hM : ∀ i j : Fin n, j.val ≤ i.val → M i j = 0) :
    ∀ r (i j : Fin n), j.val < i.val + r → (M ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j hji
      have hij : i ≠ j := by
        intro heq
        subst j
        omega
      simp [hij]
  | succ r ih =>
      intro i j hji
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + r
      · rw [ih i l hl, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rw [hM l j hjl, mul_zero]

private lemma p23_binomial_apply (n k : ℕ) (δ : ℝ≥0)
    (M : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    ((Matrix.diagonal (fun _ : Fin n => δ) + M) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (M ^ r) i j := by
  have hc : Commute M (Matrix.diagonal (fun _ : Fin n => δ)) :=
    (Matrix.scalar_commute δ (fun r => Commute.all δ r) M).symm
  rw [add_comm (Matrix.diagonal (fun _ : Fin n => δ)) M, hc.add_pow]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Matrix.diagonal_pow]
  change (M ^ r * Matrix.diagonal (fun _ : Fin n => δ ^ (k - r)) *
      Matrix.diagonal (fun _ : Fin n => (Nat.choose k r : ℝ≥0))) i j = _
  simp only [Matrix.mul_diagonal]
  ring

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  let M : Matrix (Fin n) (Fin n) ℝ≥0 := p23AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 :=
    Matrix.diagonal (fun _ : Fin n => δ) + M
  have hM : ∀ i j : Fin n, j.val ≤ i.val → M i j = 0 := by
    intro i j hij
    simp [M, p23AbsMatrix, hN i j hij]
  have hD' : ∀ i j : Fin n,
      p23AbsMatrix D i j ≤ (Matrix.diagonal (fun _ : Fin n => δ)) i j := by
    intro i j
    simpa [p23AbsMatrix, Matrix.diagonal_apply] using hD i j
  have hbase : ∀ i j : Fin n, p23AbsMatrix (D + N) i j ≤ S i j := by
    intro i j
    calc
      p23AbsMatrix (D + N) i j ≤ p23AbsMatrix D i j + M i j :=
        p23_abs_add_le D N i j
      _ ≤ (Matrix.diagonal (fun _ : Fin n => δ)) i j + M i j :=
        add_le_add (hD' i j) le_rfl
      _ = S i j := rfl
  intro i j
  calc
    p23AbsMatrix ((D + N) ^ k) i j ≤ (S ^ k) i j :=
      p23_abs_pow_le (D + N) S hbase k i j
    _ = ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (M ^ r) i j :=
      p23_binomial_apply n k δ M i j
    _ = p23PowerMajorant k δ N i j := by
      unfold p23PowerMajorant
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r < n
      · simp [h, M]
      · have hz : (M ^ r) i j = 0 := by
          apply p23_strict_pow_apply_zero M hM r i j
          have hj := j.isLt
          omega
        simp [h, hz, M]

end VSCLReuse

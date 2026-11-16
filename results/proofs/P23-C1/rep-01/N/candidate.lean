import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private lemma p23_abs_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    p23AbsMatrix (A * B) i j ≤
      (p23AbsMatrix A * p23AbsMatrix B) i j := by
  simp only [p23AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ l, A i l * B l j‖₊ ≤ ∑ l, ‖A i l * B l j‖₊ := nnnorm_sum_le _ _
    _ ≤ ∑ l, ‖A i l‖₊ * ‖B l j‖₊ :=
      Finset.sum_le_sum (fun l hl ↦ nnnorm_mul_le _ _)

private lemma p23_abs_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    p23AbsMatrix (A + B) i j ≤
      p23AbsMatrix A i j + p23AbsMatrix B i j := by
  exact nnnorm_add_le _ _

private lemma p23_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j)
    (i j : Fin n) : (A * B) i j ≤ (C * E) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum (fun l hl ↦ mul_le_mul' (hAC i l) (hBE l j))

private lemma p23_abs_pow_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (h : ∀ i j, p23AbsMatrix A i j ≤ B i j) (k : ℕ) :
    ∀ i j, p23AbsMatrix (A ^ k) i j ≤ (B ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    by_cases hij : i = j <;> simp [p23AbsMatrix, hij]
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ]
    exact (p23_abs_mul_le (A ^ k) A i j).trans (p23_mul_mono ih h i j)

private lemma p23_strict_pow_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0)
    (hA : ∀ i j, j.val ≤ i.val → A i j = 0) :
    ∀ r (i j : Fin n), j.val < i.val + r → (A ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
    intro i j hij
    have hne : i ≠ j := by
      intro he
      subst j
      omega
    simp [hne]
  | succ r ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hil : l.val < i.val + r
    · simp [ih i l hil]
    · have hlj : j.val ≤ l.val := by omega
      simp [hA l j hlj]

private lemma p23_binomial_term {n k r : ℕ} (δ : ℝ≥0)
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (i j : Fin n) :
    (B ^ r * (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ (k - r) *
      (Nat.choose k r : Matrix (Fin n) (Fin n) ℝ≥0)) i j =
      (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
  have hc : (Nat.choose k r : Matrix (Fin n) (Fin n) ℝ≥0) =
      (Nat.choose k r : ℝ≥0) • (1 : Matrix (Fin n) (Fin n) ℝ≥0) := by
    simp [Nat.cast_smul_eq_nsmul]
  rw [hc, smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, Matrix.mul_one]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

private lemma p23_power_majorant_eq {n : ℕ} (k : ℕ)
    (N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hN : p23StrictUpper N) (i j : Fin n) :
    ((p23AbsMatrix N + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j =
      p23PowerMajorant k δ N i j := by
  have hs : ∀ a b, b.val ≤ a.val → p23AbsMatrix N a b = 0 := by
    intro a b hab
    simp [p23AbsMatrix, hN a b hab]
  have hc : Commute (p23AbsMatrix N)
      (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) := by
    change p23AbsMatrix N * (δ • 1) = (δ • 1) * p23AbsMatrix N
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.smul_eq_mul_diagonal,
      ← Matrix.smul_eq_diagonal_mul]
  rw [hc.add_pow k]
  simp only [Matrix.sum_apply, p23PowerMajorant]
  apply Finset.sum_congr rfl
  intro r hr
  rw [p23_binomial_term]
  by_cases hrn : r < n
  · simp [hrn]
  · have hz : (p23AbsMatrix N ^ r) i j = 0 := by
      apply p23_strict_pow_zero (p23AbsMatrix N) hs r i j
      have hj := j.isLt
      omega
    simp [hrn, hz]

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  have hA : ∀ i j, p23AbsMatrix (D + N) i j ≤
      (p23AbsMatrix N + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) i j := by
    intro i j
    apply (p23_abs_add_le D N i j).trans
    simpa [p23AbsMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      add_comm] using (add_le_add_right (hD i j) ‖N i j‖₊)
  intro i j
  calc
    p23AbsMatrix ((D + N) ^ k) i j ≤
        ((p23AbsMatrix N + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j :=
      p23_abs_pow_le (D + N) _ hA k i j
    _ = p23PowerMajorant k δ N i j := p23_power_majorant_eq k N δ hN i j

end VSCLReuse

import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private lemma absMatrix_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    p23AbsMatrix (A + B) i j ≤ p23AbsMatrix A i j + p23AbsMatrix B i j := by
  simpa [p23AbsMatrix] using nnnorm_add_le (A i j) (B i j)

private lemma absMatrix_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    p23AbsMatrix (A * B) i j ≤ (p23AbsMatrix A * p23AbsMatrix B) i j := by
  simp only [p23AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ l, A i l * B l j‖₊ ≤ ∑ l, ‖A i l * B l j‖₊ := nnnorm_sum_le _ _
    _ = ∑ l, ‖A i l‖₊ * ‖B l j‖₊ := by simp

private lemma matrix_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAC : ∀ i j, A i j ≤ C i j) (hBE : ∀ i j, B i j ≤ E i j)
    (i j : Fin n) : (A * B) i j ≤ (C * E) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum (fun l _ ↦ mul_le_mul (hAC i l) (hBE l j)
    (zero_le _) (zero_le _))

private lemma absMatrix_pow_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (r : ℕ) :
    ∀ i j : Fin n, p23AbsMatrix (A ^ r) i j ≤ (p23AbsMatrix A ^ r) i j := by
  induction r with
  | zero =>
      intro i j
      by_cases h : i = j <;> simp [p23AbsMatrix, h]
  | succ r ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (absMatrix_mul_le (A ^ r) A i j).trans
        (matrix_mul_mono ih (fun i j ↦ le_refl _) i j)

private lemma strictUpper_pow_entry_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0)
    (hA : ∀ i j : Fin n, j.val ≤ i.val → A i j = 0) :
    ∀ r (i j : Fin n), j.val < i.val + r → (A ^ r) i j = 0 := by
  intro r
  induction r with
  | zero =>
      intro i j h
      have hij : i ≠ j := by
        intro e
        subst j
        omega
      simp [hij]
  | succ r ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l.val < i.val + r
      · simp [ih i l hl]
      · have hjl : j.val ≤ l.val := by omega
        simp [hA l j hjl]

private lemma absStrictUpper_pow_zero {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p23StrictUpper N)
    (r : ℕ) (hr : n ≤ r) (i j : Fin n) :
    (p23AbsMatrix N ^ r) i j = 0 := by
  apply strictUpper_pow_entry_zero (p23AbsMatrix N) (by
    intro a b h
    simp [p23AbsMatrix, hN a b h]) r i j
  omega

private lemma matrix_pow_mono {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAB : ∀ i j, A i j ≤ B i j) (r : ℕ) :
    ∀ i j, (A ^ r) i j ≤ (B ^ r) i j := by
  induction r with
  | zero => intro i j; exact le_refl _
  | succ r ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact matrix_mul_mono ih hAB i j

private lemma abs_sum_le_scalar {n : ℕ}
    (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0) :
    ∀ i j, p23AbsMatrix (D + N) i j ≤
      ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) + p23AbsMatrix N) i j := by
  intro i j
  calc
    p23AbsMatrix (D + N) i j ≤ p23AbsMatrix D i j + p23AbsMatrix N i j :=
      absMatrix_add_le D N i j
    _ ≤ ((δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) + p23AbsMatrix N) i j := by
      simpa [p23AbsMatrix, Matrix.smul_apply, Matrix.one_apply] using
        add_le_add_right (hD i j) (p23AbsMatrix N i j)

private lemma scalar_binomial_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0) (δ : ℝ≥0) (k : ℕ)
    (i j : Fin n) :
    ((A + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j := by
  have hc : Commute A (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) :=
    (Commute.one_right A).smul_right δ
  rw [hc.add_pow', Matrix.sum_apply,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => (k.choose a • (A ^ a * (δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ b)) i j) k]
  apply Finset.sum_congr rfl
  intro r hr
  rw [smul_pow, one_pow, mul_smul_one]
  change k.choose r • (δ ^ (k - r) • (A ^ r) i j) =
    (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j
  simp [nsmul_eq_mul, smul_eq_mul, mul_assoc]

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  intro i j
  let A := p23AbsMatrix N
  have hdom : ∀ a b : Fin n, p23AbsMatrix (D + N) a b ≤
      (A + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) a b := by
    intro a b
    simpa [A, Matrix.add_apply, add_comm] using abs_sum_le_scalar D N δ hD a b
  have hpow : p23AbsMatrix ((D + N) ^ k) i j ≤
      ((A + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j :=
    (absMatrix_pow_le (D + N) k i j).trans (matrix_pow_mono hdom k i j)
  calc
    p23AbsMatrix ((D + N) ^ k) i j ≤
        ((A + δ • (1 : Matrix (Fin n) (Fin n) ℝ≥0)) ^ k) i j := hpow
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j :=
      scalar_binomial_entry A δ k i j
    _ = p23PowerMajorant k δ N i j := by
      unfold p23PowerMajorant
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r < n
      · simp [h, A]
      · have hz : (A ^ r) i j = 0 := by
          exact absStrictUpper_pow_zero N hN r (by omega) i j
        simp [h, hz]

end VSCLReuse

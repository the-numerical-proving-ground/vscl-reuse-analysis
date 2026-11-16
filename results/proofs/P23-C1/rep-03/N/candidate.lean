import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private theorem p23_abs_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A + B) i j ≤
      p23AbsMatrix A i j + p23AbsMatrix B i j := by
  simpa [p23AbsMatrix] using nnnorm_add_le (A i j) (B i j)

private theorem p23_abs_mul_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A * B) i j ≤
      (p23AbsMatrix A * p23AbsMatrix B) i j := by
  simp only [p23AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ t : Fin n, A i t * B t j‖₊ ≤ ∑ t : Fin n, ‖A i t * B t j‖₊ :=
      nnnorm_sum_le _ _
    _ = ∑ t : Fin n, ‖A i t‖₊ * ‖B t j‖₊ := by simp

private theorem p23_matrix_mul_mono {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAB : ∀ i j, A i j ≤ B i j)
    (hCE : ∀ i j, C i j ≤ E i j) :
    ∀ i j, (A * C) i j ≤ (B * E) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun t _ => mul_le_mul (hAB i t) (hCE t j) (zero_le _) (zero_le _)

private theorem p23_abs_pow_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ∀ i j, p23AbsMatrix (A ^ k) i j ≤ (p23AbsMatrix A ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      by_cases hij : i = j
      · subst j; simp [p23AbsMatrix]
      · simp [p23AbsMatrix, hij]
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (p23_abs_mul_le (A ^ k) A i j).trans
        (p23_matrix_mul_mono ih (fun _ _ => le_refl _) i j)

private theorem p23_matrix_pow_mono {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) :
    ∀ i j, (A ^ k) i j ≤ (B ^ k) i j := by
  induction k with
  | zero => exact fun _ _ => le_refl _
  | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact p23_matrix_mul_mono ih hAB i j

private theorem p23_abs_upper_pow_zero {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℂ) (hN : p23StrictUpper N)
    (r : ℕ) (i j : Fin n) (h : j.val < i.val + r) :
    (p23AbsMatrix N ^ r) i j = 0 := by
  induction r generalizing i j with
  | zero =>
      simp only [Nat.add_zero] at h
      have hij : i ≠ j := by
        intro he
        subst j
        omega
      simp [hij]
  | succ r ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro t _
      by_cases ht : t.val < i.val + r
      · simp [ih i t ht]
      · have hjt : j.val ≤ t.val := by omega
        simp [p23AbsMatrix, hN t j hjt]

private theorem p23_binomial_term {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ≥0) (δ : ℝ≥0) (k r : ℕ)
    (i j : Fin n) :
    (A ^ r * (Matrix.scalar (Fin n) δ) ^ (k - r) *
        (↑(k.choose r) : Matrix (Fin n) (Fin n) ℝ≥0)) i j =
      (k.choose r : ℝ≥0) * δ ^ (k - r) * (A ^ r) i j := by
  have hcast : (↑(k.choose r) : Matrix (Fin n) (Fin n) ℝ≥0) =
      Matrix.scalar (Fin n) (k.choose r : ℝ≥0) := by
    ext a b
    simp [Matrix.natCast_apply]
  rw [hcast, ← map_pow (Matrix.scalar (Fin n)) δ (k - r)]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal]
  ac_rfl

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  let A : Matrix (Fin n) (Fin n) ℝ≥0 := p23AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := Matrix.scalar (Fin n) δ
  have hbase : ∀ i j, p23AbsMatrix (D + N) i j ≤ (S + A) i j := by
    intro i j
    calc
      p23AbsMatrix (D + N) i j ≤ p23AbsMatrix D i j + p23AbsMatrix N i j :=
        p23_abs_add_le D N i j
      _ ≤ (S + A) i j := by
        dsimp [S, A]
        exact add_le_add (by simpa [p23AbsMatrix, Matrix.scalar_apply] using hD i j)
          (le_refl _)
  have hcomm : Commute S A := Matrix.scalar_commute δ (fun _ => Commute.all _ _) A
  intro i j
  calc
    p23AbsMatrix ((D + N) ^ k) i j ≤ ((S + A) ^ k) i j :=
      (p23_abs_pow_le (D + N) k i j).trans (p23_matrix_pow_mono hbase k i j)
    _ = p23PowerMajorant k δ N i j := by
      have hbin := hcomm.symm.add_pow k
      rw [show S + A = A + S by exact add_comm S A, hbin]
      simp only [Matrix.sum_apply]
      unfold p23PowerMajorant
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrn : r < n
      · simp only [if_pos hrn]
        exact p23_binomial_term A δ k r i j
      · simp only [if_neg hrn]
        have hzero : (A ^ r) i j = 0 := by
          apply p23_abs_upper_pow_zero N hN r i j
          have hj := j.isLt
          omega
        rw [p23_binomial_term A δ k r i j, hzero]
        simp

end VSCLReuse

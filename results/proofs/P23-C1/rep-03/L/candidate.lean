import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private theorem p23_abs_mul_le {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A * C) i j ≤ (p23AbsMatrix A * p23AbsMatrix C) i j := by
  change ‖(A * C) i j‖₊ ≤ (p23AbsMatrix A * p23AbsMatrix C) i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    ‖∑ l, A i l * C l j‖₊ ≤ ∑ l, ‖A i l * C l j‖₊ := nnnorm_sum_le _ _
    _ = ∑ l, p23AbsMatrix A i l * p23AbsMatrix C l j := by
      simp [p23AbsMatrix, nnnorm_mul]

private theorem p23_mul_le {n : ℕ}
    {A B C E : Matrix (Fin n) (Fin n) ℝ≥0}
    (hAB : ∀ i j, A i j ≤ B i j) (hCE : ∀ i j, C i j ≤ E i j)
    (i j : Fin n) : (A * C) i j ≤ (B * E) i j := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_le_sum fun l _ =>
    mul_le_mul (hAB i l) (hCE l j) (zero_le _) (zero_le _)

private theorem p23_strictUpper_pow_eq_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hB : ∀ i j : Fin n, j.val ≤ i.val → B i j = 0) : B ^ n = 0 := by
  have hband : ∀ m : ℕ, ∀ i j : Fin n,
      j.val < i.val + m → (B ^ m) i j = 0 := by
    intro m
    induction m with
    | zero =>
      intro i j hji
      have hij : i ≠ j := by
        intro h
        subst j
        omega
      simpa using Matrix.one_apply_ne (α := ℝ≥0) hij
    | succ m ih =>
      intro i j hji
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < i.val + m
      · rw [ih i l hl, zero_mul]
      · have hjl : j.val ≤ l.val := by omega
        rw [hB l j hjl, mul_zero]
  apply Matrix.ext
  intro i j
  change (B ^ n) i j = 0
  apply hband n i j
  have := j.isLt
  omega

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  let B : Matrix (Fin n) (Fin n) ℝ≥0 := p23AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := Matrix.scalar (Fin n) δ
  have hentry : ∀ i j, p23AbsMatrix (D + N) i j ≤ (S + B) i j := by
    intro i j
    change ‖D i j + N i j‖₊ ≤ (S + B) i j
    calc
      ‖D i j + N i j‖₊ ≤ ‖D i j‖₊ + ‖N i j‖₊ := nnnorm_add_le _ _
      _ ≤ (if i = j then δ else 0) + ‖N i j‖₊ := add_le_add (hD i j) le_rfl
      _ = (S + B) i j := by
        simp [S, B, Matrix.scalar_apply, Matrix.diagonal_apply, p23AbsMatrix]
  have hpow : ∀ m : ℕ, ∀ i j,
      p23AbsMatrix ((D + N) ^ m) i j ≤ ((S + B) ^ m) i j := by
    intro m
    induction m with
    | zero =>
      intro i j
      by_cases hij : i = j
      · subst j; simp [p23AbsMatrix]
      · simp [p23AbsMatrix, hij]
    | succ m ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact (p23_abs_mul_le ((D + N) ^ m) (D + N) i j).trans
        (p23_mul_le ih hentry i j)
  have hcomm : Commute B S := by
    change B * S = S * B
    ext i j
    simp [S, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  have hbin : ∀ i j, ((S + B) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
    intro i j
    rw [add_comm S B, hcomm.add_pow]
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r hr
    have hscalar : (Nat.choose k r : Matrix (Fin n) (Fin n) ℝ≥0) =
        Matrix.scalar (Fin n) (Nat.choose k r : ℝ≥0) := by
      simp
    rw [hscalar, ← map_pow (Matrix.scalar (Fin n)) δ (k - r)]
    simp only [Matrix.scalar_apply, Matrix.mul_diagonal]
    ac_rfl
  have hstrict : ∀ i j : Fin n, j.val ≤ i.val → B i j = 0 := by
    intro i j hij
    simp [B, p23AbsMatrix, hN i j hij]
  have hzero : B ^ n = 0 := p23_strictUpper_pow_eq_zero B hstrict
  have hterm : ∀ r : ℕ, n ≤ r → B ^ r = 0 := by
    intro r hr
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [pow_add, hzero, zero_mul]
  intro i j
  calc
    p23AbsMatrix ((D + N) ^ k) i j ≤ ((S + B) ^ k) i j := hpow k i j
    _ = p23PowerMajorant k δ N i j := by
      rw [hbin]
      unfold p23PowerMajorant
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h : r < n
      · simp [h, B]
      · have hz := hterm r (Nat.le_of_not_gt h)
        simp [h, hz]

end VSCLReuse

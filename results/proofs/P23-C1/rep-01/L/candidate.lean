import VSCLReuse.P23.Definitions

namespace VSCLReuse

open scoped BigOperators NNReal

private lemma p23_abs_add {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A + B) i j ≤ p23AbsMatrix A i j + p23AbsMatrix B i j := by
  exact nnnorm_add_le (A i j) (B i j)

private lemma p23_abs_mul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    p23AbsMatrix (A * B) i j ≤ (p23AbsMatrix A * p23AbsMatrix B) i j := by
  simp only [p23AbsMatrix, Matrix.mul_apply]
  calc
    ‖∑ l, A i l * B l j‖₊ ≤ ∑ l, ‖A i l * B l j‖₊ := nnnorm_sum_le _ _
    _ = ∑ l, ‖A i l‖₊ * ‖B l j‖₊ := by simp only [nnnorm_mul]

private lemma p23_mul_mono {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAC : ∀ i j, A i j ≤ C i j) (hBD : ∀ i j, B i j ≤ D i j)
    (i j : Fin n) : (A * B) i j ≤ (C * D) i j := by
  simp only [Matrix.mul_apply]
  exact Finset.sum_le_sum fun l _ =>
    mul_le_mul (hAC i l) (hBD l j) (zero_le _) (zero_le _)

private lemma p23_abs_pow {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (i j : Fin n) :
    p23AbsMatrix (A ^ k) i j ≤ (p23AbsMatrix A ^ k) i j := by
  induction k generalizing i j with
  | zero =>
      by_cases h : i = j <;> simp [p23AbsMatrix, h]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      calc
        p23AbsMatrix (A ^ k * A) i j
            ≤ (p23AbsMatrix (A ^ k) * p23AbsMatrix A) i j := p23_abs_mul _ _ i j
        _ ≤ (p23AbsMatrix A ^ k * p23AbsMatrix A) i j :=
          p23_mul_mono _ _ _ _ (fun i j => ih i j) (fun i j => le_refl _) i j

private lemma p23_pow_mono {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) (i j : Fin n) :
    (A ^ k) i j ≤ (B ^ k) i j := by
  induction k generalizing i j with
  | zero => exact le_refl _
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact p23_mul_mono _ _ _ _ (fun i j => ih i j) hAB i j

private lemma p23_upper_pow_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0)
    (hB : ∀ i j : Fin n, j.val ≤ i.val → B i j = 0)
    (r : ℕ) (hr : n ≤ r) : B ^ r = 0 := by
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
        simp [hij]
    | succ m ih =>
        intro i j hji
        rw [pow_succ, Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hl : l.val < i.val + m
        · rw [ih i l hl, zero_mul]
        · have hjl : j.val ≤ l.val := by omega
          rw [hB l j hjl, mul_zero]
  apply Matrix.ext
  intro i j
  apply hband r i j
  have := j.isLt
  omega

private lemma p23_binomial_apply {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ≥0) (δ : ℝ≥0)
    (k : ℕ) (i j : Fin n) :
    ((Matrix.diagonal (fun _ : Fin n => δ) + B) ^ k) i j =
      ∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : ℝ≥0) * δ ^ (k - r) * (B ^ r) i j := by
  have hc : Commute B (Matrix.diagonal (fun _ : Fin n => δ)) := by
    have hs := Matrix.scalar_commute (n := Fin n) δ (fun x => mul_comm δ x) B
    simpa [Matrix.scalar_apply] using hs.symm
  rw [show Matrix.diagonal (fun _ : Fin n => δ) + B = B + Matrix.diagonal (fun _ => δ)
      by abel, hc.add_pow k]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_natCast (Nat.choose k r)]
  simp only [Matrix.mul_diagonal, Pi.pow_apply]
  ring

/-- P23-C1: the componentwise truncated-binomial bound of Lemma 2.1. -/
theorem p23_c1_truncated_binomial_power_bound
    (n k : ℕ) (D N : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ≥0)
    (hD : ∀ i j, ‖D i j‖₊ ≤ if i = j then δ else 0)
    (hN : p23StrictUpper N) :
    ∀ i j, p23AbsMatrix ((D + N) ^ k) i j ≤
      p23PowerMajorant k δ N i j := by
  -- PROOF_START P23-C1-H001
  let B : Matrix (Fin n) (Fin n) ℝ≥0 := p23AbsMatrix N
  let S : Matrix (Fin n) (Fin n) ℝ≥0 := Matrix.diagonal (fun _ => δ)
  have hmajor : ∀ i j, p23AbsMatrix (D + N) i j ≤ (S + B) i j := by
    intro i j
    calc
      p23AbsMatrix (D + N) i j
          ≤ p23AbsMatrix D i j + p23AbsMatrix N i j := p23_abs_add D N i j
      _ ≤ (if i = j then δ else 0) + p23AbsMatrix N i j :=
          by gcongr; exact hD i j
      _ = (S + B) i j := by simp [S, B, Matrix.diagonal_apply, p23AbsMatrix]
  have hupper : ∀ i j : Fin n, j.val ≤ i.val → B i j = 0 := by
    intro i j hij
    simp [B, p23AbsMatrix, hN i j hij]
  have htrunc : ∀ i j : Fin n, ((S + B) ^ k) i j = p23PowerMajorant k δ N i j := by
    intro i j
    rw [show S = Matrix.diagonal (fun _ : Fin n => δ) from rfl,
        p23_binomial_apply]
    simp only [p23PowerMajorant]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hn : r < n
    · simp [hn, B]
    · have hzero : B ^ r = 0 := p23_upper_pow_zero B hupper r (Nat.le_of_not_gt hn)
      simp [hn, hzero]
  intro i j
  calc
    p23AbsMatrix ((D + N) ^ k) i j
        ≤ (p23AbsMatrix (D + N) ^ k) i j := p23_abs_pow _ _ i j
    _ ≤ ((S + B) ^ k) i j := p23_pow_mono _ _ hmajor k i j
    _ = p23PowerMajorant k δ N i j := htrunc i j

end VSCLReuse

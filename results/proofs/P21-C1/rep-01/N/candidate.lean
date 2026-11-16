import VSCLReuse.P21.Definitions

namespace VSCLReuse

private theorem p21_matrix_refactor (n : ℕ) (x y b c : ℕ → ℝ)
    (hsum : ∀ i, i < n → x i + y i = b i + c i)
    (hprod : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p21UnitLowerBidiagonal n x * p21UnitLowerBidiagonal n y =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c := by
  have hlin : p21LowerShift n x + p21LowerShift n y =
      p21LowerShift n b + p21LowerShift n c := by
    ext i j
    by_cases h : i.val = j.val + 1
    · have hj : j.val < n := by omega
      simp [p21LowerShift, h, hsum j.val hj]
    · simp [p21LowerShift, h]
  have hquad : p21LowerShift n x * p21LowerShift n y =
      p21LowerShift n b * p21LowerShift n c := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hi : i.val = k.val + 1
    · by_cases hj : k.val = j.val + 1
      · have hjn : j.val + 1 < n := by omega
        simpa [p21LowerShift, hi, hj] using hprod j.val hjn
      · simp [p21LowerShift, hi, hj]
    · simp [p21LowerShift, hi]
  unfold p21UnitLowerBidiagonal
  calc
    (1 + p21LowerShift n x) * (1 + p21LowerShift n y) =
        1 + (p21LowerShift n x + p21LowerShift n y) +
          p21LowerShift n x * p21LowerShift n y := by noncomm_ring
    _ = 1 + (p21LowerShift n b + p21LowerShift n c) +
          p21LowerShift n b * p21LowerShift n c := by rw [hlin, hquad]
    _ = (1 + p21LowerShift n b) * (1 + p21LowerShift n c) := by noncomm_ring

/-- P21-C1: Lemma 4.1 and the structural guarantees of Algorithm 4.1. -/
theorem p21_c1_dqd2_refactorization
    (n q : ℕ) (b c : ℕ → ℝ)
    (hn : 0 < n) (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (hstop : q < n → b q = 0) :
    (∀ i, i < n → 0 ≤ p21DqdB q b c i) ∧
    (∀ i, i < n → 0 ≤ p21DqdC q b c i) ∧
    p21DqdB q b c 0 = 0 ∧
    p21UnitLowerBidiagonal n (p21DqdB q b c) *
        p21UnitLowerBidiagonal n (p21DqdC q b c) =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c ∧
    (∀ i, 0 < i → i < n →
      (p21DqdB q b c i = 0 ↔ b i = 0)) ∧
    (∀ i, i < n → p21DqdC q b c i = 0 → c i = 0) ∧
    (∀ i, i < n → c i = 0 → p21DqdC q b c i ≠ 0 → i + 1 = q) ∧
    (∀ i, q ≤ i →
      p21DqdB q b c i = b i ∧ p21DqdC q b c i = c i) ∧
    4 * q ≤ 4 * n := by
  -- PROOF_START P21-C1-H001
  let d := p21DqdD b c
  let x := p21DqdB q b c
  let y := p21DqdC q b c
  have hd_nonneg : ∀ i, i < q → 0 ≤ d i := by
    intro i
    induction i with
    | zero =>
        intro _
        change 0 ≤ b 0
        exact hb 0 (by omega)
    | succ i ih =>
        intro hi
        have hdi : 0 ≤ d i := ih (by omega)
        have hci : 0 ≤ c i := hc i (by omega)
        have hbi : 0 ≤ b (i + 1) := hb (i + 1) (by omega)
        change 0 ≤ b (i + 1) * d i / (c i + d i)
        positivity
  have hc_prev_pos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hbi : 0 < b (i + 1) := hbefore (i + 1) (by omega) hi
    rcases eq_or_lt_of_le (hc i (by omega)) with hci | hci
    · have hbi0 : b (i + 1) = 0 := hzero i (by omega) hci.symm
      linarith
    · exact hci
  have hden_pos : ∀ i, i + 1 < q → 0 < c i + d i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hc_prev_pos i hi) (hd_nonneg i (by omega))
  have hx_zero : x 0 = 0 := by
    rfl
  have hx_step : ∀ i, i + 1 < q →
      x (i + 1) = b (i + 1) * c i / (c i + d i) := by
    intro i hi
    simp [x, p21DqdB, hi, d]
  have hd_step : ∀ i, d (i + 1) = b (i + 1) * d i / (c i + d i) := by
    intro i
    rfl
  have hy_inner : ∀ i, i < q → y i = c i + d i := by
    intro i hi
    simp [y, p21DqdC, hi, d]
  have hx_tail : ∀ i, q ≤ i → x i = b i := by
    intro i hi
    cases i with
    | zero => omega
    | succ i =>
        simp [x, p21DqdB, show ¬ i + 1 < q by omega]
  have hy_tail : ∀ i, q ≤ i → y i = c i := by
    intro i hi
    simp [y, p21DqdC, show ¬ i < q by omega]
  have hsplit : ∀ i, i + 1 < q → x (i + 1) + d (i + 1) = b (i + 1) := by
    intro i hi
    rw [hx_step i hi, hd_step i]
    have hne : c i + d i ≠ 0 := ne_of_gt (hden_pos i hi)
    field_simp
  have hsum : ∀ i, i < n → x i + y i = b i + c i := by
    intro i hin
    cases i with
    | zero =>
        rw [hx_zero, hy_inner 0 hqpos]
        change 0 + (c 0 + b 0) = b 0 + c 0
        ring
    | succ i =>
        by_cases hi : i + 1 < q
        · rw [hy_inner (i + 1) hi]
          calc
            x (i + 1) + (c (i + 1) + d (i + 1)) =
                (x (i + 1) + d (i + 1)) + c (i + 1) := by ring
            _ = b (i + 1) + c (i + 1) := by rw [hsplit i hi]
        · have htail : q ≤ i + 1 := by omega
          rw [hx_tail (i + 1) htail, hy_tail (i + 1) htail]
  have hprod : ∀ i, i + 1 < n →
      x (i + 1) * y i = b (i + 1) * c i := by
    intro i hin
    by_cases hi : i + 1 < q
    · rw [hx_step i hi, hy_inner i (by omega)]
      have hne : c i + d i ≠ 0 := ne_of_gt (hden_pos i hi)
      field_simp
    · by_cases heq : i + 1 = q
      · have hb0 : b (i + 1) = 0 := by rw [heq]; exact hstop (by omega)
        rw [hx_tail (i + 1) (by omega), hb0]
        simp
      · have htail : q ≤ i := by omega
        rw [hx_tail (i + 1) (by omega), hy_tail i htail]
  have hx_nonneg : ∀ i, i < n → 0 ≤ x i := by
    intro i hin
    cases i with
    | zero => rw [hx_zero]
    | succ i =>
        by_cases hi : i + 1 < q
        · rw [hx_step i hi]
          exact div_nonneg (mul_nonneg (hb (i + 1) hin) (hc i (by omega)))
            (le_of_lt (hden_pos i hi))
        · rw [hx_tail (i + 1) (by omega)]
          exact hb (i + 1) hin
  have hy_nonneg : ∀ i, i < n → 0 ≤ y i := by
    intro i hin
    by_cases hi : i < q
    · rw [hy_inner i hi]
      exact add_nonneg (hc i hin) (hd_nonneg i hi)
    · rw [hy_tail i (by omega)]
      exact hc i hin
  have hx_zero_iff : ∀ i, 0 < i → i < n → (x i = 0 ↔ b i = 0) := by
    intro i hip hin
    by_cases hi : i < q
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hbpos : 0 < b (j + 1) := hbefore (j + 1) (by omega) hi
      have hxpos : 0 < x (j + 1) := by
        rw [hx_step j hi]
        exact div_pos (mul_pos hbpos (hc_prev_pos j hi)) (hden_pos j hi)
      constructor <;> intro hz <;> linarith
    · rw [hx_tail i (by omega)]
  have hy_zero_implies : ∀ i, i < n → y i = 0 → c i = 0 := by
    intro i hin hy0
    by_cases hi : i < q
    · rw [hy_inner i hi] at hy0
      have hci := hc i hin
      have hdi := hd_nonneg i hi
      linarith
    · simpa [hy_tail i (by omega)] using hy0
  have hy_new_zero : ∀ i, i < n → c i = 0 → y i ≠ 0 → i + 1 = q := by
    intro i hin hci hyne
    have hi : i < q := by
      by_contra h
      exact hyne ((hy_tail i (by omega)).trans hci)
    by_contra hne
    have hlt : i + 1 < q := by omega
    exact (ne_of_gt (hc_prev_pos i hlt)) hci
  refine ⟨hx_nonneg, hy_nonneg, hx_zero, ?_, hx_zero_iff,
    hy_zero_implies, hy_new_zero, ?_, by omega⟩
  · exact p21_matrix_refactor n x y b c hsum hprod
  · intro i hi
    exact ⟨hx_tail i hi, hy_tail i hi⟩

end VSCLReuse

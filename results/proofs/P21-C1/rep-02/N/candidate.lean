import VSCLReuse.P21.Definitions

namespace VSCLReuse

private theorem p21_product_eq_of_coeff (n : ℕ) (x y b c : ℕ → ℝ)
    (hs : ∀ i, i < n → x i + y i = b i + c i)
    (hp : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p21UnitLowerBidiagonal n x * p21UnitLowerBidiagonal n y =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c := by
  have hadd : p21LowerShift n x + p21LowerShift n y =
      p21LowerShift n b + p21LowerShift n c := by
    ext i j
    by_cases h : i.val = j.val + 1
    · have hj : j.val < n := by have := i.isLt; omega
      simp [p21LowerShift, h, hs j.val hj]
    · simp [p21LowerShift, h]
  have hmul : p21LowerShift n x * p21LowerShift n y =
      p21LowerShift n b * p21LowerShift n c := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i.val = k.val + 1
    · by_cases hkj : k.val = j.val + 1
      · have hj : j.val + 1 < n := by have := i.isLt; omega
        simp only [p21LowerShift, if_pos hik, if_pos hkj]
        rw [hkj]
        exact hp j.val hj
      · simp [p21LowerShift, hik, hkj]
    · simp [p21LowerShift, hik]
  simp only [p21UnitLowerBidiagonal]
  calc
    (1 + p21LowerShift n x) * (1 + p21LowerShift n y) =
        1 + (p21LowerShift n x + p21LowerShift n y) +
          p21LowerShift n x * p21LowerShift n y := by noncomm_ring
    _ = 1 + (p21LowerShift n b + p21LowerShift n c) +
          p21LowerShift n b * p21LowerShift n c := by rw [hadd, hmul]
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
  have hd : ∀ i, i < n → 0 ≤ p21DqdD b c i := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa [p21DqdD] using hb 0 hn
    | succ i ih =>
        intro hi
        rw [p21DqdD]
        exact div_nonneg (mul_nonneg (hb (i + 1) hi) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hin : i + 1 < n := by omega
    have hbpos : 0 < b (i + 1) := hbefore (i + 1) (by omega) hi
    have hne : c i ≠ 0 := by
      intro hci
      have := hzero i hin hci
      linarith
    rcases lt_or_eq_of_le (hc i (by omega)) with h | h
    · exact h
    · exact (hne h.symm).elim
  have hden : ∀ i, i + 1 < q → 0 < c i + p21DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hcpos i hi) (hd i (by omega))
  have hBstep : ∀ i, i + 1 < q →
      p21DqdB q b c (i + 1) =
        b (i + 1) * c i / (c i + p21DqdD b c i) := by
    intro i hi
    simp [p21DqdB, hi]
  have hCbefore : ∀ i, i < q →
      p21DqdC q b c i = c i + p21DqdD b c i := by
    intro i hi
    simp [p21DqdC, hi]
  have hBtail : ∀ i, q ≤ i → p21DqdB q b c i = b i := by
    intro i hi
    cases i with
    | zero => omega
    | succ i => simp [p21DqdB, show ¬ i + 1 < q by omega]
  have hCtail : ∀ i, q ≤ i → p21DqdC q b c i = c i := by
    intro i hi
    simp [p21DqdC, show ¬ i < q by omega]
  have hsplit : ∀ i, i + 1 < q →
      p21DqdB q b c (i + 1) + p21DqdD b c (i + 1) = b (i + 1) := by
    intro i hi
    rw [hBstep i hi, p21DqdD]
    have hnz : c i + p21DqdD b c i ≠ 0 := ne_of_gt (hden i hi)
    field_simp
  have hsum : ∀ i, i < n →
      p21DqdB q b c i + p21DqdC q b c i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        rw [hCbefore 0 hqpos]
        simp [p21DqdB, p21DqdD]
        ac_rfl
    | succ i =>
        by_cases hlt : i + 1 < q
        · rw [hCbefore (i + 1) hlt]
          have := hsplit i hlt
          linarith
        · rw [hBtail (i + 1) (by omega), hCtail (i + 1) (by omega)]
  have hprod : ∀ i, i + 1 < n →
      p21DqdB q b c (i + 1) * p21DqdC q b c i = b (i + 1) * c i := by
    intro i hi
    by_cases hlt : i + 1 < q
    · rw [hBstep i hlt, hCbefore i (by omega)]
      have hnz : c i + p21DqdD b c i ≠ 0 := ne_of_gt (hden i hlt)
      field_simp
    · by_cases heq : i + 1 = q
      · rw [hBtail (i + 1) (by omega), heq, hstop (by omega)]
        simp
      · rw [hBtail (i + 1) (by omega), hCtail i (by omega)]
  have hBnonneg : ∀ i, i < n → 0 ≤ p21DqdB q b c i := by
    intro i hi
    cases i with
    | zero => simp [p21DqdB]
    | succ i =>
        by_cases hlt : i + 1 < q
        · rw [hBstep i hlt]
          exact div_nonneg (mul_nonneg (hb (i + 1) hi) (hc i (by omega)))
            (le_of_lt (hden i hlt))
        · rw [hBtail (i + 1) (by omega)]
          exact hb (i + 1) hi
  have hCnonneg : ∀ i, i < n → 0 ≤ p21DqdC q b c i := by
    intro i hi
    by_cases hlt : i < q
    · rw [hCbefore i hlt]
      exact add_nonneg (hc i hi) (hd i hi)
    · rw [hCtail i (by omega)]
      exact hc i hi
  have hBzero : ∀ i, 0 < i → i < n →
      (p21DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hip hin
    by_cases hlt : i < q
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hbpos := hbefore (j + 1) (by omega) hlt
      have hpos : 0 < p21DqdB q b c (j + 1) := by
        rw [hBstep j hlt]
        exact div_pos (mul_pos hbpos (hcpos j hlt)) (hden j hlt)
      constructor <;> intro h <;> linarith
    · rw [hBtail i (by omega)]
  have hCzero : ∀ i, i < n → p21DqdC q b c i = 0 → c i = 0 := by
    intro i hin hci
    by_cases hlt : i < q
    · rw [hCbefore i hlt] at hci
      have := hc i hin
      have := hd i hin
      linarith
    · rwa [hCtail i (by omega)] at hci
  have hConly : ∀ i, i < n → c i = 0 →
      p21DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hcn
    have hlt : i < q := by
      by_contra h
      exact hcn ((hCtail i (by omega)).trans hci)
    by_contra hne
    have hlt' : i + 1 < q := by omega
    have := hcpos i hlt'
    linarith
  refine ⟨hBnonneg, hCnonneg, ?_, ?_, hBzero, hCzero, hConly, ?_, ?_⟩
  · simp [p21DqdB]
  · exact p21_product_eq_of_coeff n (p21DqdB q b c) (p21DqdC q b c) b c hsum hprod
  · intro i hi
    exact ⟨hBtail i hi, hCtail i hi⟩
  · omega

end VSCLReuse

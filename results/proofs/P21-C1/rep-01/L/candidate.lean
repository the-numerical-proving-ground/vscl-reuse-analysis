import VSCLReuse.P21.Definitions

namespace VSCLReuse

private theorem p21_matrix_product_of_coefficients
    (n : ℕ) (x y b c : ℕ → ℝ)
    (hsum : ∀ i, i < n → x i + y i = b i + c i)
    (hprod : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p21UnitLowerBidiagonal n x * p21UnitLowerBidiagonal n y =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c := by
  have hshift : p21LowerShift n x + p21LowerShift n y =
      p21LowerShift n b + p21LowerShift n c := by
    ext i j
    simp only [p21LowerShift, Matrix.add_apply]
    by_cases h : i.val = j.val + 1
    · simp only [if_pos h]
      have hj : j.val < n := by
        have hi := i.isLt
        omega
      exact hsum j.val hj
    · simp only [if_neg h]
  have hmul : p21LowerShift n x * p21LowerShift n y =
      p21LowerShift n b * p21LowerShift n c := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [p21LowerShift]
    by_cases h₁ : i.val = k.val + 1
    · by_cases h₂ : k.val = j.val + 1
      · simp only [if_pos h₁, if_pos h₂]
        have hj : j.val + 1 < n := by
          have hi := i.isLt
          omega
        simpa only [h₂] using hprod j.val hj
      · simp only [if_pos h₁, if_neg h₂, mul_zero]
    · simp only [if_neg h₁, zero_mul]
  simp only [p21UnitLowerBidiagonal]
  simp only [add_mul, mul_add, one_mul, mul_one]
  calc
    1 + p21LowerShift n x + (p21LowerShift n y + p21LowerShift n x * p21LowerShift n y) =
        1 + (p21LowerShift n x + p21LowerShift n y) +
          p21LowerShift n x * p21LowerShift n y := by abel
    _ = 1 + (p21LowerShift n b + p21LowerShift n c) +
          p21LowerShift n b * p21LowerShift n c := by rw [hshift, hmul]
    _ = 1 + p21LowerShift n b + (p21LowerShift n c + p21LowerShift n b * p21LowerShift n c) := by abel

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
  have hd_nonneg : ∀ i, i < n → 0 ≤ p21DqdD b c i := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa [p21DqdD] using hb 0 hi
    | succ i ih =>
        intro hi
        have hin : i < n := by omega
        rw [p21DqdD]
        apply div_nonneg
        · exact mul_nonneg (hb (i + 1) hi) (ih hin)
        · exact add_nonneg (hc i hin) (ih hin)
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hin : i + 1 < n := by omega
    have hci := hc i (by omega : i < n)
    have hbi := hbefore (i + 1) (by omega) hi
    by_contra h
    have hz : c i = 0 := by linarith
    have hbz := hzero i hin hz
    linarith
  have hdenpos : ∀ i, i + 1 < q → 0 < c i + p21DqdD b c i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hcpos i hi) (hd_nonneg i (by omega))
  have hden : ∀ i, i + 1 < q → c i + p21DqdD b c i ≠ 0 := by
    intro i hi
    exact ne_of_gt (hdenpos i hi)
  have htail : ∀ i, q ≤ i →
      p21DqdB q b c i = b i ∧ p21DqdC q b c i = c i := by
    intro i hi
    constructor
    · cases i with
      | zero => omega
      | succ j => simp [p21DqdB, show ¬ j + 1 < q by omega]
    · simp [p21DqdC, show ¬ i < q by omega]
  have hadd_step : ∀ i, i + 1 < q →
      p21DqdB q b c (i + 1) + p21DqdD b c (i + 1) = b (i + 1) := by
    intro i hi
    simp only [p21DqdB, if_pos hi, p21DqdD]
    field_simp [hden i hi]
  have hprod_step : ∀ i, i + 1 < q →
      p21DqdB q b c (i + 1) * p21DqdC q b c i = b (i + 1) * c i := by
    intro i hi
    have hiq : i < q := by omega
    simp only [p21DqdB, if_pos hi, p21DqdC, if_pos hiq]
    field_simp [hden i hi]
  have hsum : ∀ i, i < n →
      p21DqdB q b c i + p21DqdC q b c i = b i + c i := by
    intro i hin
    by_cases hiq : i < q
    · cases i with
      | zero =>
          simp only [p21DqdB, p21DqdC, if_pos hqpos, p21DqdD, zero_add]
          abel
      | succ j =>
          have hs := hadd_step j hiq
          simp only [p21DqdC, if_pos hiq]
          linarith
    · obtain ⟨hB, hC⟩ := htail i (by omega)
      rw [hB, hC]
  have hprod : ∀ i, i + 1 < n →
      p21DqdB q b c (i + 1) * p21DqdC q b c i = b (i + 1) * c i := by
    intro i hin
    by_cases hbeforeq : i + 1 < q
    · exact hprod_step i hbeforeq
    · by_cases htaili : q ≤ i
      · rw [(htail (i + 1) (by omega)).1, (htail i htaili).2]
      · have heq : i + 1 = q := by omega
        have hbz : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        rw [(htail (i + 1) (by omega)).1, hbz]
        simp
  have hBnonneg : ∀ i, i < n → 0 ≤ p21DqdB q b c i := by
    intro i hin
    cases i with
    | zero => simp [p21DqdB]
    | succ j =>
        by_cases hiq : j + 1 < q
        · simp only [p21DqdB, if_pos hiq]
          exact div_nonneg (mul_nonneg (hb (j + 1) hin) (hc j (by omega)))
            (le_of_lt (hdenpos j hiq))
        · rw [(htail (j + 1) (by omega)).1]
          exact hb (j + 1) hin
  have hCnonneg : ∀ i, i < n → 0 ≤ p21DqdC q b c i := by
    intro i hin
    by_cases hiq : i < q
    · simp only [p21DqdC, if_pos hiq]
      exact add_nonneg (hc i hin) (hd_nonneg i hin)
    · rw [(htail i (by omega)).2]
      exact hc i hin
  have hBzero : p21DqdB q b c 0 = 0 := by simp [p21DqdB]
  have hBpattern : ∀ i, 0 < i → i < n →
      (p21DqdB q b c i = 0 ↔ b i = 0) := by
    intro i hip hin
    by_cases hiq : i < q
    · have hbpos := hbefore i hip hiq
      have hBpos : 0 < p21DqdB q b c i := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        simp only [p21DqdB, if_pos hiq]
        exact div_pos (mul_pos hbpos (hcpos j hiq)) (hdenpos j hiq)
      constructor <;> intro h <;> linarith
    · rw [(htail i (by omega)).1]
  have hCzero : ∀ i, i < n → p21DqdC q b c i = 0 → c i = 0 := by
    intro i hin hz
    have hc' := hc i hin
    by_cases hiq : i < q
    · have hd' := hd_nonneg i hin
      simp only [p21DqdC, if_pos hiq] at hz
      linarith
    · rw [(htail i (by omega)).2] at hz
      exact hz
  have hCnew : ∀ i, i < n → c i = 0 → p21DqdC q b c i ≠ 0 → i + 1 = q := by
    intro i hin hci hci'
    by_cases hlt : i + 1 < q
    · have := hcpos i hlt
      linarith
    · by_cases hge : q ≤ i
      · rw [(htail i hge).2, hci] at hci'
        contradiction
      · omega
  refine ⟨hBnonneg, hCnonneg, hBzero, ?_, hBpattern, hCzero, hCnew, htail, ?_⟩
  · exact p21_matrix_product_of_coefficients n _ _ b c hsum hprod
  · omega

end VSCLReuse

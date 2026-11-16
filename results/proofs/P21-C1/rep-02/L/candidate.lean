import VSCLReuse.P21.Definitions

namespace VSCLReuse

private lemma p21LowerShift_add_eq (n : ℕ) (u v b c : ℕ → ℝ)
    (h : ∀ i, i < n → u i + v i = b i + c i) :
    p21LowerShift n u + p21LowerShift n v =
      p21LowerShift n b + p21LowerShift n c := by
  ext i j
  by_cases hij : i.val = j.val + 1
  · have hj : j.val < n := by have := i.isLt; omega
    simpa [p21LowerShift, hij] using h j.val hj
  · simp [p21LowerShift, hij]

private lemma p21LowerShift_mul_eq (n : ℕ) (u v b c : ℕ → ℝ)
    (h : ∀ i, i + 1 < n → u (i + 1) * v i = b (i + 1) * c i) :
    p21LowerShift n u * p21LowerShift n v =
      p21LowerShift n b * p21LowerShift n c := by
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · have hj : j.val + 1 < n := by have := i.isLt; omega
      simpa [p21LowerShift, hik, hkj] using h j.val hj
    · simp [p21LowerShift, hik, hkj]
  · simp [p21LowerShift, hik]

private lemma p21UnitLowerBidiagonal_mul_eq (n : ℕ) (u v b c : ℕ → ℝ)
    (hsum : ∀ i, i < n → u i + v i = b i + c i)
    (hprod : ∀ i, i + 1 < n → u (i + 1) * v i = b (i + 1) * c i) :
    p21UnitLowerBidiagonal n u * p21UnitLowerBidiagonal n v =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c := by
  simp only [p21UnitLowerBidiagonal]
  have hs := p21LowerShift_add_eq n u v b c hsum
  have hp := p21LowerShift_mul_eq n u v b c hprod
  calc
    (1 + p21LowerShift n u) * (1 + p21LowerShift n v) =
        1 + (p21LowerShift n u + p21LowerShift n v) +
          p21LowerShift n u * p21LowerShift n v := by noncomm_ring
    _ = 1 + (p21LowerShift n b + p21LowerShift n c) +
          p21LowerShift n b * p21LowerShift n c := by rw [hs, hp]
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
  let u := p21DqdB q b c
  let v := p21DqdC q b c
  have hd : ∀ i, i < n → 0 ≤ d i := by
    intro i
    induction i with
    | zero =>
        intro hi
        simpa [d, p21DqdD] using hb 0 hn
    | succ i ih =>
        intro hi
        rw [show d (i + 1) = b (i + 1) * d i / (c i + d i) by
          rfl]
        exact div_nonneg (mul_nonneg (hb (i + 1) hi) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    have hci := hc i (by omega)
    by_contra h
    have hcz : c i = 0 := le_antisymm (le_of_not_gt h) hci
    have hbz := hzero i (by omega) hcz
    have hbp := hbefore (i + 1) (by omega) hi
    linarith
  have hden : ∀ i, i + 1 < q → 0 < c i + d i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hcpos i hi) (hd i (by omega))
  have hsplit : ∀ i, i + 1 < q →
      b (i + 1) * c i / (c i + d i) + d (i + 1) = b (i + 1) := by
    intro i hi
    rw [show d (i + 1) = b (i + 1) * d i / (c i + d i) by rfl]
    have hne : c i + d i ≠ 0 := ne_of_gt (hden i hi)
    field_simp
  have hu0 : u 0 = 0 := by rfl
  have hafter : ∀ i, q ≤ i → u i = b i ∧ v i = c i := by
    intro i hi
    have hiz : i ≠ 0 := by omega
    cases i with
    | zero => contradiction
    | succ j =>
        constructor
        · simp [u, p21DqdB, not_lt.mpr hi]
        · simp [v, p21DqdC, not_lt.mpr hi]
  have hu_nonneg : ∀ i, i < n → 0 ≤ u i := by
    intro i hi
    cases i with
    | zero => simp [hu0]
    | succ j =>
        by_cases hjq : j + 1 < q
        · rw [show u (j + 1) = b (j + 1) * c j / (c j + d j) by
            simp [u, p21DqdB, d, hjq]]
          exact div_nonneg (mul_nonneg (hb (j + 1) hi) (hc j (by omega)))
            (le_of_lt (hden j hjq))
        · rw [(hafter (j + 1) (by omega)).1]
          exact hb (j + 1) hi
  have hv_nonneg : ∀ i, i < n → 0 ≤ v i := by
    intro i hi
    by_cases hiq : i < q
    · rw [show v i = c i + d i by simp [v, p21DqdC, d, hiq]]
      exact add_nonneg (hc i hi) (hd i hi)
    · rw [(hafter i (by omega)).2]
      exact hc i hi
  have hsum : ∀ i, i < n → u i + v i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        simp [u, v, p21DqdB, p21DqdC, p21DqdD, hqpos]
        ring
    | succ j =>
        by_cases hjq : j + 1 < q
        · have huv : u (j + 1) + v (j + 1) =
              b (j + 1) * c j / (c j + d j) + (c (j + 1) + d (j + 1)) := by
            simp [u, v, p21DqdB, p21DqdC, d, hjq]
          rw [huv, add_comm (c (j + 1)) (d (j + 1)), ← add_assoc,
            hsplit j hjq]
        · rcases hafter (j + 1) (by omega) with ⟨hu, hv⟩
          rw [hu, hv]
  have hprod : ∀ i, i + 1 < n → u (i + 1) * v i = b (i + 1) * c i := by
    intro i hi
    by_cases hiq : i + 1 < q
    · have hu : u (i + 1) = b (i + 1) * c i / (c i + d i) := by
        simp [u, p21DqdB, d, hiq]
      have hv : v i = c i + d i := by
        simp [v, p21DqdC, show i < q by omega, d]
      rw [hu, hv, div_mul_cancel₀ _ (ne_of_gt (hden i hiq))]
    · by_cases hiq' : i < q
      · have heq : i + 1 = q := by omega
        have hbq : b (i + 1) = 0 := by rw [heq]; exact hstop (by omega)
        rw [(hafter (i + 1) (by omega)).1, hbq]
        ring
      · rw [(hafter (i + 1) (by omega)).1, (hafter i (by omega)).2]
  have hzeroB : ∀ i, 0 < i → i < n → (u i = 0 ↔ b i = 0) := by
    intro i hip hin
    by_cases hiq : i < q
    · have hbip : 0 < b i := hbefore i hip hiq
      have hupi : 0 < u i := by
        cases i with
        | zero => omega
        | succ j =>
            rw [show u (j + 1) = b (j + 1) * c j / (c j + d j) by
              simp [u, p21DqdB, d, hiq]]
            exact div_pos (mul_pos hbip (hcpos j hiq)) (hden j hiq)
      constructor
      · intro h; exact False.elim ((ne_of_gt hupi) h)
      · intro h; exact False.elim ((ne_of_gt hbip) h)
    · rw [(hafter i (by omega)).1]
  have hzeroC : ∀ i, i < n → v i = 0 → c i = 0 := by
    intro i hi hvz
    by_cases hiq : i < q
    · rw [show v i = c i + d i by simp [v, p21DqdC, d, hiq]] at hvz
      have hci := hc i hi
      have hdi := hd i hi
      linarith
    · rw [(hafter i (by omega)).2] at hvz
      exact hvz
  have hchanged : ∀ i, i < n → c i = 0 → v i ≠ 0 → i + 1 = q := by
    intro i hi hci hvi
    by_contra hneq
    by_cases hqle : q ≤ i
    · exact hvi (by rw [(hafter i hqle).2, hci])
    · have hic : i + 1 < q := by omega
      have hcpi := hcpos i hic
      linarith
  refine ⟨hu_nonneg, hv_nonneg, hu0,
    p21UnitLowerBidiagonal_mul_eq n u v b c hsum hprod,
    hzeroB, hzeroC, hchanged, hafter, ?_⟩
  omega

end VSCLReuse

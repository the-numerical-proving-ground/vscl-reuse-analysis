import VSCLReuse.P21.Definitions

namespace VSCLReuse

private theorem p21_matrix_product_of_entries
    (n : ℕ) (x y b c : ℕ → ℝ)
    (hs : ∀ i, i < n → x i + y i = b i + c i)
    (hp : ∀ i, i + 1 < n → x (i + 1) * y i = b (i + 1) * c i) :
    p21UnitLowerBidiagonal n x * p21UnitLowerBidiagonal n y =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c := by
  have hsum : p21LowerShift n x + p21LowerShift n y =
      p21LowerShift n b + p21LowerShift n c := by
    ext i j
    by_cases h : i.val = j.val + 1
    · have hj : j.val < n := by omega
      simpa [p21LowerShift, h] using hs j.val hj
    · simp [p21LowerShift, h]
  have hmul : p21LowerShift n x * p21LowerShift n y =
      p21LowerShift n b * p21LowerShift n c := by
    ext i j
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hik : i.val = k.val + 1
    · by_cases hkj : k.val = j.val + 1
      · have hj : j.val + 1 < n := by omega
        simpa [p21LowerShift, hik, hkj] using hp j.val hj
      · simp [p21LowerShift, hik, hkj]
    · simp [p21LowerShift, hik]
  dsimp [p21UnitLowerBidiagonal]
  calc
    (1 + p21LowerShift n x) * (1 + p21LowerShift n y) =
        1 + (p21LowerShift n x + p21LowerShift n y) +
          p21LowerShift n x * p21LowerShift n y := by
            simp only [add_mul, mul_add, one_mul, mul_one]
            abel
    _ = 1 + (p21LowerShift n b + p21LowerShift n c) +
          p21LowerShift n b * p21LowerShift n c := by rw [hsum, hmul]
    _ = (1 + p21LowerShift n b) * (1 + p21LowerShift n c) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          abel

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
  have hd : ∀ i, i < q → 0 ≤ d i := by
    intro i
    induction i with
    | zero =>
        intro _
        exact hb 0 (by omega)
    | succ i ih =>
        intro hi
        change 0 ≤ b (i + 1) * d i / (c i + d i)
        exact div_nonneg
          (mul_nonneg (hb (i + 1) (by omega)) (ih (by omega)))
          (add_nonneg (hc i (by omega)) (ih (by omega)))
  have hcpos : ∀ i, i + 1 < q → 0 < c i := by
    intro i hi
    rcases eq_or_lt_of_le (hc i (by omega)) with h | h
    · have hbpos := hbefore (i + 1) (by omega) hi
      have hbzero := hzero i (by omega) h.symm
      exact False.elim ((ne_of_gt hbpos) hbzero)
    · exact h
  have hden : ∀ i, i + 1 < q → 0 < c i + d i := by
    intro i hi
    exact add_pos_of_pos_of_nonneg (hcpos i hi) (hd i (by omega))
  have htail : ∀ i, q ≤ i → x i = b i ∧ y i = c i := by
    intro i hi
    constructor
    · cases i with
      | zero => omega
      | succ k =>
          change (if k + 1 < q then
            b (k + 1) * c k / (c k + d k) else b (k + 1)) = b (k + 1)
          simp [show ¬ k + 1 < q by omega]
    · change (if i < q then c i + d i else c i) = c i
      simp [show ¬ i < q by omega]
  have hx0 : x 0 = 0 := rfl
  have hxstep : ∀ i, i + 1 < q →
      x (i + 1) = b (i + 1) * c i / (c i + d i) := by
    intro i hi
    change (if i + 1 < q then
      b (i + 1) * c i / (c i + d i) else b (i + 1)) = _
    simp [hi]
  have hystep : ∀ i, i < q → y i = c i + d i := by
    intro i hi
    change (if i < q then c i + d i else c i) = _
    simp [hi]
  have hdstep : ∀ i, d (i + 1) =
      b (i + 1) * d i / (c i + d i) := by
    intro i
    rfl
  have hy0 : y 0 = c 0 + b 0 := by
    rw [hystep 0 hqpos]
    rfl
  have hxnonneg : ∀ i, i < n → 0 ≤ x i := by
    intro i hi
    cases i with
    | zero => simp [hx0]
    | succ k =>
        by_cases hk : k + 1 < q
        · rw [hxstep k hk]
          exact div_nonneg
            (mul_nonneg (hb (k + 1) hi) (hc k (by omega)))
            (le_of_lt (hden k hk))
        · exact (htail (k + 1) (by omega)).1 ▸ hb (k + 1) hi
  have hynonneg : ∀ i, i < n → 0 ≤ y i := by
    intro i hi
    by_cases hiq : i < q
    · rw [hystep i hiq]
      exact add_nonneg (hc i hi) (hd i hiq)
    · exact (htail i (by omega)).2 ▸ hc i hi
  have hsum : ∀ i, i < n → x i + y i = b i + c i := by
    intro i hi
    cases i with
    | zero =>
        rw [hx0, hy0]
        abel
    | succ k =>
        by_cases hk : k + 1 < q
        · have hne : c k + d k ≠ 0 := ne_of_gt (hden k hk)
          rw [hxstep k hk, hystep (k + 1) hk, hdstep k]
          field_simp
          ring
        · have hx := (htail (k + 1) (by omega)).1
          by_cases heq : k + 1 = q
          · have hbk : b (k + 1) = 0 := by
              rw [heq]
              exact hstop (by omega)
            have hy : y (k + 1) = c (k + 1) :=
              (htail (k + 1) (by omega)).2
            rw [hx, hy]
          · have hy : y (k + 1) = c (k + 1) :=
              (htail (k + 1) (by omega)).2
            rw [hx, hy]
  have hprod : ∀ i, i + 1 < n →
      x (i + 1) * y i = b (i + 1) * c i := by
    intro i hi
    by_cases hnext : i + 1 < q
    · have hne : c i + d i ≠ 0 := ne_of_gt (hden i hnext)
      have hprev : i < q := by omega
      rw [hxstep i hnext, hystep i hprev]
      field_simp
    · have hx := (htail (i + 1) (by omega)).1
      by_cases heq : i + 1 = q
      · have hbk : b (i + 1) = 0 := by
          rw [heq]
          exact hstop (by omega)
        rw [hx, hbk]
        simp
      · have hy := (htail i (by omega)).2
        rw [hx, hy]
  have hmat := p21_matrix_product_of_entries n x y b c hsum hprod
  have hxzero : ∀ i, 0 < i → i < n → (x i = 0 ↔ b i = 0) := by
    intro i hip hin
    by_cases hiq : i < q
    · have hbpos := hbefore i hip hiq
      have hxpos : 0 < x i := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [hxstep k hiq]
        exact div_pos (mul_pos hbpos (hcpos k hiq)) (hden k hiq)
      constructor
      · intro he; exact False.elim ((ne_of_gt hxpos) he)
      · intro he; exact False.elim ((ne_of_gt hbpos) he)
    · rw [(htail i (by omega)).1]
  have hyzero : ∀ i, i < n → y i = 0 → c i = 0 := by
    intro i hin he
    by_cases hiq : i < q
    · rw [hystep i hiq] at he
      have hci := hc i hin
      have hdi := hd i hiq
      linarith
    · rw [(htail i (by omega)).2] at he
      exact he
  have hnewzero : ∀ i, i < n → c i = 0 → y i ≠ 0 → i + 1 = q := by
    intro i hin hci hyne
    by_contra hneq
    have hiq : i < q := by
      by_contra h
      exact hyne ((htail i (by omega)).2.trans hci)
    have hnext : i + 1 < q := by omega
    exact (ne_of_gt (hcpos i hnext)) hci
  refine ⟨hxnonneg, hynonneg, hx0, hmat, hxzero, hyzero,
    hnewzero, htail, ?_⟩
  omega

end VSCLReuse

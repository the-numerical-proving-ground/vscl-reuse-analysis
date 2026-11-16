import VSCLReuse.P21.Definitions

namespace VSCLReuse

private theorem p21_d_nonneg (n : ℕ) (b c : ℕ → ℝ)
    (hb : ∀ i, i < n → 0 ≤ b i) (hc : ∀ i, i < n → 0 ≤ c i) :
    ∀ i, i < n → 0 ≤ p21DqdD b c i := by
  intro i
  induction i with
  | zero =>
      intro hi
      simpa [p21DqdD] using hb 0 hi
  | succ i ih =>
      intro hi
      have hip : i < n := by omega
      rw [p21DqdD]
      exact div_nonneg (mul_nonneg (hb (i + 1) hi) (ih hip))
        (add_nonneg (hc i hip) (ih hip))

private theorem p21_c_pos_before (n q : ℕ) (b c : ℕ → ℝ)
    (hqn : q ≤ n) (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (i : ℕ) (hi : i + 1 < q) : 0 < c i := by
  have hin : i < n := by omega
  have hnext : i + 1 < n := by omega
  have hne : c i ≠ 0 := by
    intro hz
    have hbpos := hbefore (i + 1) (by omega) hi
    have hbzero := hzero i hnext hz
    linarith
  exact lt_of_le_of_ne (hc i hin) (Ne.symm hne)

private theorem p21_after (q : ℕ) (b c : ℕ → ℝ) (hqpos : 0 < q) (i : ℕ)
    (hi : q ≤ i) :
    p21DqdB q b c i = b i ∧ p21DqdC q b c i = c i := by
  constructor
  · cases i with
    | zero => omega
    | succ k =>
        simp [p21DqdB, show ¬ k + 1 < q by omega]
  · simp [p21DqdC, show ¬ i < q by omega]

private theorem p21_b_zero (q : ℕ) (b c : ℕ → ℝ) :
    p21DqdB q b c 0 = 0 := by
  rfl

private theorem p21_b_nonneg (n q : ℕ) (b c : ℕ → ℝ)
    (hb : ∀ i, i < n → 0 ≤ b i) (hc : ∀ i, i < n → 0 ≤ c i) :
    ∀ i, i < n → 0 ≤ p21DqdB q b c i := by
  intro i hi
  cases i with
  | zero => simp [p21DqdB]
  | succ k =>
      by_cases hq : k + 1 < q
      · simp only [p21DqdB, if_pos hq]
        apply div_nonneg
        · exact mul_nonneg (hb (k + 1) hi) (hc k (by omega))
        · exact add_nonneg (hc k (by omega))
            (p21_d_nonneg n b c hb hc k (by omega))
      · simpa [p21DqdB, hq] using hb (k + 1) hi

private theorem p21_c_nonneg (n q : ℕ) (b c : ℕ → ℝ)
    (hb : ∀ i, i < n → 0 ≤ b i) (hc : ∀ i, i < n → 0 ≤ c i) :
    ∀ i, i < n → 0 ≤ p21DqdC q b c i := by
  intro i hi
  by_cases hq : i < q
  · simpa [p21DqdC, hq] using
      add_nonneg (hc i hi) (p21_d_nonneg n b c hb hc i hi)
  · simpa [p21DqdC, hq] using hc i hi

private theorem p21_before_sum (n q : ℕ) (b c : ℕ → ℝ)
    (hqn : q ≤ n) (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (i : ℕ) (hi : i + 1 < q) :
    p21DqdB q b c (i + 1) + p21DqdC q b c (i + 1) =
      b (i + 1) + c (i + 1) := by
  have hden : c i + p21DqdD b c i ≠ 0 := by
    have hcpos := p21_c_pos_before n q b c hqn hc hbefore hzero i hi
    have hdnon := p21_d_nonneg n b c hb hc i (by omega)
    positivity
  simp only [p21DqdB, if_pos hi, p21DqdC, p21DqdD]
  field_simp
  ring

private theorem p21_before_product (n q : ℕ) (b c : ℕ → ℝ)
    (hqn : q ≤ n) (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (i : ℕ) (hi : i + 1 < q) :
    p21DqdB q b c (i + 1) * p21DqdC q b c i =
      b (i + 1) * c i := by
  have hden : c i + p21DqdD b c i ≠ 0 := by
    have hcpos := p21_c_pos_before n q b c hqn hc hbefore hzero i hi
    have hdnon := p21_d_nonneg n b c hb hc i (by omega)
    positivity
  have hi' : i < q := by omega
  simp only [p21DqdB, if_pos hi, p21DqdC, if_pos hi']
  field_simp

private theorem p21_scalar_sum (n q : ℕ) (b c : ℕ → ℝ)
    (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0) :
    ∀ i, i < n →
      p21DqdB q b c i + p21DqdC q b c i = b i + c i := by
  intro i hi
  cases i with
  | zero => simp [p21DqdB, p21DqdC, p21DqdD, hqpos, add_comm]
  | succ i =>
      by_cases hlt : i + 1 < q
      · exact p21_before_sum n q b c hqn hb hc hbefore hzero i hlt
      · obtain ⟨hb', hc'⟩ := p21_after q b c hqpos (i + 1) (by omega)
        rw [hb', hc']

private theorem p21_scalar_product (n q : ℕ) (b c : ℕ → ℝ)
    (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (hstop : q < n → b q = 0) :
    ∀ i, i + 1 < n →
      p21DqdB q b c (i + 1) * p21DqdC q b c i =
        b (i + 1) * c i := by
  intro i hi
  by_cases hlt : i + 1 < q
  · exact p21_before_product n q b c hqn hb hc hbefore hzero i hlt
  · by_cases heq : i + 1 = q
    · have hbz : b (i + 1) = 0 := by rw [heq]; exact hstop (by omega)
      obtain ⟨hb', _⟩ := p21_after q b c hqpos (i + 1) (by omega)
      rw [hb', hbz]
      simp
    · have hqi : q ≤ i := by omega
      obtain ⟨hb', _⟩ := p21_after q b c hqpos (i + 1) (by omega)
      obtain ⟨_, hc'⟩ := p21_after q b c hqpos i hqi
      rw [hb', hc']

private theorem p21_shift_add (n : ℕ) (x y u v : ℕ → ℝ)
    (hsum : ∀ i, i < n → x i + y i = u i + v i) :
    p21LowerShift n x + p21LowerShift n y =
      p21LowerShift n u + p21LowerShift n v := by
  ext i j
  change (if i.val = j.val + 1 then x j.val else 0) +
      (if i.val = j.val + 1 then y j.val else 0) =
      (if i.val = j.val + 1 then u j.val else 0) +
      (if i.val = j.val + 1 then v j.val else 0)
  by_cases hij : i.val = j.val + 1
  · have hj : j.val < n := by have := i.isLt; omega
    simp [hij, hsum j.val hj]
  · simp [hij]

private theorem p21_shift_mul (n : ℕ) (x y u v : ℕ → ℝ)
    (hprod : ∀ i, i + 1 < n → x (i + 1) * y i = u (i + 1) * v i) :
    p21LowerShift n x * p21LowerShift n y =
      p21LowerShift n u * p21LowerShift n v := by
  ext i j
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  change (if i.val = k.val + 1 then x k.val else 0) *
      (if k.val = j.val + 1 then y j.val else 0) =
      (if i.val = k.val + 1 then u k.val else 0) *
      (if k.val = j.val + 1 then v j.val else 0)
  by_cases hik : i.val = k.val + 1
  · by_cases hkj : k.val = j.val + 1
    · have hj : j.val + 1 < n := by have := i.isLt; omega
      simpa [hik, hkj] using hprod j.val hj
    · simp [hkj]
  · simp [hik]

private theorem p21_matrix_refactor (n : ℕ) (x y u v : ℕ → ℝ)
    (hsum : ∀ i, i < n → x i + y i = u i + v i)
    (hprod : ∀ i, i + 1 < n → x (i + 1) * y i = u (i + 1) * v i) :
    p21UnitLowerBidiagonal n x * p21UnitLowerBidiagonal n y =
      p21UnitLowerBidiagonal n u * p21UnitLowerBidiagonal n v := by
  let X := p21LowerShift n x
  let Y := p21LowerShift n y
  let U := p21LowerShift n u
  let V := p21LowerShift n v
  have hadd : X + Y = U + V := p21_shift_add n x y u v hsum
  have hmul : X * Y = U * V := p21_shift_mul n x y u v hprod
  change (1 + X) * (1 + Y) = (1 + U) * (1 + V)
  simp only [add_mul, mul_add, one_mul, mul_one]
  calc
    1 + X + (Y + X * Y) = 1 + (X + Y) + X * Y := by abel
    _ = 1 + (U + V) + U * V := by rw [hadd, hmul]
    _ = 1 + U + (V + U * V) := by abel

private theorem p21_b_zero_iff (n q : ℕ) (b c : ℕ → ℝ)
    (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0) :
    ∀ i, 0 < i → i < n → (p21DqdB q b c i = 0 ↔ b i = 0) := by
  intro i hip hin
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  by_cases hlt : k + 1 < q
  · have hbpos := hbefore (k + 1) (by omega) hlt
    have hcpos := p21_c_pos_before n q b c hqn hc hbefore hzero k hlt
    have hdnon := p21_d_nonneg n b c hb hc k (by omega)
    have hdenpos : 0 < c k + p21DqdD b c k := by positivity
    have hb'pos : 0 < p21DqdB q b c (k + 1) := by
      simp only [p21DqdB, if_pos hlt]
      exact div_pos (mul_pos hbpos hcpos) hdenpos
    constructor <;> intro hz <;> linarith
  · rw [(p21_after q b c hqpos (k + 1) (by omega)).1]

private theorem p21_c_zero_implies (n q : ℕ) (b c : ℕ → ℝ)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i) :
    ∀ i, i < n → p21DqdC q b c i = 0 → c i = 0 := by
  intro i hin hz
  by_cases hlt : i < q
  · have hsum : c i + p21DqdD b c i = 0 := by
      simpa [p21DqdC, hlt] using hz
    have hci := hc i hin
    have hdi := p21_d_nonneg n b c hb hc i hin
    linarith
  · simpa [p21DqdC, hlt] using hz

private theorem p21_c_new_zero_location (n q : ℕ) (b c : ℕ → ℝ)
    (hqpos : 0 < q) (hqn : q ≤ n)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0) :
    ∀ i, i < n → c i = 0 → p21DqdC q b c i ≠ 0 → i + 1 = q := by
  intro i hin hci hnew
  have hlt : i < q := by
    by_contra hnot
    have hafter := (p21_after q b c hqpos i (by omega)).2
    exact hnew (hafter.trans hci)
  by_contra hneq
  have hnext : i + 1 < q := by omega
  have hbpos := hbefore (i + 1) (by omega) hnext
  have hbzero := hzero i (by omega) hci
  linarith

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
  refine ⟨p21_b_nonneg n q b c hb hc,
    p21_c_nonneg n q b c hb hc,
    p21_b_zero q b c,
    p21_matrix_refactor n (p21DqdB q b c) (p21DqdC q b c) b c
      (p21_scalar_sum n q b c hqpos hqn hb hc hbefore hzero)
      (p21_scalar_product n q b c hqpos hqn hb hc hbefore hzero hstop),
    p21_b_zero_iff n q b c hqpos hqn hb hc hbefore hzero,
    p21_c_zero_implies n q b c hb hc,
    p21_c_new_zero_location n q b c hqpos hqn hbefore hzero,
    p21_after q b c hqpos,
    Nat.mul_le_mul_left 4 hqn⟩

end VSCLReuse

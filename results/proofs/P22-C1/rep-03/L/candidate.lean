import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p22_diag_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (h : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22DiagSquare L i := by
  unfold p22DiagSquare
  exact pow_pos (h i) 2

private lemma p22_row_ge_diag {n : ℕ} (L : Fin n → Fin n → ℝ)
    (i : Fin n) : p22DiagSquare L i ≤ p22RowEnergy L i := by
  unfold p22RowEnergy
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun k hk => sq_nonneg _)

private lemma p22_row_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (h : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22RowEnergy L i :=
  lt_of_lt_of_le (p22_diag_pos L h i) (p22_row_ge_diag L i)

private lemma p22_row_eq_iff {n : ℕ} (L : Fin n → Fin n → ℝ)
    (i : Fin n) :
    p22RowEnergy L i = p22DiagSquare L i ↔
      ∀ k, k.val < i.val → L i k = 0 := by
  classical
  constructor
  · intro heq k hk
    have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
        (L i j) ^ 2) = 0 := by
      unfold p22RowEnergy at heq
      linarith
    have hmem : k ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    have hle : (L i k) ^ 2 ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (L i j) ^ 2 := by
      exact Finset.single_le_sum (fun j hj => sq_nonneg _) hmem
    nlinarith [sq_nonneg (L i k)]
  · intro hzero
    unfold p22RowEnergy
    have : (∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
        (L i k) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
      simp [hzero k hki]
    rw [this, add_zero]

private lemma p22_measure_basic {n : ℕ} (L : Fin n → Fin n → ℝ)
    (h : ∀ i, 0 < L i i) :
    p22HadamardMeasure L ≤ 1 ∧
      (p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L) := by
  classical
  let a := ∏ i, p22DiagSquare L i
  let b := ∏ i, p22RowEnergy L i
  have ha : 0 < a := Finset.prod_pos fun i hi => p22_diag_pos L h i
  have hb : 0 < b := Finset.prod_pos fun i hi => p22_row_pos L h i
  have hab : a ≤ b := Finset.prod_le_prod
    (fun i hi => (p22_diag_pos L h i).le)
    (fun i hi => p22_row_ge_diag L i)
  have hmeas : p22HadamardMeasure L = a / b := rfl
  constructor
  · rw [hmeas]
    exact (div_le_iff₀ hb).2 (by nlinarith)
  · rw [hmeas]
    constructor
    · intro heq i k hk
      have habEq : a = b := by
        apply (div_eq_one_iff_eq hb.ne').mp at heq
        exact heq
      by_contra hne
      have hsq : 0 < (L i k) ^ 2 := sq_pos_of_ne_zero hne
      have hrow : p22DiagSquare L i < p22RowEnergy L i := by
        unfold p22RowEnergy
        have hmem : k ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        have hle : (L i k) ^ 2 ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (L i j) ^ 2 :=
          Finset.single_le_sum (fun j hj => sq_nonneg _) hmem
        linarith
      have hprod : a < b := Finset.prod_lt_prod
        (fun j hj => p22_diag_pos L h j)
        (fun j hj => p22_row_ge_diag L j)
        ⟨i, Finset.mem_univ _, hrow⟩
      exact (ne_of_lt hprod) habEq
    · intro hdiag
      have heq : a = b := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (p22_row_eq_iff L i).2 (hdiag i) |>.symm
      rw [heq, div_self hb.ne']

private lemma p22_measure_scale {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (hs : ∀ i, s i ≠ 0) :
    p22HadamardMeasure (p22ScaleRows s L) = p22HadamardMeasure L := by
  classical
  have hdiag (i : Fin n) :
      p22DiagSquare (p22ScaleRows s L) i =
        (s i) ^ 2 * p22DiagSquare L i := by
    unfold p22DiagSquare p22ScaleRows
    ring
  have hrow (i : Fin n) :
      p22RowEnergy (p22ScaleRows s L) i =
        (s i) ^ 2 * p22RowEnergy L i := by
    unfold p22RowEnergy p22DiagSquare p22ScaleRows
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    ring
  have hscale : (∏ i : Fin n, (s i) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hs i)
  unfold p22HadamardMeasure
  simp_rw [hdiag, hrow, Finset.prod_mul_distrib]
  exact mul_div_mul_left _ _ hscale

private lemma p22_tail_prod_le_exp {n : ℕ} (x : Fin n → ℝ)
    (hpos : ∀ i, 0 < x i) (hsum : ∑ i, x i ≤ (n + 1 : ℝ)) :
    ∏ i, x i ≤ Real.exp 1 := by
  have hpoint (i : Fin n) : x i ≤ Real.exp (x i - 1) := by
    have h := Real.add_one_le_exp (x i - 1)
    linarith
  have hprod : (∏ i, x i) ≤ ∏ i, Real.exp (x i - 1) :=
    Finset.prod_le_prod (fun i hi => (hpos i).le) (fun i hi => hpoint i)
  have hshift : (∑ i, (x i - 1)) ≤ (1 : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul, mul_one]
    linarith
  calc
    (∏ i, x i) ≤ ∏ i, Real.exp (x i - 1) := hprod
    _ = Real.exp (∑ i, (x i - 1)) := by rw [Real.exp_sum]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hshift

/-- P22-C1: all five Hadamard-measure conclusions of Proposition 6.2. -/
theorem p22_c1_hadamard_measure_jacobi_growth
    (n M : ℕ) (L : Fin n → Fin n → ℝ) (s : Fin n → ℝ)
    (detH : ℝ) (diagProduct measure jacobiEntry : ℕ → ℝ)
    (lambdaMin lambdaMax : ℕ → ℝ)
    (tailEigen : ℕ → Fin n → ℝ) (kappa : ℕ → ℝ)
    (hn : 0 < n)
    (hLdiag : ∀ i, 0 < L i i)
    (hs : ∀ i, s i ≠ 0)
    (hdetH : detH = ∏ i, p22DiagSquare L i)
    (hdiag0 : diagProduct 0 = ∏ i, p22RowEnergy L i)
    (hdiagPos : ∀ m, m ≤ M → 0 < diagProduct m)
    (hmeasure : ∀ m, m ≤ M → measure m = detH / diagProduct m)
    (hjacobi : ∀ m, m < M →
      diagProduct (m + 1) =
        (1 - (jacobiEntry m) ^ 2) * diagProduct m)
    (hjacobiSmall : ∀ m, m < M → (jacobiEntry m) ^ 2 < 1)
    (hlambdaMinPos : ∀ m, m ≤ M → 0 < lambdaMin m)
    (htailPos : ∀ m, m ≤ M → ∀ i, 0 < tailEigen m i)
    (htailSum : ∀ m, m ≤ M →
      ∑ i, tailEigen m i ≤ (n + 1 : ℝ))
    (hmeasureEigen : ∀ m, m ≤ M →
      measure m = lambdaMin m * ∏ i, tailEigen m i)
    (hlambdaMax : ∀ m, m ≤ M → lambdaMax m ≤ (n + 1 : ℝ))
    (hkappa : ∀ m, m ≤ M → kappa m = lambdaMax m / lambdaMin m) :
    p22HadamardMeasure L ≤ 1 ∧
    (p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L) ∧
    p22HadamardMeasure (p22ScaleRows s L) = p22HadamardMeasure L ∧
    (∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m) ∧
    (∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1)) ∧
    (∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p22HadamardMeasure L) := by
  -- PROOF_START P22-C1-H001
  classical
  have hbasic := p22_measure_basic L hLdiag
  have hscale := p22_measure_scale L s hs
  have hdetPos : 0 < detH := by
    rw [hdetH]
    exact Finset.prod_pos (fun i hi => p22_diag_pos L hLdiag i)
  have hbasePos : 0 < p22HadamardMeasure L := by
    unfold p22HadamardMeasure
    apply div_pos
    · exact Finset.prod_pos (fun i hi => p22_diag_pos L hLdiag i)
    · exact Finset.prod_pos (fun i hi => p22_row_pos L hLdiag i)
  have hmeasure0 : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hmeasurePos (m : ℕ) (hm : m ≤ M) : 0 < measure m := by
    rw [hmeasure m hm]
    exact div_pos hdetPos (hdiagPos m hm)
  have hminBound (m : ℕ) (hm : m ≤ M) :
      measure m / Real.exp 1 ≤ lambdaMin m := by
    have htail := p22_tail_prod_le_exp (tailEigen m)
      (htailPos m hm) (htailSum m hm)
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    rw [hmeasureEigen m hm]
    exact mul_le_mul_of_nonneg_left htail (hlambdaMinPos m hm).le
  have hstep (m : ℕ) (hm : m < M) :
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    have hm1 : m + 1 ≤ M := Nat.succ_le_of_lt hm
    have hfpos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hf_le : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m (le_of_lt hm), hjacobi m hm]
      field_simp
    constructor
    · exact heq
    · rw [heq]
      apply (le_div_iff₀ hfpos).2
      calc
        measure m * (1 - (jacobiEntry m) ^ 2) ≤ measure m * 1 :=
          mul_le_mul_of_nonneg_left hf_le (hmeasurePos m (le_of_lt hm)).le
        _ = measure m := by ring
  have hmon : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m
    induction m with
    | zero => intro hm; exact le_rfl
    | succ m ih =>
        intro hm
        exact (ih (Nat.le_of_succ_le hm)).trans
          (hstep m (Nat.lt_of_succ_le hm)).2
  refine ⟨hbasic.1, hbasic.2, hscale, hminBound, hstep, ?_⟩
  intro m hm
  have hbaseMin : p22HadamardMeasure L ≤ lambdaMin m * Real.exp 1 := by
    calc
      p22HadamardMeasure L = measure 0 := hmeasure0.symm
      _ ≤ measure m := hmon m hm
      _ ≤ lambdaMin m * Real.exp 1 :=
        (div_le_iff₀ (Real.exp_pos 1)).mp (hminBound m hm)
  rw [hkappa m hm]
  apply (div_le_div_iff₀ (hlambdaMinPos m hm) hbasePos).2
  calc
    lambdaMax m * p22HadamardMeasure L ≤
        (n + 1 : ℝ) * p22HadamardMeasure L :=
      mul_le_mul_of_nonneg_right (hlambdaMax m hm) hbasePos.le
    _ ≤ (n + 1 : ℝ) * (lambdaMin m * Real.exp 1) :=
      mul_le_mul_of_nonneg_left hbaseMin (by positivity)
    _ = (n + 1 : ℝ) * Real.exp 1 * lambdaMin m := by ring

end VSCLReuse

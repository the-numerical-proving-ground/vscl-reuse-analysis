import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p22_diag_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22DiagSquare L i := by
  unfold p22DiagSquare
  exact sq_pos_of_pos (hLdiag i)

private theorem p22_row_ge_diag {n : ℕ} (L : Fin n → Fin n → ℝ)
    (i : Fin n) : p22DiagSquare L i ≤ p22RowEnergy L i := by
  unfold p22RowEnergy
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => sq_nonneg (L i k)))

private theorem p22_row_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22RowEnergy L i :=
  lt_of_lt_of_le (p22_diag_pos L hLdiag i) (p22_row_ge_diag L i)

private theorem p22_row_eq_diag_iff {n : ℕ} (L : Fin n → Fin n → ℝ)
    (i : Fin n) :
    p22RowEnergy L i = p22DiagSquare L i ↔
      ∀ k, k.val < i.val → L i k = 0 := by
  constructor
  · intro h k hk
    have hsum :
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), (L i j) ^ 2) = 0 := by
      unfold p22RowEnergy at h
      linarith
    have hmem : k ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    have hle : (L i k) ^ 2 ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), (L i j) ^ 2 := by
      exact Finset.single_le_sum (fun j hj => sq_nonneg (L i j)) hmem
    nlinarith [sq_nonneg (L i k)]
  · intro h
    unfold p22RowEnergy
    have hsum :
        (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val), (L i k) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
      simp [h k hki]
    rw [hsum, add_zero]

private theorem p22_measure_le_one {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) : p22HadamardMeasure L ≤ 1 := by
  have hprod : (∏ i, p22DiagSquare L i) ≤ ∏ i, p22RowEnergy L i := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (p22_diag_pos L hLdiag i).le
    · intro i hi
      exact p22_row_ge_diag L i
  have hrow : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos (fun i hi => p22_row_pos L hLdiag i)
  unfold p22HadamardMeasure
  exact (div_le_iff₀ hrow).2 (by simpa using hprod)

private theorem p22_measure_eq_one_iff {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) :
    p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L := by
  have hrow : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos (fun i hi => p22_row_pos L hLdiag i)
  constructor
  · intro h i k hk
    have hprod : (∏ j, p22DiagSquare L j) = ∏ j, p22RowEnergy L j := by
      have h' := h
      unfold p22HadamardMeasure at h'
      simpa using (div_eq_iff hrow.ne').mp h'
    have hroweq : p22RowEnergy L i = p22DiagSquare L i := by
      apply le_antisymm
      · by_contra hnot
        have hne : p22DiagSquare L i ≠ p22RowEnergy L i := by
          intro heq
          exact hnot heq.ge
        have hlt : p22DiagSquare L i < p22RowEnergy L i :=
          lt_of_le_of_ne (p22_row_ge_diag L i) hne
        have hprodlt : (∏ j, p22DiagSquare L j) < ∏ j, p22RowEnergy L j := by
          apply Finset.prod_lt_prod
          · intro j hj
            exact p22_diag_pos L hLdiag j
          · intro j hj
            exact p22_row_ge_diag L j
          · exact ⟨i, Finset.mem_univ i, hlt⟩
        exact (ne_of_lt hprodlt) hprod
      · exact p22_row_ge_diag L i
    exact (p22_row_eq_diag_iff L i).mp hroweq k hk
  · intro h
    have hprod : (∏ i, p22DiagSquare L i) = ∏ i, p22RowEnergy L i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ((p22_row_eq_diag_iff L i).mpr (fun k hk => h i k hk)).symm
    unfold p22HadamardMeasure
    rw [hprod]
    exact div_self hrow.ne'

private theorem p22_scaled_diag {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) :
    p22DiagSquare (p22ScaleRows s L) i = (s i) ^ 2 * p22DiagSquare L i := by
  simp only [p22DiagSquare, p22ScaleRows, mul_pow]

private theorem p22_scaled_row {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) :
    p22RowEnergy (p22ScaleRows s L) i = (s i) ^ 2 * p22RowEnergy L i := by
  simp only [p22RowEnergy, p22_scaled_diag, p22ScaleRows, mul_pow]
  rw [← Finset.mul_sum]
  ring

private theorem p22_measure_scale {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (hs : ∀ i, s i ≠ 0) :
    p22HadamardMeasure (p22ScaleRows s L) = p22HadamardMeasure L := by
  have hsprod : (∏ i : Fin n, (s i) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero 2 (hs i)
  have hnum : (∏ i, p22DiagSquare (p22ScaleRows s L) i) =
      (∏ i, (s i) ^ 2) * ∏ i, p22DiagSquare L i := by
    simp_rw [p22_scaled_diag]
    exact Finset.prod_mul_distrib
  have hden : (∏ i, p22RowEnergy (p22ScaleRows s L) i) =
      (∏ i, (s i) ^ 2) * ∏ i, p22RowEnergy L i := by
    simp_rw [p22_scaled_row]
    exact Finset.prod_mul_distrib
  unfold p22HadamardMeasure
  rw [hnum, hden]
  exact mul_div_mul_left _ _ hsprod

private theorem p22_tail_prod_le_exp {n : ℕ} (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i, z i ≤ (n + 1 : ℝ)) :
    (∏ i, z i) ≤ Real.exp 1 := by
  have hsum_sub : (∑ i : Fin n, (z i - 1)) ≤ (1 : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    linarith
  calc
    (∏ i, z i) ≤ ∏ i, Real.exp (z i - 1) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hz i
      · intro i hi
        have h := Real.add_one_le_exp (z i - 1)
        linarith
    _ = Real.exp (∑ i, (z i - 1)) := by rw [Real.exp_sum]
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum_sub

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
  have hdetPos : 0 < detH := by
    rw [hdetH]
    exact Finset.prod_pos (fun i hi => p22_diag_pos L hLdiag i)
  have hmeasure0 : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hhadPos : 0 < p22HadamardMeasure L := by
    rw [← hmeasure0, hmeasure 0 (Nat.zero_le M)]
    exact div_pos hdetPos (hdiagPos 0 (Nat.zero_le M))
  have hmeasurePos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetPos (hdiagPos m hm)
  have heigenBound : ∀ m, m ≤ M → measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    have hprod : (∏ i, tailEigen m i) ≤ Real.exp 1 :=
      p22_tail_prod_le_exp (tailEigen m)
        (fun i => (htailPos m hm i).le) (htailSum m hm)
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    rw [hmeasureEigen m hm]
    exact mul_le_mul_of_nonneg_left hprod (hlambdaMinPos m hm).le
  have hstep : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := Nat.succ_le_of_lt hm
    have hfacPos : 0 < 1 - (jacobiEntry m) ^ 2 := sub_pos.mpr (hjacobiSmall m hm)
    have hfacLe : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      calc
        measure (m + 1) = detH / ((1 - (jacobiEntry m) ^ 2) * diagProduct m) := by
          rw [hmeasure (m + 1) hm1, hjacobi m hm]
        _ = (detH / diagProduct m) / (1 - (jacobiEntry m) ^ 2) := by
          field_simp [(hdiagPos m (Nat.le_of_lt hm)).ne', hfacPos.ne']
        _ = measure m / (1 - (jacobiEntry m) ^ 2) := by
          rw [hmeasure m (Nat.le_of_lt hm)]
    refine ⟨heq, ?_⟩
    rw [heq]
    apply (le_div_iff₀ hfacPos).2
    simpa using mul_le_mul_of_nonneg_left hfacLe
      (hmeasurePos m (Nat.le_of_lt hm)).le
  have hmono : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hlt : m < M := Nat.lt_of_succ_le hm
      exact (ih (Nat.le_of_lt hlt)).trans ((hstep m hlt).2)
  refine ⟨p22_measure_le_one L hLdiag,
    p22_measure_eq_one_iff L hLdiag,
    p22_measure_scale L s hs,
    heigenBound, hstep, ?_⟩
  intro m hm
  have hhadLe : p22HadamardMeasure L ≤ Real.exp 1 * lambdaMin m := by
    have heig := (div_le_iff₀ (Real.exp_pos 1)).mp (heigenBound m hm)
    calc
      p22HadamardMeasure L = measure 0 := hmeasure0.symm
      _ ≤ measure m := hmono m hm
      _ ≤ Real.exp 1 * lambdaMin m := by simpa [mul_comm] using heig
  rw [hkappa m hm]
  apply (div_le_div_iff₀ (hlambdaMinPos m hm) hhadPos).2
  calc
    lambdaMax m * p22HadamardMeasure L ≤
        (n + 1 : ℝ) * p22HadamardMeasure L :=
      mul_le_mul_of_nonneg_right (hlambdaMax m hm) hhadPos.le
    _ ≤ (n + 1 : ℝ) * (Real.exp 1 * lambdaMin m) :=
      mul_le_mul_of_nonneg_left hhadLe (by positivity)
    _ = ((n + 1 : ℝ) * Real.exp 1) * lambdaMin m := by ring

end VSCLReuse

import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

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
  have hSqPos : ∀ i, 0 < p22DiagSquare L i := by
    intro i
    exact sq_pos_of_pos (hLdiag i)
  have hrowNonneg : ∀ i,
      0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val), (L i k) ^ 2 := by
    intro i
    exact Finset.sum_nonneg (fun k _ ↦ sq_nonneg (L i k))
  have hrowPos : ∀ i, 0 < p22RowEnergy L i := by
    intro i
    unfold p22RowEnergy
    exact lt_of_lt_of_le (hSqPos i) (le_add_of_nonneg_right (hrowNonneg i))
  have hrowLe : ∀ i, p22DiagSquare L i ≤ p22RowEnergy L i := by
    intro i
    unfold p22RowEnergy
    exact le_add_of_nonneg_right (hrowNonneg i)
  have hDpos : 0 < ∏ i, p22DiagSquare L i :=
    Finset.prod_pos (fun i _ ↦ hSqPos i)
  have hEpos : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos (fun i _ ↦ hrowPos i)
  have hHpos : 0 < p22HadamardMeasure L := by
    unfold p22HadamardMeasure
    exact div_pos hDpos hEpos
  have hHadLe : p22HadamardMeasure L ≤ 1 := by
    unfold p22HadamardMeasure
    apply (div_le_iff₀ hEpos).2
    simpa using (Finset.prod_le_prod
      (s := Finset.univ) (f := fun i ↦ p22DiagSquare L i)
      (g := fun i ↦ p22RowEnergy L i)
      (fun i _ ↦ (hSqPos i).le) (fun i _ ↦ hrowLe i))
  have hHadEq : p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L := by
    constructor
    · intro h i k hk
      have hprodEq : (∏ j, p22DiagSquare L j) = ∏ j, p22RowEnergy L j := by
        have hh := h
        unfold p22HadamardMeasure at hh
        exact (div_eq_one_iff_eq hEpos.ne').mp hh
      by_contra hne
      have hkpos : 0 < (L i k) ^ 2 := sq_pos_of_ne_zero hne
      have hmem : k ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
      have hsingle : (L i k) ^ 2 ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (L i j) ^ 2 :=
        Finset.single_le_sum (fun j _ ↦ sq_nonneg (L i j)) hmem
      have hstrict : p22DiagSquare L i < p22RowEnergy L i := by
        unfold p22RowEnergy
        linarith
      have hprodLt : (∏ j, p22DiagSquare L j) < ∏ j, p22RowEnergy L j :=
        Finset.prod_lt_prod (fun j _ ↦ hSqPos j) (fun j _ ↦ hrowLe j)
          ⟨i, Finset.mem_univ i, hstrict⟩
      exact (ne_of_lt hprodLt) hprodEq
    · intro hd
      have hrows : ∀ i, p22RowEnergy L i = p22DiagSquare L i := by
        intro i
        unfold p22RowEnergy
        have hzero :
            (∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (L i k) ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
          simp [hd i k hki]
        simpa only [Fin.lt_def, add_zero] using congrArg
          (fun x : ℝ ↦ p22DiagSquare L i + x) hzero
      unfold p22HadamardMeasure
      simp_rw [hrows]
      exact div_self hDpos.ne'
  have hScaleDiag : ∀ i, p22DiagSquare (p22ScaleRows s L) i =
      (s i) ^ 2 * p22DiagSquare L i := by
    intro i
    unfold p22DiagSquare p22ScaleRows
    ring
  have hScaleRow : ∀ i, p22RowEnergy (p22ScaleRows s L) i =
      (s i) ^ 2 * p22RowEnergy L i := by
    intro i
    unfold p22RowEnergy p22DiagSquare p22ScaleRows
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k hk
      ring
  have hScale : p22HadamardMeasure (p22ScaleRows s L) =
      p22HadamardMeasure L := by
    have hsprod : (∏ i, (s i) ^ 2) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact pow_ne_zero 2 (hs i)
    unfold p22HadamardMeasure
    simp_rw [hScaleDiag, hScaleRow, Finset.prod_mul_distrib]
    field_simp
  have hzero : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hTailBound : ∀ m, m ≤ M → (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hsum : (∑ i, (tailEigen m i - 1)) ≤ 1 := by
      have hh : (∑ i, (tailEigen m i - 1)) = (∑ i, tailEigen m i) - (n : ℝ) := by
        simp [Finset.sum_sub_distrib]
      rw [hh]
      linarith [htailSum m hm]
    calc
      (∏ i, tailEigen m i)
          ≤ ∏ i, Real.exp (tailEigen m i - 1) := by
              apply Finset.prod_le_prod
              · intro i hi
                exact (htailPos m hm i).le
              · intro i hi
                have hh := Real.add_one_le_exp (tailEigen m i - 1)
                linarith
      _ = Real.exp (∑ i, (tailEigen m i - 1)) := by
            rw [← Real.exp_sum]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
  have hMinBound : ∀ m, m ≤ M → measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    rw [hmeasureEigen m hm]
    exact mul_le_mul_of_nonneg_left (hTailBound m hm) (hlambdaMinPos m hm).le
  have hJacobiStep : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := Nat.succ_le_of_lt hm
    have hfactorPos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hfactorLe : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    have hmeasurePos : 0 < measure m := by
      rw [hmeasure m (Nat.le_of_lt hm), hdetH]
      exact div_pos hDpos (hdiagPos m (Nat.le_of_lt hm))
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m (Nat.le_of_lt hm), hjacobi m hm]
      field_simp
    refine ⟨heq, ?_⟩
    rw [heq]
    exact (le_div_iff₀ hfactorPos).2
      (mul_le_of_le_one_right hmeasurePos.le hfactorLe)
  have hMonotone : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
      intro hm
      exact (ih (Nat.le_of_lt (Nat.lt_of_succ_le hm))).trans
        ((hJacobiStep m (Nat.lt_of_succ_le hm)).2)
  refine ⟨hHadLe, hHadEq, hScale, hMinBound, hJacobiStep, ?_⟩
  intro m hm
  have hbase : p22HadamardMeasure L ≤ lambdaMin m * Real.exp 1 := by
    calc
      p22HadamardMeasure L = measure 0 := hzero.symm
      _ ≤ measure m := hMonotone m hm
      _ ≤ lambdaMin m * Real.exp 1 :=
        (div_le_iff₀ (Real.exp_pos 1)).mp (hMinBound m hm)
  rw [hkappa m hm]
  apply (div_le_div_iff₀ (hlambdaMinPos m hm) hHpos).2
  calc
    lambdaMax m * p22HadamardMeasure L
        ≤ (n + 1 : ℝ) * p22HadamardMeasure L :=
          mul_le_mul_of_nonneg_right (hlambdaMax m hm) hHpos.le
    _ ≤ (n + 1 : ℝ) * (lambdaMin m * Real.exp 1) :=
          mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (n + 1 : ℝ) * Real.exp 1 * lambdaMin m := by ring

end VSCLReuse

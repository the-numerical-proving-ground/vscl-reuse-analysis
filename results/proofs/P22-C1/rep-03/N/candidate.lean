import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p22_tail_product_le_exp {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i ≤ (n + 1 : ℝ)) :
    (∏ i, x i) ≤ Real.exp 1 := by
  have hprod : (∏ i, x i) ≤ ∏ i, Real.exp (x i - 1) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (hx i).le
    · intro i hi
      have h := Real.add_one_le_exp (x i - 1)
      linarith
  rw [← Real.exp_sum] at hprod
  have hsum' : (∑ i, (x i - 1)) ≤ (1 : ℝ) := by
    have hcard : (∑ _i : Fin n, (1 : ℝ)) = n := by simp
    rw [Finset.sum_sub_distrib, hcard]
    linarith
  exact hprod.trans (Real.exp_le_exp_of_le hsum')

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
  have hDpos (i : Fin n) : 0 < p22DiagSquare L i := by
    unfold p22DiagSquare
    exact pow_pos (hLdiag i) _
  have hRpos (i : Fin n) : 0 < p22RowEnergy L i := by
    unfold p22RowEnergy
    have hsum : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
        (L i k) ^ 2 := by positivity
    linarith [hDpos i]
  have hDR (i : Fin n) : p22DiagSquare L i ≤ p22RowEnergy L i := by
    unfold p22RowEnergy
    have hsum : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
        (L i k) ^ 2 := by positivity
    linarith
  have hDprodpos : 0 < ∏ i, p22DiagSquare L i :=
    Finset.prod_pos fun i _ ↦ hDpos i
  have hRprodpos : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos fun i _ ↦ hRpos i
  have hDRprod : (∏ i, p22DiagSquare L i) ≤ ∏ i, p22RowEnergy L i :=
    Finset.prod_le_prod (fun i _ ↦ (hDpos i).le) (fun i _ ↦ hDR i)
  have hHpos : 0 < p22HadamardMeasure L := by
    unfold p22HadamardMeasure
    exact div_pos hDprodpos hRprodpos
  have hHle : p22HadamardMeasure L ≤ 1 := by
    unfold p22HadamardMeasure
    exact (div_le_one hRprodpos).2 hDRprod
  have hHeq : p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L := by
    constructor
    · intro heq i k hki
      have hprodEq : (∏ j, p22DiagSquare L j) = ∏ j, p22RowEnergy L j := by
        have heq' := heq
        unfold p22HadamardMeasure at heq'
        exact (div_eq_one_iff_eq hRprodpos.ne').mp heq'
      by_contra hne
      have hkpos : 0 < (L i k) ^ 2 := sq_pos_of_ne_zero hne
      have hmem : k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki⟩
      have hsum_le : (L i k) ^ 2 ≤
          ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val), (L i j) ^ 2 := by
        apply Finset.single_le_sum (fun j hj ↦ sq_nonneg (L i j))
        exact hmem
      have hstrict : p22DiagSquare L i < p22RowEnergy L i := by
        unfold p22RowEnergy
        linarith
      have hpstrict : (∏ j, p22DiagSquare L j) < ∏ j, p22RowEnergy L j :=
        Finset.prod_lt_prod (fun j _ ↦ hDpos j) (fun j _ ↦ hDR j)
          ⟨i, Finset.mem_univ i, hstrict⟩
      exact (ne_of_lt hpstrict) hprodEq
    · intro hdiag
      have hrows (i : Fin n) : p22RowEnergy L i = p22DiagSquare L i := by
        have hsumzero :
            (∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
              (L i k) ^ 2) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
          simp [hdiag i k hki]
        unfold p22RowEnergy
        rw [hsumzero]
        ring
      unfold p22HadamardMeasure
      simp_rw [hrows]
      exact div_self hDprodpos.ne'
  have hscaleD (i : Fin n) :
      p22DiagSquare (p22ScaleRows s L) i = s i ^ 2 * p22DiagSquare L i := by
    simp [p22DiagSquare, p22ScaleRows, mul_pow]
  have hscaleR (i : Fin n) :
      p22RowEnergy (p22ScaleRows s L) i = s i ^ 2 * p22RowEnergy L i := by
    simp only [p22RowEnergy, p22DiagSquare, p22ScaleRows, mul_pow]
    rw [← Finset.mul_sum]
    ring
  have hsprod : (∏ i : Fin n, s i ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (hs i)
  have hscale : p22HadamardMeasure (p22ScaleRows s L) =
      p22HadamardMeasure L := by
    unfold p22HadamardMeasure
    simp_rw [hscaleD, hscaleR]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    exact mul_div_mul_left _ _ hsprod
  have hmeasure_zero : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hmeasurepos (m : ℕ) (hm : m ≤ M) : 0 < measure m := by
    rw [hmeasure m hm, hdetH]
    exact div_pos hDprodpos (hdiagPos m hm)
  have heigen (m : ℕ) (hm : m ≤ M) :
      measure m / Real.exp 1 ≤ lambdaMin m := by
    have htail := p22_tail_product_le_exp (tailEigen m)
      (htailPos m hm) (htailSum m hm)
    rw [hmeasureEigen m hm]
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    exact mul_le_mul_of_nonneg_left htail (hlambdaMinPos m hm).le
  have hjstep (m : ℕ) (hm : m < M) :
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    have hm1 : m + 1 ≤ M := by omega
    have hf : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hd := hdiagPos m (by omega : m ≤ M)
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m (by omega : m ≤ M), hjacobi m hm]
      field_simp
    refine ⟨heq, ?_⟩
    rw [heq, le_div_iff₀ hf]
    nlinarith [hmeasurepos m (by omega : m ≤ M), sq_nonneg (jacobiEntry m)]
  have hmono : ∀ m, m ≤ M → measure 0 ≤ measure m := by
    intro m hm
    induction m with
    | zero => exact le_refl _
    | succ m ih =>
      exact (ih (by omega)).trans ((hjstep m (by omega)).2)
  have hkbound (m : ℕ) (hm : m ≤ M) :
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p22HadamardMeasure L := by
    have hmin : p22HadamardMeasure L / Real.exp 1 ≤ lambdaMin m :=
      (div_le_div_of_nonneg_right (hmeasure_zero ▸ hmono m hm) (Real.exp_pos 1).le).trans
        (heigen m hm)
    have hmin' : p22HadamardMeasure L ≤ Real.exp 1 * lambdaMin m := by
      simpa [mul_comm] using (div_le_iff₀ (Real.exp_pos 1)).mp hmin
    rw [hkappa m hm]
    apply (div_le_div_iff₀ (hlambdaMinPos m hm) hHpos).2
    have hnum : 0 ≤ (n + 1 : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_right (hlambdaMax m hm) hHpos.le
    have hsecond := mul_le_mul_of_nonneg_left hmin' hnum
    nlinarith
  exact ⟨hHle, hHeq, hscale, heigen, hjstep, hkbound⟩

end VSCLReuse

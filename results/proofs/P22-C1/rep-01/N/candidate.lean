import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p22_diagSquare_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22DiagSquare L i := by
  unfold p22DiagSquare
  exact pow_pos (hLdiag i) 2

private theorem p22_rowEnergy_ge {n : ℕ} (L : Fin n → Fin n → ℝ)
    (i : Fin n) : p22DiagSquare L i ≤ p22RowEnergy L i := by
  unfold p22RowEnergy
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun k hk => sq_nonneg (L i k))

private theorem p22_rowEnergy_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22RowEnergy L i :=
  lt_of_lt_of_le (p22_diagSquare_pos L hLdiag i) (p22_rowEnergy_ge L i)

private theorem p22_hadamard_le {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) : p22HadamardMeasure L ≤ 1 := by
  have hprod : (∏ i, p22DiagSquare L i) ≤ ∏ i, p22RowEnergy L i :=
    Finset.prod_le_prod (fun i _ => (p22_diagSquare_pos L hLdiag i).le)
      (fun i _ => p22_rowEnergy_ge L i)
  have hpos : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos fun i _ => p22_rowEnergy_pos L hLdiag i
  unfold p22HadamardMeasure
  exact (div_le_iff₀ hpos).2 (by simpa using hprod)

private theorem p22_hadamard_eq_iff {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) :
    p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L := by
  have hpos : 0 < ∏ i, p22RowEnergy L i :=
    Finset.prod_pos fun i _ => p22_rowEnergy_pos L hLdiag i
  constructor
  · intro heq
    have hprod : (∏ i, p22DiagSquare L i) = ∏ i, p22RowEnergy L i := by
      apply (div_eq_one_iff_eq hpos.ne').1
      exact heq
    have hrow : ∀ i, p22RowEnergy L i = p22DiagSquare L i := by
      intro i
      have hle := p22_rowEnergy_ge L i
      by_contra hne
      have hlt : p22DiagSquare L i < p22RowEnergy L i := lt_of_le_of_ne hle (Ne.symm hne)
      have hltprod : (∏ j, p22DiagSquare L j) < ∏ j, p22RowEnergy L j :=
        Finset.prod_lt_prod
          (fun j _ => p22_diagSquare_pos L hLdiag j)
          (fun j _ => p22_rowEnergy_ge L j)
          ⟨i, Finset.mem_univ i, hlt⟩
      exact (lt_irrefl _ (hprod ▸ hltprod))
    intro i k hik
    have hk : k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hik⟩
    have hsum : (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val),
        (L i j) ^ 2) = 0 := by
      have hi := hrow i
      unfold p22RowEnergy at hi
      linarith
    have hle : (L i k) ^ 2 ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), (L i j) ^ 2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (L i j)) hk
    nlinarith [sq_nonneg (L i k)]
  · intro hdiag
    have hrow : ∀ i, p22RowEnergy L i = p22DiagSquare L i := by
      intro i
      unfold p22RowEnergy
      have hsum : (∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val < i.val),
          (L i k) ^ 2) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
        simp [hdiag i k hki]
      rw [hsum, add_zero]
    unfold p22HadamardMeasure
    simp only [hrow]
    exact div_self (Finset.prod_ne_zero_iff.mpr (fun i hi =>
      (p22_diagSquare_pos L hLdiag i).ne'))

private theorem p22_scaled_diag {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) :
    p22DiagSquare (p22ScaleRows s L) i = (s i) ^ 2 * p22DiagSquare L i := by
  unfold p22DiagSquare p22ScaleRows
  ring

private theorem p22_scaled_row {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (i : Fin n) :
    p22RowEnergy (p22ScaleRows s L) i = (s i) ^ 2 * p22RowEnergy L i := by
  unfold p22RowEnergy
  rw [p22_scaled_diag]
  simp_rw [p22ScaleRows, mul_pow]
  rw [← Finset.mul_sum]
  ring

private theorem p22_scaled_measure {n : ℕ} (L : Fin n → Fin n → ℝ)
    (s : Fin n → ℝ) (hs : ∀ i, s i ≠ 0) :
    p22HadamardMeasure (p22ScaleRows s L) = p22HadamardMeasure L := by
  have hp : (∏ i, (s i) ^ 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero 2 (hs i)
  unfold p22HadamardMeasure
  simp_rw [p22_scaled_diag, p22_scaled_row]
  simp_rw [Finset.prod_mul_distrib]
  exact mul_div_mul_left _ _ hp

private theorem p22_tail_product_le_exp (n : ℕ) (hn : 0 < n)
    (z : Fin n → ℝ) (hz : ∀ i, 0 < z i)
    (hsum : ∑ i, z i ≤ (n + 1 : ℝ)) :
    (∏ i, z i) ≤ Real.exp 1 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hprodpos : 0 < ∏ i, z i := Finset.prod_pos fun i _ => hz i
  have hgm : (∏ i, z i) ^ (n : ℝ)⁻¹ ≤ (∑ i, z i) / (n : ℝ) := by
    simpa using Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin n => (1 : ℝ)) z
      (fun i hi => zero_le_one) (by simp [hnreal]) (fun i hi => (hz i).le)
  have hmean : (∑ i, z i) / (n : ℝ) ≤ ((n : ℝ) + 1) / n :=
    div_le_div_of_nonneg_right (by simpa using hsum) hnreal.le
  have hpow : (∏ i, z i) ≤ (((n : ℝ) + 1) / n) ^ n := by
    calc
      (∏ i, z i) = ((∏ i, z i) ^ (n : ℝ)⁻¹) ^ n :=
        (Real.rpow_inv_natCast_pow hprodpos.le (by omega)).symm
      _ ≤ (((n : ℝ) + 1) / n) ^ n :=
        pow_le_pow_left₀ (Real.rpow_nonneg hprodpos.le _) (hgm.trans hmean) n
  have hexp : (((n : ℝ) + 1) / n) ^ n ≤ Real.exp 1 := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := (-1 : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hform : ((n : ℝ) + 1) / n = 1 - (-1 : ℝ) / n := by
      field_simp
      ring
    simpa only [neg_neg, ← hform] using h
  exact hpow.trans hexp

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
  have hdetpos : 0 < detH := by
    rw [hdetH]
    exact Finset.prod_pos fun i _ => p22_diagSquare_pos L hLdiag i
  have hzero : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hhadpos : 0 < p22HadamardMeasure L := by
    rw [← hzero, hmeasure 0 (Nat.zero_le M)]
    exact div_pos hdetpos (hdiagPos 0 (Nat.zero_le M))
  have hmeasurepos (m : ℕ) (hm : m ≤ M) : 0 < measure m := by
    rw [hmeasure m hm]
    exact div_pos hdetpos (hdiagPos m hm)
  have hstep (m : ℕ) (hm : m < M) :
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
    have hmnext : m + 1 ≤ M := by omega
    have hfactor : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    rw [hmeasure (m + 1) hmnext, hjacobi m hm, hmeasure m (by omega)]
    field_simp [ne_of_gt hfactor, ne_of_gt (hdiagPos m (by omega))]
  have hstep_le (m : ℕ) (hm : m < M) : measure m ≤ measure (m + 1) := by
    rw [hstep m hm]
    have hfactor : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hfactor_le : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    apply (le_div_iff₀ hfactor).2
    calc
      measure m * (1 - (jacobiEntry m) ^ 2) ≤ measure m * 1 :=
        mul_le_mul_of_nonneg_left hfactor_le (hmeasurepos m (by omega)).le
      _ = measure m := by ring
  have hmon (m : ℕ) (hm : m ≤ M) : measure 0 ≤ measure m := by
    induction m with
    | zero => exact le_refl _
    | succ m ih =>
        exact le_trans (ih (by omega)) (hstep_le m (by omega))
  have hminbound (m : ℕ) (hm : m ≤ M) :
      measure m / Real.exp 1 ≤ lambdaMin m := by
    have htail : (∏ i, tailEigen m i) ≤ Real.exp 1 :=
      p22_tail_product_le_exp n hn (tailEigen m) (htailPos m hm) (htailSum m hm)
    have hle : measure m ≤ lambdaMin m * Real.exp 1 := by
      rw [hmeasureEigen m hm]
      exact mul_le_mul_of_nonneg_left htail (hlambdaMinPos m hm).le
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    simpa only [mul_comm] using hle
  refine ⟨p22_hadamard_le L hLdiag, p22_hadamard_eq_iff L hLdiag,
    p22_scaled_measure L s hs, hminbound, ?_, ?_⟩
  · intro m hm
    exact ⟨hstep m hm, hstep_le m hm⟩
  · intro m hm
    have hhadle : p22HadamardMeasure L ≤ lambdaMin m * Real.exp 1 := by
      calc
        p22HadamardMeasure L = measure 0 := hzero.symm
        _ ≤ measure m := hmon m hm
        _ ≤ lambdaMin m * Real.exp 1 := by
          have h := hminbound m hm
          exact (div_le_iff₀ (Real.exp_pos 1)).1 h |>.trans_eq (by ring)
    rw [hkappa m hm]
    apply (div_le_div_iff₀ (hlambdaMinPos m hm) hhadpos).2
    have hnat : (0 : ℝ) ≤ n + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hhadle hnat
    nlinarith [hmul, hlambdaMax m hm]

end VSCLReuse

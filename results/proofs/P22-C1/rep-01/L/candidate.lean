import VSCLReuse.P22.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p22_diag_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22DiagSquare L i := by
  unfold p22DiagSquare
  exact pow_pos (hLdiag i) _

private lemma p22_row_le {n : ℕ} (L : Fin n → Fin n → ℝ) (i : Fin n) :
    p22DiagSquare L i ≤ p22RowEnergy L i := by
  unfold p22RowEnergy
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun k hk => sq_nonneg _)

private lemma p22_row_pos {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hLdiag : ∀ i, 0 < L i i) (i : Fin n) : 0 < p22RowEnergy L i :=
  lt_of_lt_of_le (p22_diag_pos L hLdiag i) (p22_row_le L i)

private lemma p22_row_eq_of_diagonal {n : ℕ} (L : Fin n → Fin n → ℝ)
    (h : p22IsDiagonalCholesky L) (i : Fin n) :
    p22RowEnergy L i = p22DiagSquare L i := by
  unfold p22RowEnergy
  have hz : ∑ k ∈ Finset.univ.filter (fun k : Fin n ↦ k.val < i.val),
      (L i k) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k.val < i.val := (Finset.mem_filter.mp hk).2
    simp [h i k hki]
  rw [hz, add_zero]

private lemma p22_diagonal_of_row_eq {n : ℕ} (L : Fin n → Fin n → ℝ)
    (h : ∀ i, p22DiagSquare L i = p22RowEnergy L i) :
    p22IsDiagonalCholesky L := by
  intro i k hki
  have hsum : ∑ j ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val),
      (L i j) ^ 2 = 0 := by
    have hi := h i
    unfold p22RowEnergy at hi
    linarith
  have hk : k ∈ Finset.univ.filter (fun j : Fin n ↦ j.val < i.val) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hki⟩
  have hsq : (L i k) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sq_nonneg (L i j))).mp hsum k hk
  nlinarith [sq_nonneg (L i k)]

private lemma p22_scale_diag {n : ℕ} (s : Fin n → ℝ)
    (L : Fin n → Fin n → ℝ) (i : Fin n) :
    p22DiagSquare (p22ScaleRows s L) i = (s i) ^ 2 * p22DiagSquare L i := by
  simp only [p22DiagSquare, p22ScaleRows]
  ring

private lemma p22_scale_row {n : ℕ} (s : Fin n → ℝ)
    (L : Fin n → Fin n → ℝ) (i : Fin n) :
    p22RowEnergy (p22ScaleRows s L) i = (s i) ^ 2 * p22RowEnergy L i := by
  simp only [p22RowEnergy, p22_scale_diag, p22ScaleRows, mul_pow]
  rw [← Finset.mul_sum]
  ring

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
  let d : ℝ := ∏ i, p22DiagSquare L i
  let r : ℝ := ∏ i, p22RowEnergy L i
  have hdpos : 0 < d := Finset.prod_pos (fun i hi => p22_diag_pos L hLdiag i)
  have hrpos : 0 < r := Finset.prod_pos (fun i hi => p22_row_pos L hLdiag i)
  have hdr : d ≤ r := Finset.prod_le_prod
    (fun i hi => (p22_diag_pos L hLdiag i).le)
    (fun i hi => p22_row_le L i)
  have hhadpos : 0 < p22HadamardMeasure L := by
    change 0 < d / r
    exact div_pos hdpos hrpos
  have hhadle : p22HadamardMeasure L ≤ 1 := by
    change d / r ≤ 1
    exact (div_le_one hrpos).2 hdr
  have hhadiff : p22HadamardMeasure L = 1 ↔ p22IsDiagonalCholesky L := by
    constructor
    · intro heq
      have hprod : d = r := by
        apply (div_eq_one_iff_eq hrpos.ne').mp
        exact heq
      apply p22_diagonal_of_row_eq L
      intro i
      by_contra hi
      have hstrict : p22DiagSquare L i < p22RowEnergy L i :=
        lt_of_le_of_ne (p22_row_le L i) hi
      have hprodstrict : d < r := Finset.prod_lt_prod
        (fun j hj => p22_diag_pos L hLdiag j)
        (fun j hj => p22_row_le L j)
        ⟨i, Finset.mem_univ _, hstrict⟩
      exact (ne_of_lt hprodstrict) hprod
    · intro hdiagonal
      have hprod : d = r := Finset.prod_congr rfl
        (fun i hi => (p22_row_eq_of_diagonal L hdiagonal i).symm)
      change d / r = 1
      rw [hprod, div_self hrpos.ne']
  have hscale : p22HadamardMeasure (p22ScaleRows s L) =
      p22HadamardMeasure L := by
    let S : ℝ := ∏ i, (s i) ^ 2
    have hSpos : 0 < S := Finset.prod_pos
      (fun i hi => sq_pos_of_ne_zero (hs i))
    have hdiagscale : (∏ i, p22DiagSquare (p22ScaleRows s L) i) = S * d := by
      simp only [p22_scale_diag]
      rw [Finset.prod_mul_distrib]
    have hrowscale : (∏ i, p22RowEnergy (p22ScaleRows s L) i) = S * r := by
      simp only [p22_scale_row]
      rw [Finset.prod_mul_distrib]
    unfold p22HadamardMeasure
    rw [hdiagscale, hrowscale]
    exact mul_div_mul_left d r hSpos.ne'
  have hmeasure0 : measure 0 = p22HadamardMeasure L := by
    rw [hmeasure 0 (Nat.zero_le M), hdetH, hdiag0]
    rfl
  have hdetpos : 0 < detH := by
    rw [hdetH]
    exact hdpos
  have hmeasurepos : ∀ m, m ≤ M → 0 < measure m := by
    intro m hm
    rw [hmeasure m hm]
    exact div_pos hdetpos (hdiagPos m hm)
  have htailBound : ∀ m, m ≤ M →
      (∏ i, tailEigen m i) ≤ Real.exp 1 := by
    intro m hm
    have hsum : (∑ i, (tailEigen m i - 1)) ≤ (1 : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simpa [add_comm] using (htailSum m hm)
    calc
      (∏ i, tailEigen m i) ≤ ∏ i, Real.exp (tailEigen m i - 1) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact (htailPos m hm i).le
        · intro i hi
          have h := Real.add_one_le_exp (tailEigen m i - 1)
          linarith
      _ = Real.exp (∑ i, (tailEigen m i - 1)) := by
        rw [Real.exp_sum]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
  have hminimum : ∀ m, m ≤ M →
      measure m / Real.exp 1 ≤ lambdaMin m := by
    intro m hm
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    have hprod := htailBound m hm
    have hmul := mul_le_mul_of_nonneg_left hprod (hlambdaMinPos m hm).le
    rw [← hmeasureEigen m hm] at hmul
    simpa [mul_comm] using hmul
  have hjacobiStep : ∀ m, m < M →
      measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) ∧
      measure m ≤ measure (m + 1) := by
    intro m hm
    have hm1 : m + 1 ≤ M := hm
    have hm0 : m ≤ M := Nat.le_of_lt hm
    have hfpos : 0 < 1 - (jacobiEntry m) ^ 2 := by
      linarith [hjacobiSmall m hm]
    have hfle : 1 - (jacobiEntry m) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (jacobiEntry m)]
    have heq : measure (m + 1) = measure m / (1 - (jacobiEntry m) ^ 2) := by
      rw [hmeasure (m + 1) hm1, hmeasure m hm0, hjacobi m hm]
      field_simp
    refine ⟨heq, ?_⟩
    rw [heq]
    apply (le_div_iff₀ hfpos).2
    simpa using (mul_le_mul_of_nonneg_left hfle (hmeasurepos m hm0).le)
  have hmonotone : ∀ m, m ≤ M → p22HadamardMeasure L ≤ measure m := by
    intro m
    induction m with
    | zero =>
        intro hm
        rw [hmeasure0]
    | succ m ih =>
        intro hm
        have hlt : m < M := Nat.lt_of_succ_le hm
        exact (ih (Nat.le_of_lt hlt)).trans (hjacobiStep m hlt).2
  have hcondition : ∀ m, m ≤ M →
      kappa m ≤ (n + 1 : ℝ) * Real.exp 1 / p22HadamardMeasure L := by
    intro m hm
    have hmeasle : measure m ≤ lambdaMin m * Real.exp 1 :=
      (div_le_iff₀ (Real.exp_pos 1)).mp (hminimum m hm)
    have hhadlemin : p22HadamardMeasure L ≤ lambdaMin m * Real.exp 1 :=
      (hmonotone m hm).trans hmeasle
    rw [hkappa m hm]
    apply (div_le_div_iff₀ (hlambdaMinPos m hm) hhadpos).2
    calc
      lambdaMax m * p22HadamardMeasure L ≤
          (n + 1 : ℝ) * p22HadamardMeasure L := by
        exact mul_le_mul_of_nonneg_right (hlambdaMax m hm) hhadpos.le
      _ ≤ (n + 1 : ℝ) * (lambdaMin m * Real.exp 1) := by
        exact mul_le_mul_of_nonneg_left hhadlemin (by positivity)
      _ = ((n + 1 : ℝ) * Real.exp 1) * lambdaMin m := by ring
  exact ⟨hhadle, hhadiff, hscale, hminimum, hjacobiStep, hcondition⟩

end VSCLReuse

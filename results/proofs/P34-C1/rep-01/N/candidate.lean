import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p34_factor_natDegree (a : ℝ) :
    (Polynomial.C a - Polynomial.X).natDegree = 1 := by
  rw [show Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) by ring,
    Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

private lemma p34_factor_lc (a : ℝ) :
    (Polynomial.C a - Polynomial.X).leadingCoeff = -1 := by
  rw [show Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) by ring,
    Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]

private lemma p34_char_natDegree {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).natDegree = n := by
  unfold p34Characteristic
  rw [Polynomial.natDegree_prod]
  · simp [p34_factor_natDegree]
  · intro i hi h
    have hdeg := p34_factor_natDegree (v i)
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega

private lemma p34_char_lc {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).leadingCoeff = (-1) ^ n := by
  unfold p34Characteristic
  rw [Polynomial.leadingCoeff_prod]
  simp [p34_factor_lc]

private lemma p34_char_ne_zero {n : ℕ} (hn : 0 < n) (v : P34Vector n) :
    p34Characteristic v ≠ 0 := by
  intro h
  have hdeg := p34_char_natDegree v
  rw [h, Polynomial.natDegree_zero] at hdeg
  omega

private lemma p34_char_sub_natDegree_lt {n : ℕ} (hn : 0 < n)
    (v w : P34Vector n) :
    (p34Characteristic v - p34Characteristic w).natDegree < n := by
  by_cases hz : p34Characteristic v - p34Characteristic w = 0
  · simp [hz, hn]
  · have hv := p34_char_ne_zero hn v
    have hw := p34_char_ne_zero hn w
    have heq : (p34Characteristic v).degree = (p34Characteristic w).degree := by
      rw [Polynomial.degree_eq_natDegree hv, Polynomial.degree_eq_natDegree hw,
        p34_char_natDegree, p34_char_natDegree]
    have hlc : (p34Characteristic v).leadingCoeff =
        (p34Characteristic w).leadingCoeff := by
      rw [p34_char_lc, p34_char_lc]
    have hlt := Polynomial.degree_sub_lt heq hv hlc
    exact (Polynomial.natDegree_lt_natDegree hz hlt).trans_eq (p34_char_natDegree v)

private lemma p34_deleted_natDegree_le {n : ℕ} (d : P34Vector n) (i : Fin n) :
    (p34DeletedCharacteristic d i).natDegree ≤ n - 1 := by
  unfold p34DeletedCharacteristic
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i,
        (Polynomial.C (d j) - Polynomial.X).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = n - 1 := by simp [p34_factor_natDegree]

private lemma p34_char_eval {n : ℕ} (v : P34Vector n) (x : ℝ) :
    Polynomial.eval x (p34Characteristic v) = ∏ j, (v j - x) := by
  simp [p34Characteristic, Polynomial.eval_prod]

private lemma p34_deleted_eval {n : ℕ} (d : P34Vector n)
    (i : Fin n) (x : ℝ) :
    Polynomial.eval x (p34DeletedCharacteristic d i) =
      ∏ j ∈ Finset.univ.erase i, (d j - x) := by
  simp [p34DeletedCharacteristic, Polynomial.eval_prod]

private lemma p34_weight_factorization {n : ℕ} (d lambda : P34Vector n)
    (i : Fin n) :
    p34SecularWeight d lambda i =
      (lambda i - d i) *
        ∏ j ∈ Finset.univ.erase i, (lambda j - d i) / (d j - d i) := by
  classical
  unfold p34SecularWeight
  rw [← Finset.prod_erase_mul Finset.univ (fun j => lambda j - d i)
    (Finset.mem_univ i)]
  rw [Finset.prod_div_distrib]
  ring

private lemma p34_weight_pos {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d)
    (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j)
    (i : Fin n) : 0 < p34SecularWeight d lambda i := by
  rw [p34_weight_factorization]
  apply mul_pos (sub_pos.mpr (hlower i))
  apply Finset.prod_pos
  intro j hj
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact div_pos_of_neg_of_neg (sub_neg.mpr (hupper j i hlt))
      (sub_neg.mpr (hd hlt))
  · exact (hne heq).elim
  · exact div_pos (sub_pos.mpr (lt_trans (hd hgt) (hlower j)))
      (sub_pos.mpr (hd hgt))

private lemma p34_den_ne_zero {n : ℕ} (d : P34Vector n)
    (hd : StrictMono d) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (hd.injective.ne hne)

private lemma p34_weight_mul_den {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (i : Fin n) :
    p34SecularWeight d lambda i *
        (∏ j ∈ Finset.univ.erase i, (d j - d i)) =
      ∏ j, (lambda j - d i) := by
  unfold p34SecularWeight
  exact div_mul_cancel₀ _ (p34_den_ne_zero d hd i)

private lemma p34_char_eval_self_zero {n : ℕ} (d : P34Vector n)
    (i : Fin n) : Polynomial.eval (d i) (p34Characteristic d) = 0 := by
  rw [p34_char_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

private lemma p34_deleted_eval_other_zero {n : ℕ} (d : P34Vector n)
    (i j : Fin n) (hji : j ≠ i) :
    Polynomial.eval (d i) (p34DeletedCharacteristic d j) = 0 := by
  rw [p34_deleted_eval]
  apply Finset.prod_eq_zero (i := i)
  · simp [hji.symm]
  · exact sub_self _

private lemma p34_weight_eval {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (i : Fin n) :
    p34SecularWeight d lambda i *
      Polynomial.eval (d i) (p34DeletedCharacteristic d i) =
        Polynomial.eval (d i) (p34Characteristic lambda) := by
  rw [p34_deleted_eval, p34_char_eval]
  exact p34_weight_mul_den d lambda hd i

private lemma p34_sum_eval {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (i : Fin n) :
    Polynomial.eval (d i)
      (∑ j, Polynomial.C (p34SecularWeight d lambda j) *
        p34DeletedCharacteristic d j) =
      Polynomial.eval (d i) (p34Characteristic lambda) := by
  rw [Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single i]
  · simpa only [Polynomial.eval_mul, Polynomial.eval_C] using
      p34_weight_eval d lambda hd i
  · intro j hj hji
    simp [p34_deleted_eval_other_zero d i j hji]
  · simp

private lemma p34_sum_natDegree_lt {n : ℕ} (hn : 0 < n)
    (d lambda : P34Vector n) :
    (∑ i, Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i).natDegree < n := by
  calc
    _ ≤ n - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (p34_deleted_natDegree_le d i)
    _ < n := by omega

/-- P34-C1: the inverse secular construction in equations (3.2)--(3.3). -/
theorem p34_c1_inverse_secular_construction
    (n : ℕ) (hn : 0 < n)
    (d lambda : P34Vector n)
    (hd : StrictMono d)
    (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j) :
    (∀ i, 0 < p34SecularWeight d lambda i) ∧
      p34Characteristic lambda =
        p34Characteristic d +
          ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
            p34DeletedCharacteristic d i := by
  -- PROOF_START P34-C1-H001
  constructor
  · exact p34_weight_pos d lambda hd hlower hupper
  · let S : Polynomial ℝ :=
      ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
        p34DeletedCharacteristic d i
    have hzero : p34Characteristic lambda - p34Characteristic d - S = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        _ hd.injective ?_ ?_
      · intro i
        simp only [Polynomial.eval_sub]
        rw [p34_char_eval_self_zero d i]
        change Polynomial.eval (d i) (p34Characteristic lambda) - 0 -
          Polynomial.eval (d i)
            (∑ j, Polynomial.C (p34SecularWeight d lambda j) *
              p34DeletedCharacteristic d j) = 0
        rw [p34_sum_eval d lambda hd i]
        ring
      · have h₁ := p34_char_sub_natDegree_lt hn lambda d
        have h₂ := p34_sum_natDegree_lt hn d lambda
        have hbound :
            (p34Characteristic lambda - p34Characteristic d - S).natDegree < n :=
          (Polynomial.natDegree_sub_le _ _).trans_lt (max_lt h₁ h₂)
        simpa only [Fintype.card_fin] using hbound
    dsimp [S] at hzero
    linear_combination hzero

end VSCLReuse

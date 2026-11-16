import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p34_factor_degree (a : ℝ) :
    (Polynomial.C a - Polynomial.X).degree = 1 := by
  have h : Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) := by ring
  rw [h, Polynomial.degree_neg, Polynomial.degree_X_sub_C]

private lemma p34_factor_lc (a : ℝ) :
    (Polynomial.C a - Polynomial.X).leadingCoeff = -1 := by
  have h : Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) := by ring
  rw [h, Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]

private lemma p34_char_degree {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).degree = n := by
  simp [p34Characteristic, Polynomial.degree_prod, p34_factor_degree]

private lemma p34_char_lc {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).leadingCoeff = (-1 : ℝ) ^ n := by
  simp [p34Characteristic, Polynomial.leadingCoeff_prod, p34_factor_lc]

private lemma p34_deleted_degree {n : ℕ} (v : P34Vector n) (i : Fin n) :
    (p34DeletedCharacteristic v i).degree = (n - 1 : ℕ) := by
  simp [p34DeletedCharacteristic, Polynomial.degree_prod, p34_factor_degree]

private lemma p34_char_eval {n : ℕ} (v : P34Vector n) (x : ℝ) :
    Polynomial.eval x (p34Characteristic v) = ∏ j, (v j - x) := by
  simp [p34Characteristic, Polynomial.eval_prod]

private lemma p34_deleted_eval {n : ℕ} (v : P34Vector n) (i : Fin n) (x : ℝ) :
    Polynomial.eval x (p34DeletedCharacteristic v i) =
      ∏ j ∈ Finset.univ.erase i, (v j - x) := by
  simp [p34DeletedCharacteristic, Polynomial.eval_prod]

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
  classical
  have hweight : ∀ i, 0 < p34SecularWeight d lambda i := by
    intro i
    have hfactor : ∀ j ∈ Finset.univ.erase i,
        0 < (lambda j - d i) / (d j - d i) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rcases lt_trichotomy j i with hlt | heq | hgt
      · exact div_pos_of_neg_of_neg (sub_neg.mpr (hupper j i hlt))
          (sub_neg.mpr (hd hlt))
      · exact (hji heq).elim
      · exact div_pos (sub_pos.mpr (lt_trans (hd hgt) (hlower j)))
          (sub_pos.mpr (hd hgt))
    calc
      p34SecularWeight d lambda i =
          (lambda i - d i) *
            ∏ j ∈ Finset.univ.erase i, (lambda j - d i) / (d j - d i) := by
              unfold p34SecularWeight
              rw [Finset.prod_div_distrib, ← mul_div_assoc,
                Finset.mul_prod_erase Finset.univ (fun j => lambda j - d i)
                  (Finset.mem_univ i)]
      _ > 0 := mul_pos (sub_pos.mpr (hlower i)) (Finset.prod_pos hfactor)
  refine ⟨hweight, ?_⟩
  let corr : Polynomial ℝ :=
    ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i
  have hcorr_degree : corr.degree < (n : WithBot ℕ) := by
    have hle : corr.degree ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
      dsimp [corr]
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le ?_)
      intro i hi
      calc
        (Polynomial.C (p34SecularWeight d lambda i) *
            p34DeletedCharacteristic d i).degree ≤
            (Polynomial.C (p34SecularWeight d lambda i)).degree +
              (p34DeletedCharacteristic d i).degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + ((n - 1 : ℕ) : WithBot ℕ) := by
          exact add_le_add Polynomial.degree_C_le (le_of_eq (p34_deleted_degree d i))
        _ = ((n - 1 : ℕ) : WithBot ℕ) := by simp
    exact lt_of_le_of_lt hle (by exact_mod_cast Nat.sub_lt hn (by decide : 0 < 1))
  have hdeg_rhs : (p34Characteristic d + corr).degree = n := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · exact p34_char_degree d
    · simpa [p34_char_degree] using hcorr_degree
  have hlc_rhs : (p34Characteristic d + corr).leadingCoeff = (-1 : ℝ) ^ n := by
    rw [Polynomial.leadingCoeff_add_of_degree_lt']
    · exact p34_char_lc d
    · simpa [p34_char_degree] using hcorr_degree
  have hdeg_lhs : (p34Characteristic lambda).degree = n := p34_char_degree lambda
  have hlc_lhs : (p34Characteristic lambda).leadingCoeff = (-1 : ℝ) ^ n :=
    p34_char_lc lambda
  have heval : ∀ i : Fin n,
      Polynomial.eval (d i) (p34Characteristic lambda) =
        Polynomial.eval (d i) (p34Characteristic d + corr) := by
    intro i
    have hden : (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
      apply (Finset.prod_ne_zero_iff).2
      intro j hj
      exact sub_ne_zero.mpr (hd.injective.ne (Finset.mem_erase.mp hj).1)
    have hnum : (∏ j, (lambda j - d i)) =
        p34SecularWeight d lambda i *
          ∏ j ∈ Finset.univ.erase i, (d j - d i) := by
      unfold p34SecularWeight
      exact (div_mul_cancel₀ _ hden).symm
    have hself : Polynomial.eval (d i) (p34Characteristic d) = 0 := by
      rw [p34_char_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    have hoff : ∀ j : Fin n, j ≠ i →
        Polynomial.eval (d i) (p34DeletedCharacteristic d j) = 0 := by
      intro j hji
      rw [p34_deleted_eval]
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩) (sub_self _)
    have hcorr_eval : Polynomial.eval (d i) corr =
        p34SecularWeight d lambda i *
          ∏ j ∈ Finset.univ.erase i, (d j - d i) := by
      dsimp [corr]
      rw [Polynomial.eval_finset_sum]
      simp_rw [Polynomial.eval_mul, Polynomial.eval_C]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [p34_deleted_eval]
      · intro j hj hji
        rw [hoff j hji]
        simp
    rw [p34_char_eval, Polynomial.eval_add, hself, hcorr_eval]
    simpa using hnum
  change p34Characteristic lambda = p34Characteristic d + corr
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (Finset.univ : Finset (Fin n))
    (v := d) (by intro i hi j hj hij; exact hd.injective hij)
  · simpa using le_of_eq hdeg_lhs
  · exact hdeg_lhs.trans hdeg_rhs.symm
  · exact hlc_lhs.trans hlc_rhs.symm
  · intro i hi; exact heval i

end VSCLReuse

import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

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
  have hinj : Function.Injective d := hd.injective
  have hfactor_deg (x : ℝ) :
      (Polynomial.C x - Polynomial.X).degree = 1 := by
    rw [show Polynomial.C x - Polynomial.X =
        -(Polynomial.X - Polynomial.C x) by ring,
      Polynomial.degree_neg, Polynomial.degree_X_sub_C]
  have hfactor_nat (x : ℝ) :
      (Polynomial.C x - Polynomial.X).natDegree = 1 := by
    rw [show Polynomial.C x - Polynomial.X =
        -(Polynomial.X - Polynomial.C x) by ring,
      Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hfactor_lc (x : ℝ) :
      (Polynomial.C x - Polynomial.X).leadingCoeff = -1 := by
    rw [show Polynomial.C x - Polynomial.X =
        -(Polynomial.X - Polynomial.C x) by ring,
      Polynomial.leadingCoeff_neg,
      (Polynomial.monic_X_sub_C x).leadingCoeff]
  have hchar_deg (v : P34Vector n) :
      (p34Characteristic v).degree = n := by
    simp [p34Characteristic, Polynomial.degree_prod, hfactor_deg]
  have hchar_lc (v : P34Vector n) :
      (p34Characteristic v).leadingCoeff = (-1 : ℝ) ^ n := by
    simp [p34Characteristic, Polynomial.leadingCoeff_prod, hfactor_lc]
  have hden (i : Fin n) :
      (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (fun h => hji (hinj h))
  have hweight_pos (i : Fin n) : 0 < p34SecularWeight d lambda i := by
    have hratio (j : Fin n) (hji : j ≠ i) :
        0 < (lambda j - d i) / (d j - d i) := by
      rcases lt_trichotomy j i with hlt | heq | hgt
      · apply div_pos_of_neg_of_neg
        · exact sub_neg.mpr (hupper j i hlt)
        · exact sub_neg.mpr (hd hlt)
      · exact (hji heq).elim
      · apply div_pos
        · exact sub_pos.mpr ((hd hgt).trans (hlower j))
        · exact sub_pos.mpr (hd hgt)
    have hprod :
        0 < ∏ j ∈ Finset.univ.erase i,
          (lambda j - d i) / (d j - d i) := by
      apply Finset.prod_pos
      intro j hj
      exact hratio j (Finset.mem_erase.mp hj).1
    have hrewrite :
        p34SecularWeight d lambda i =
          (lambda i - d i) *
            ∏ j ∈ Finset.univ.erase i,
              (lambda j - d i) / (d j - d i) := by
      rw [p34SecularWeight, Finset.prod_div_distrib,
        ← Finset.mul_prod_erase Finset.univ (fun j => lambda j - d i)
          (Finset.mem_univ i)]
      ring
    rw [hrewrite]
    exact mul_pos (sub_pos.mpr (hlower i)) hprod
  refine ⟨hweight_pos, ?_⟩
  let correction : Polynomial ℝ :=
    ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i
  have hdeleted_deg (i : Fin n) :
      (p34DeletedCharacteristic d i).natDegree < n := by
    calc
      (p34DeletedCharacteristic d i).natDegree ≤
          ∑ j ∈ Finset.univ.erase i,
            (Polynomial.C (d j) - Polynomial.X).natDegree := by
              exact Polynomial.natDegree_prod_le _ _
      _ = (Finset.univ.erase i).card := by simp [hfactor_nat]
      _ < n := by simpa using
        (Finset.card_erase_lt_of_mem (Finset.mem_univ i))
  have hcorr_deg : correction.natDegree < n := by
    have hbound : correction.natDegree ≤ n - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Nat.le_sub_one_of_lt (hdeleted_deg i))
    exact lt_of_le_of_lt hbound (Nat.sub_lt hn (by omega))
  have hchar_ne (v : P34Vector n) : p34Characteristic v ≠ 0 := by
    intro hv
    have h := hchar_deg v
    rw [hv] at h
    simp at h
  have hbase_deg :
      (p34Characteristic lambda - p34Characteristic d).natDegree < n := by
    by_cases hz : p34Characteristic lambda - p34Characteristic d = 0
    · simp [hz, hn]
    · apply (Polynomial.natDegree_lt_iff_degree_lt hz).2
      have h := Polynomial.degree_sub_lt
        ((hchar_deg lambda).trans (hchar_deg d).symm)
        (hchar_ne lambda)
        ((hchar_lc lambda).trans (hchar_lc d).symm)
      simpa [hchar_deg] using h
  have hdiff_deg :
      ((p34Characteristic lambda - p34Characteristic d) - correction).natDegree < n := by
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (by
      exact max_lt hbase_deg hcorr_deg)
  have heval (i : Fin n) :
      Polynomial.eval (d i)
        ((p34Characteristic lambda - p34Characteristic d) - correction) = 0 := by
    have hdel_eval (j : Fin n) (hji : j ≠ i) :
        Polynomial.eval (d i) (p34DeletedCharacteristic d j) = 0 := by
      simp only [p34DeletedCharacteristic, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
        (by simp)
    have hdiag : Polynomial.eval (d i) (p34Characteristic d) = 0 := by
      simp only [p34Characteristic, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hdeleted :
        Polynomial.eval (d i) (p34DeletedCharacteristic d i) =
          ∏ j ∈ Finset.univ.erase i, (d j - d i) := by
      simp [p34DeletedCharacteristic, Polynomial.eval_prod]
    have hlambda :
        Polynomial.eval (d i) (p34Characteristic lambda) =
          ∏ j, (lambda j - d i) := by
      simp [p34Characteristic, Polynomial.eval_prod]
    have hcorrection :
        Polynomial.eval (d i) correction =
          p34SecularWeight d lambda i *
            ∏ j ∈ Finset.univ.erase i, (d j - d i) := by
      simp only [correction, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [Finset.sum_eq_single i]
      · rw [hdeleted]
      · intro j hj hji
        rw [hdel_eval j hji, mul_zero]
      · simp
    rw [Polynomial.eval_sub, Polynomial.eval_sub, hdiag, hcorrection,
      hlambda, sub_zero, p34SecularWeight]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ (hden i)).symm
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    ((p34Characteristic lambda - p34Characteristic d) - correction)
    hinj heval (by simpa using hdiff_deg)
  have hident : p34Characteristic lambda = p34Characteristic d + correction := by
    calc
      p34Characteristic lambda = p34Characteristic d + correction +
          (p34Characteristic lambda - p34Characteristic d - correction) := by ring
      _ = p34Characteristic d + correction := by rw [hzero, add_zero]
  exact hident

end VSCLReuse

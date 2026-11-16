import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p34_weight_eq_prod {n : ℕ} (d lambda : P34Vector n) (i : Fin n) :
    p34SecularWeight d lambda i =
      (lambda i - d i) *
        ∏ j ∈ Finset.univ.erase i, (lambda j - d i) / (d j - d i) := by
  classical
  rw [p34SecularWeight, Finset.prod_div_distrib]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => lambda j - d i) (Finset.mem_univ i)]
  ring

private lemma p34_weight_pos {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j) (i : Fin n) :
    0 < p34SecularWeight d lambda i := by
  rw [p34_weight_eq_prod]
  apply mul_pos (sub_pos.mpr (hlower i))
  apply Finset.prod_pos
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact div_pos_of_neg_of_neg (sub_neg.mpr (hupper j i hlt))
      (sub_neg.mpr (hd hlt))
  · exact False.elim (hji heq)
  · exact div_pos (sub_pos.mpr (lt_trans (hd hgt) (hlower j)))
      (sub_pos.mpr (hd hgt))

private lemma p34_factor_degree (a : ℝ) :
    (Polynomial.C a - Polynomial.X).degree = 1 := by
  rw [show Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) by ring,
    Polynomial.degree_neg, Polynomial.degree_X_sub_C]

private lemma p34_factor_lc (a : ℝ) :
    (Polynomial.C a - Polynomial.X).leadingCoeff = -1 := by
  rw [show Polynomial.C a - Polynomial.X = -(Polynomial.X - Polynomial.C a) by ring,
    Polynomial.leadingCoeff_neg, (Polynomial.monic_X_sub_C a).leadingCoeff]

private lemma p34_char_degree {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).degree = (n : WithBot ℕ) := by
  classical
  rw [p34Characteristic, Polynomial.degree_prod]
  simp [p34_factor_degree]

private lemma p34_char_lc {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).leadingCoeff = (-1 : ℝ) ^ n := by
  classical
  rw [p34Characteristic, Polynomial.leadingCoeff_prod]
  simp [p34_factor_lc]

private lemma p34_deleted_degree {n : ℕ} (d : P34Vector n) (i : Fin n) :
    (p34DeletedCharacteristic d i).degree = ((n - 1 : ℕ) : WithBot ℕ) := by
  classical
  rw [p34DeletedCharacteristic, Polynomial.degree_prod]
  simp [p34_factor_degree]

private lemma p34_extra_natDegree_lt {n : ℕ} (hn : 0 < n)
    (d lambda : P34Vector n) :
    (∑ i, Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i).natDegree < n := by
  classical
  calc
    _ ≤ n - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_eq_of_degree_eq_some (p34_deleted_degree d i)).le
    _ < n := Nat.sub_lt hn (by decide)

private lemma p34_char_eval {n : ℕ} (v : P34Vector n) (x : ℝ) :
    (p34Characteristic v).eval x = ∏ j, (v j - x) := by
  simp [p34Characteristic, Polynomial.eval_prod]

private lemma p34_deleted_eval {n : ℕ} (d : P34Vector n) (i : Fin n) (x : ℝ) :
    (p34DeletedCharacteristic d i).eval x =
      ∏ j ∈ Finset.univ.erase i, (d j - x) := by
  simp [p34DeletedCharacteristic, Polynomial.eval_prod]

private lemma p34_den_ne_zero {n : ℕ} (d : P34Vector n) (hd : StrictMono d) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (hd.injective.ne hji)

private lemma p34_char_eval_self {n : ℕ} (d : P34Vector n) (i : Fin n) :
    (p34Characteristic d).eval (d i) = 0 := by
  rw [p34_char_eval]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (d i))

private lemma p34_deleted_eval_other {n : ℕ} (d : P34Vector n) (i j : Fin n)
    (hji : j ≠ i) :
    (p34DeletedCharacteristic d j).eval (d i) = 0 := by
  rw [p34_deleted_eval]
  apply Finset.prod_eq_zero
  · exact Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
  · exact sub_self (d i)

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
  · classical
    let extra : Polynomial ℝ :=
      ∑ i, Polynomial.C (p34SecularWeight d lambda i) * p34DeletedCharacteristic d i
    have hsmall : extra.natDegree < n := p34_extra_natDegree_lt hn d lambda
    have hdeg : (p34Characteristic d + extra).degree = (n : WithBot ℕ) := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt]
      · exact p34_char_degree d
      · apply Polynomial.degree_lt_degree
        rw [Polynomial.natDegree_eq_of_degree_eq_some (p34_char_degree d)]
        exact hsmall
    have hlc : (p34Characteristic lambda).leadingCoeff =
        (p34Characteristic d + extra).leadingCoeff := by
      rw [Polynomial.leadingCoeff_add_of_degree_lt']
      · rw [p34_char_lc, p34_char_lc]
      · apply Polynomial.degree_lt_degree
        rw [Polynomial.natDegree_eq_of_degree_eq_some (p34_char_degree d)]
        exact hsmall
    have heval : ∀ i : Fin n,
        (p34Characteristic lambda).eval (d i) =
          (p34Characteristic d + extra).eval (d i) := by
      intro i
      rw [p34_char_eval]
      change (∏ j, (lambda j - d i)) =
        (p34Characteristic d +
          ∑ j, Polynomial.C (p34SecularWeight d lambda j) *
            p34DeletedCharacteristic d j).eval (d i)
      simp only [Polynomial.eval_add, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        Polynomial.eval_C, p34_char_eval_self, zero_add]
      rw [Finset.sum_eq_single i]
      · rw [p34_deleted_eval, p34SecularWeight]
        exact (div_mul_cancel₀ _ (p34_den_ne_zero d hd i)).symm
      · intro j hj hji
        rw [p34_deleted_eval_other d i j hji, mul_zero]
      · simp
    have hinj : Set.InjOn d (Finset.univ : Finset (Fin n)) := by
      intro i hi j hj hij
      exact hd.injective hij
    apply Polynomial.eq_of_degree_le_of_eval_index_eq (s := Finset.univ) (v := d)
      hinj
    · simp [p34_char_degree]
    · rw [p34_char_degree, hdeg]
    · exact hlc
    · intro i hi
      exact heval i

end VSCLReuse

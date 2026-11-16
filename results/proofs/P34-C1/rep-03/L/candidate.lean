import VSCLReuse.P34.Definitions


open scoped BigOperators

namespace VSCLReuse

private lemma p34_factor_degree (a : ℝ) :
    (Polynomial.C a - Polynomial.X).degree = 1 := by
  calc
    (Polynomial.C a - Polynomial.X).degree = (-(Polynomial.X - Polynomial.C a)).degree := by congr 1; ring
    _ = (Polynomial.X - Polynomial.C a).degree := Polynomial.degree_neg _
    _ = (1 : WithBot ℕ) := Polynomial.degree_X_sub_C a

private lemma p34_factor_leadingCoeff (a : ℝ) :
    (Polynomial.C a - Polynomial.X).leadingCoeff = -1 := by
  calc
    (Polynomial.C a - Polynomial.X).leadingCoeff = (-(Polynomial.X - Polynomial.C a)).leadingCoeff := by congr 1; ring
    _ = (-(Polynomial.X - Polynomial.C a).leadingCoeff : ℝ) := Polynomial.leadingCoeff_neg _
    _ = (-1 : ℝ) := by rw [(Polynomial.monic_X_sub_C a).leadingCoeff]

private lemma p34_characteristic_degree {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).degree = (n : WithBot ℕ) := by
  unfold p34Characteristic
  rw [Polynomial.degree_prod]
  simp [p34_factor_degree]

private lemma p34_characteristic_leadingCoeff {n : ℕ} (v : P34Vector n) :
    (p34Characteristic v).leadingCoeff = (-1 : ℝ) ^ n := by
  unfold p34Characteristic
  rw [Polynomial.leadingCoeff_prod]
  simp [p34_factor_leadingCoeff]

private lemma p34_deleted_degree {n : ℕ} (d : P34Vector n) (i : Fin n) :
    (p34DeletedCharacteristic d i).degree = ((n - 1 : ℕ) : WithBot ℕ) := by
  unfold p34DeletedCharacteristic
  rw [Polynomial.degree_prod]
  simp [p34_factor_degree]

private lemma p34_characteristic_eval {n : ℕ} (v : P34Vector n) (x : ℝ) :
    (p34Characteristic v).eval x = ∏ i, (v i - x) := by
  simp [p34Characteristic, Polynomial.eval_prod]

private lemma p34_deleted_eval {n : ℕ} (d : P34Vector n) (i : Fin n) (x : ℝ) :
    (p34DeletedCharacteristic d i).eval x =
      ∏ j ∈ Finset.univ.erase i, (d j - x) := by
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
  have hinj : Function.Injective d := hd.injective
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
    unfold p34SecularWeight
    rw [← Finset.mul_prod_erase Finset.univ (fun j => lambda j - d i) (Finset.mem_univ i)]
    rw [mul_div_assoc, ← Finset.prod_div_distrib]
    exact mul_pos (sub_pos.mpr (hlower i)) (Finset.prod_pos hfactor)
  refine ⟨hweight, ?_⟩
  have hdel_lt (i : Fin n) :
      (p34DeletedCharacteristic d i).degree < (n : WithBot ℕ) := by
    rw [p34_deleted_degree]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt hn (by decide))
  have hchar_ne : p34Characteristic lambda ≠ 0 := by
    intro h
    have hdg := p34_characteristic_degree lambda
    rw [h] at hdg
    simp at hdg
  have hdiff_degree :
      (p34Characteristic lambda - p34Characteristic d).degree < (n : WithBot ℕ) := by
    have h := Polynomial.degree_sub_lt
      (p34_characteristic_degree lambda |>.trans (p34_characteristic_degree d).symm)
      hchar_ne
      (by rw [p34_characteristic_leadingCoeff, p34_characteristic_leadingCoeff])
    simpa [p34_characteristic_degree] using h
  have hsum_degree :
      (∑ i, Polynomial.C (p34SecularWeight d lambda i) *
        p34DeletedCharacteristic d i).degree < (n : WithBot ℕ) := by
    apply (Polynomial.degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2
    intro i hi
    have hu : IsUnit (p34SecularWeight d lambda i) :=
      isUnit_iff_ne_zero.mpr (ne_of_gt (hweight i))
    simpa only [Polynomial.degree_C_mul_of_isUnit hu] using hdel_lt i
  have hdegree :
      (p34Characteristic lambda -
        (p34Characteristic d +
          ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
            p34DeletedCharacteristic d i)).degree < (n : WithBot ℕ) := by
    rw [sub_add_eq_sub_sub]
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hdiff_degree hsum_degree)
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq (s := Finset.univ)
    (v := d) (f := p34Characteristic lambda)
    (g := p34Characteristic d +
      ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
        p34DeletedCharacteristic d i)
  · exact fun a ha b hb hab => hinj hab
  · simpa using hdegree
  · intro i hi
    have hchar_d : (p34Characteristic d).eval (d i) = 0 := by
      rw [p34_characteristic_eval]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    have hdenom_ne :
        (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      exact sub_ne_zero.mpr (hinj.ne ((Finset.mem_erase.mp hj).1))
    have hratio :
        p34SecularWeight d lambda i *
          (∏ j ∈ Finset.univ.erase i, (d j - d i)) =
            ∏ j, (lambda j - d i) := by
      unfold p34SecularWeight
      exact div_mul_cancel₀ _ hdenom_ne
    have hsum_eval :
        (∑ j, Polynomial.C (p34SecularWeight d lambda j) *
          p34DeletedCharacteristic d j).eval (d i) =
            p34SecularWeight d lambda i *
              (∏ j ∈ Finset.univ.erase i, (d j - d i)) := by
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
      rw [Finset.sum_eq_single i]
      · simp [p34_deleted_eval]
      · intro j hj hji
        have hij : i ∈ Finset.univ.erase j :=
          Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩
        have hz : (p34DeletedCharacteristic d j).eval (d i) = 0 := by
          rw [p34_deleted_eval]
          exact Finset.prod_eq_zero hij (by simp)
        simp [hz]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    calc
      (p34Characteristic lambda).eval (d i) = ∏ j, (lambda j - d i) :=
        p34_characteristic_eval lambda (d i)
      _ = p34SecularWeight d lambda i *
            (∏ j ∈ Finset.univ.erase i, (d j - d i)) := hratio.symm
      _ = (p34Characteristic d +
          ∑ j, Polynomial.C (p34SecularWeight d lambda j) *
            p34DeletedCharacteristic d j).eval (d i) := by
        rw [Polynomial.eval_add, hchar_d, zero_add, hsum_eval]


end VSCLReuse

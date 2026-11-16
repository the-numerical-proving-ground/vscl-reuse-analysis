import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p34_weight_pos {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j)
    (i : Fin n) : 0 < p34SecularWeight d lambda i := by
  classical
  have hratio (j : Fin n) (hj : j ∈ Finset.univ.erase i) :
      0 < (lambda j - d i) / (d j - d i) := by
    have hne : j ≠ i := Finset.ne_of_mem_erase hj
    rcases lt_trichotomy j i with hlt | heq | hgt
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (hupper j i hlt))
        (sub_neg.mpr (hd hlt))
    · exact (hne heq).elim
    · exact div_pos (sub_pos.mpr (lt_trans (hd hgt) (hlower j)))
        (sub_pos.mpr (hd hgt))
  have hnum : (∏ j : Fin n, (lambda j - d i)) =
      (lambda i - d i) * ∏ j ∈ Finset.univ.erase i, (lambda j - d i) :=
    (Finset.mul_prod_erase Finset.univ (fun j => lambda j - d i) (Finset.mem_univ i)).symm
  rw [p34SecularWeight, hnum]
  rw [mul_div_assoc, ← Finset.prod_div_distrib]
  exact mul_pos (sub_pos.mpr (hlower i)) (Finset.prod_pos hratio)

private lemma p34_factor_natDegree (a : ℝ) :
    (Polynomial.C a - Polynomial.X).natDegree = 1 := by
  have h : Polynomial.C a - Polynomial.X =
      -(Polynomial.X - Polynomial.C a) := by ring
  rw [h, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]

private lemma p34_characteristic_sub_natDegree_lt {n : ℕ} (hn : 0 < n)
    (d lambda : P34Vector n) :
    (p34Characteristic lambda - p34Characteristic d).natDegree < n := by
  classical
  let m (v : P34Vector n) : Polynomial ℝ :=
    ∏ i : Fin n, (Polynomial.X - Polynomial.C (v i))
  have hm (v : P34Vector n) : Polynomial.IsMonicOfDegree (m v) n := by
    constructor
    · simp [m]
    · exact Polynomial.monic_prod_X_sub_C v Finset.univ
  have hchar (v : P34Vector n) :
      p34Characteristic v = (-1 : Polynomial ℝ) ^ n * m v := by
    unfold p34Characteristic m
    simp_rw [show ∀ i : Fin n, Polynomial.C (v i) - Polynomial.X =
        -(Polynomial.X - Polynomial.C (v i)) from fun i => by ring]
    rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  rw [hchar lambda, hchar d, ← mul_sub]
  have hdeg := (hm lambda).natDegree_sub_lt (Nat.ne_of_gt hn) (hm d)
  exact (Polynomial.natDegree_mul_le).trans_lt (by simpa [m] using hdeg)

private lemma p34_deleted_natDegree_le {n : ℕ} (d : P34Vector n)
    (i : Fin n) : (p34DeletedCharacteristic d i).natDegree ≤ n - 1 := by
  classical
  unfold p34DeletedCharacteristic
  calc
    (∏ j ∈ Finset.univ.erase i, (Polynomial.C (d j) - Polynomial.X)).natDegree
        ≤ ∑ j ∈ Finset.univ.erase i,
            (Polynomial.C (d j) - Polynomial.X).natDegree :=
          Polynomial.natDegree_prod_le _ _
    _ = n - 1 := by simp [p34_factor_natDegree]

private lemma p34_sum_natDegree_lt {n : ℕ} (hn : 0 < n)
    (d lambda : P34Vector n) :
    (∑ i, Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i).natDegree < n := by
  classical
  refine (Polynomial.natDegree_sum_le_of_forall_le (n := n - 1) Finset.univ
    (fun i => Polynomial.C (p34SecularWeight d lambda i) *
      p34DeletedCharacteristic d i) ?_).trans_lt (Nat.sub_lt hn (by omega))
  intro i hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans (p34_deleted_natDegree_le d i)

private lemma p34_eval_characteristic {n : ℕ} (v : P34Vector n) (x : ℝ) :
    Polynomial.eval x (p34Characteristic v) = ∏ i, (v i - x) := by
  simp [p34Characteristic, Polynomial.eval_prod]

private lemma p34_eval_deleted {n : ℕ} (d : P34Vector n)
    (i : Fin n) (x : ℝ) :
    Polynomial.eval x (p34DeletedCharacteristic d i) =
      ∏ j ∈ Finset.univ.erase i, (d j - x) := by
  simp [p34DeletedCharacteristic, Polynomial.eval_prod]

private lemma p34_eval_identity {n : ℕ} (d lambda : P34Vector n)
    (hd : StrictMono d) (i : Fin n) :
    Polynomial.eval (d i) (p34Characteristic lambda - p34Characteristic d) =
      Polynomial.eval (d i) (∑ j, Polynomial.C (p34SecularWeight d lambda j) *
        p34DeletedCharacteristic d j) := by
  classical
  have hden : (∏ j ∈ Finset.univ.erase i, (d j - d i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hd.injective.ne (Finset.ne_of_mem_erase hj))
  have hweight : p34SecularWeight d lambda i *
      (∏ j ∈ Finset.univ.erase i, (d j - d i)) =
        ∏ j : Fin n, (lambda j - d i) := by
    unfold p34SecularWeight
    exact div_mul_cancel₀ _ hden
  have hdiag : Polynomial.eval (d i) (p34Characteristic d) = 0 := by
    rw [p34_eval_characteristic]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self (d i))
  have hother (j : Fin n) (hji : j ≠ i) :
      Polynomial.eval (d i) (p34DeletedCharacteristic d j) = 0 := by
    rw [p34_eval_deleted]
    exact Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨hji.symm, Finset.mem_univ i⟩) (sub_self (d i))
  rw [Polynomial.eval_sub, hdiag, sub_zero, p34_eval_characteristic,
    Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_eq_single i]
  · rw [p34_eval_deleted]
    exact hweight.symm
  · intro j hj hji
    simp [hother j hji]
  · simp

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
  · have hpoly : p34Characteristic lambda - p34Characteristic d =
        ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
          p34DeletedCharacteristic d i := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
        (f := d) (hf := hd.injective)
      · exact p34_eval_identity d lambda hd
      · simpa using max_lt (p34_characteristic_sub_natDegree_lt hn d lambda)
          (p34_sum_natDegree_lt hn d lambda)
    calc
      p34Characteristic lambda =
          (p34Characteristic lambda - p34Characteristic d) +
            p34Characteristic d := by ring
      _ = p34Characteristic d +
          ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
            p34DeletedCharacteristic d i := by rw [hpoly]; ring

end VSCLReuse

import VSCLReuse.P32.Definitions

namespace VSCLReuse

private theorem p32Coeff_of_le (m : ℕ) (A : Fin (m + 1) → ℝ)
    {k : ℕ} (hk : k ≤ m) :
    p32Coeff m A k = A ⟨k, by omega⟩ := by
  simp [p32Coeff, show k < m + 1 by omega]

private theorem p32Polynomial_range (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1),
        alpha ^ k * beta ^ (m - k) * p32Coeff m A k := by
  rw [p32Polynomial, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [p32Coeff, k.isLt]

private theorem p32Low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32Low m A alpha beta j =
      beta * p32Low m A alpha beta ⟨j.val + 1, hj⟩ +
        alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) := by
  unfold p32Low
  have hsize : m - j.val = (m - (j.val + 1)) + 1 := by omega
  rw [hsize, Finset.sum_range_succ]
  have hexp : m - (j.val + 1) + 1 - 1 = m - j.val - 1 := by omega
  simp only [hexp]
  have htail :
      (∑ k ∈ Finset.range (m - (j.val + 1)),
        alpha ^ k * beta ^ (m - j.val - 1 - k) * p32Coeff m A k) =
      beta * ∑ k ∈ Finset.range (m - (j.val + 1)),
        alpha ^ k * beta ^ (m - (j.val + 1) - 1 - k) * p32Coeff m A k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : k < m - (j.val + 1) := Finset.mem_range.mp hk
    have he : m - j.val - 1 - k = (m - (j.val + 1) - 1 - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [htail]
  have hend : m - j.val - 1 - (m - (j.val + 1)) = 0 := by omega
  simp only [hend, pow_zero, mul_one]
  have he : m - (j.val + 1) = m - j.val - 1 := by omega
  rw [he]

private theorem p32High_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32High m A alpha beta ⟨j.val + 1, hj⟩ =
      beta ^ (j.val + 1) * p32Coeff m A (m - j.val - 1) +
        alpha * p32High m A alpha beta j := by
  unfold p32High
  rw [show (j.val + 1) + 1 = (j.val + 1) + 1 by rfl,
    Finset.sum_range_succ']
  have htail :
      (∑ q ∈ Finset.range (j.val + 1),
        alpha ^ (q + 1) * beta ^ (j.val + 1 - (q + 1)) *
          p32Coeff m A (m - (j.val + 1) + (q + 1))) =
      alpha * ∑ q ∈ Finset.range (j.val + 1),
        alpha ^ q * beta ^ (j.val - q) * p32Coeff m A (m - j.val + q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hqr : q < j.val + 1 := Finset.mem_range.mp hq
    have he : m - (j.val + 1) + (q + 1) = m - j.val + q := by omega
    have he' : j.val + 1 - (q + 1) = j.val - q := by omega
    rw [he, he', pow_succ]
    ring
  rw [htail]
  have he : m - (j.val + 1) = m - j.val - 1 := by omega
  simp only [pow_zero, one_mul, he]
  simp only [Nat.sub_zero, Nat.add_zero]
  ring

private theorem p32Polynomial_split (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) :
    p32Polynomial m A alpha beta =
      beta ^ (j.val + 1) * p32Low m A alpha beta j +
        alpha ^ (m - j.val) * p32High m A alpha beta j := by
  have hm : m + 1 = (m - j.val) + (j.val + 1) := by omega
  rw [p32Polynomial_range, hm, Finset.sum_range_add]
  unfold p32Low p32High
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkr : k < m - j.val := Finset.mem_range.mp hk
    have he : (j.val + 1) + (m - j.val - 1 - k) = m - k := by omega
    rw [← he, pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro q hq
    have hqr : q < j.val + 1 := Finset.mem_range.mp hq
    have he : m - (m - j.val + q) = j.val - q := by omega
    rw [he, pow_add]
    ring

private theorem p32MatMul_companion_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (E : P32Matrix m) (i j : Fin m) :
    p32MatMul E (p32FirstCompanion m hm A alpha beta) i j =
      E i ⟨0, hm⟩ *
        (if j.val = 0 then
          alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
        else beta * A ⟨m - 1 - j.val, by omega⟩) +
      (if hj : j.val + 1 < m then
        -(beta * E i ⟨j.val + 1, hj⟩)
       else 0) +
      (if j.val = 0 then 0 else alpha * E i j) := by
  classical
  by_cases hn : j.val + 1 < m
  · let l : Fin m := ⟨j.val + 1, hn⟩
    have hlnz : l.val ≠ 0 := by simp [l]
    have hlj : l ≠ j := by simp [l, Fin.ext_iff]
    have h0l : (⟨0, hm⟩ : Fin m) ≠ l := by simp [l, Fin.ext_iff]
    have h0j : j.val = 0 ↔ j = ⟨0, hm⟩ := by simp [Fin.ext_iff]
    calc
      _ = ∑ k : Fin m,
          ((if k = (⟨0, hm⟩ : Fin m) then
              E i k * (if j.val = 0 then
                alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
                else beta * A ⟨m - 1 - j.val, by omega⟩) else 0) +
           (if k = l then -(beta * E i k) else 0) +
           (if j.val = 0 then 0 else if k = j then alpha * E i k else 0)) := by
            unfold p32MatMul
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = (⟨0, hm⟩ : Fin m)
            · have hkv : k.val = 0 := by simpa [Fin.ext_iff] using hk0
              subst k
              by_cases hj0 : j.val = 0
              · have hkj : (⟨0, hm⟩ : Fin m) = j := (h0j.mp hj0).symm
                have hjl : j ≠ l := by
                  intro h
                  exact h0l (hkj.trans h)
                simp [p32FirstCompanion, hj0, hkj, hjl]
              · have hkj : (⟨0, hm⟩ : Fin m) ≠ j := by
                  intro h
                  exact hj0 ((h0j.mpr h.symm))
                simp [p32FirstCompanion, hj0, hkj, h0l]
            · have hkv : k.val ≠ 0 := by
                intro h
                apply hk0
                exact Fin.ext h
              by_cases hkl : k = l
              · have hks : k.val = j.val + 1 := by simpa [l, Fin.ext_iff] using hkl
                subst k
                simp [p32FirstCompanion, l, hlj]
                ring
              · have hks : k.val ≠ j.val + 1 := by
                  intro h
                  apply hkl
                  exact Fin.ext h
                by_cases hkj : k = j
                · have hjpos : j.val ≠ 0 := by
                    intro h
                    apply hk0
                    exact hkj.trans (Fin.ext h)
                  have hj0 : j ≠ (⟨0, hm⟩ : Fin m) := by
                    intro h
                    exact hjpos (congrArg Fin.val h)
                  have hjl : j ≠ l := Ne.symm hlj
                  simp [p32FirstCompanion, hkj, hjpos, hj0, hjl]
                  ring
                · simp [p32FirstCompanion, hkv, hks, hkj, hk0, hkl]
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp [l, hn]
  · calc
      _ = ∑ k : Fin m,
          ((if k = (⟨0, hm⟩ : Fin m) then
              E i k * (if j.val = 0 then
                alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
                else beta * A ⟨m - 1 - j.val, by omega⟩) else 0) +
           (if j.val = 0 then 0 else if k = j then alpha * E i k else 0)) := by
            unfold p32MatMul
            apply Finset.sum_congr rfl
            intro k hk
            by_cases hk0 : k = (⟨0, hm⟩ : Fin m)
            · have hkv : k.val = 0 := by simpa [Fin.ext_iff] using hk0
              subst k
              by_cases hj0 : j.val = 0
              · have hkj : (⟨0, hm⟩ : Fin m) = j := Fin.ext hj0.symm
                simp [p32FirstCompanion, hj0, hkj]
              · have hkj : (⟨0, hm⟩ : Fin m) ≠ j := by
                  intro h
                  exact hj0 (congrArg Fin.val h).symm
                simp [p32FirstCompanion, hj0, hkj]
            · have hkv : k.val ≠ 0 := by
                intro h
                apply hk0
                exact Fin.ext h
              have hks : k.val ≠ j.val + 1 := by omega
              by_cases hkj : k = j
              · have hjpos : j.val ≠ 0 := by
                    intro h
                    apply hk0
                    exact hkj.trans (Fin.ext h)
                have hj0 : j ≠ (⟨0, hm⟩ : Fin m) := by
                  intro h
                  exact hjpos (congrArg Fin.val h)
                simp [p32FirstCompanion, hkj, hjpos, hj0]
                ring
              · simp [p32FirstCompanion, hkv, hks, hkj, hk0]
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        simp [hn]

private theorem p32Multiplier_zero (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (hm : 0 < m) (i : Fin m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ =
      alpha ^ (m - i.val - 1) * beta ^ i.val := by
  simp [p32Multiplier]

private theorem p32Multiplier_low (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : 0 < j.val) (hij : i.val < j.val) :
    p32Multiplier m A alpha beta i j =
      -(alpha ^ (j.val - i.val - 1) * beta ^ (i.val + 1) *
          p32Low m A alpha beta j) := by
  simp [p32Multiplier, Nat.ne_of_gt hj, hij]

private theorem p32Multiplier_high (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : 0 < j.val) (hji : j.val ≤ i.val) :
    p32Multiplier m A alpha beta i j =
      alpha ^ (m - i.val - 1) * beta ^ (i.val - j.val) *
        p32High m A alpha beta j := by
  simp [p32Multiplier, Nat.ne_of_gt hj, show ¬i.val < j.val by omega]

private theorem p32High_zero (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (hm : 0 < m) :
    p32High m A alpha beta ⟨0, hm⟩ = p32Coeff m A m := by
  simp [p32High]

private theorem p32Low_last (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 = m) :
    p32Low m A alpha beta j = p32Coeff m A 0 := by
  unfold p32Low
  have h : m - j.val = 1 := by omega
  rw [h]
  simp

private theorem p32Multiplier_first_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (alpha * p32Coeff m A m + beta * p32Coeff m A (m - 1)) +
      (if h : 1 < m then
        -(beta * p32Multiplier m A alpha beta i ⟨1, h⟩)
       else 0) =
      if i = ⟨0, hm⟩ then p32Polynomial m A alpha beta else 0 := by
  classical
  by_cases hn : 1 < m
  · rw [dif_pos hn]
    let z : Fin m := ⟨0, hm⟩
    let o : Fin m := ⟨1, hn⟩
    have hP := p32Polynomial_split m A alpha beta z
    have hL := p32Low_step m A alpha beta z hn
    have hH := p32High_zero m A alpha beta hm
    by_cases hi : i = z
    · subst i
      rw [if_pos rfl]
      rw [p32Multiplier_zero, p32Multiplier_low _ _ _ _ z o (by simp [o]) (by simp [z, o])]
      dsimp [z, o] at hP hL hH ⊢
      rw [hP, hL, hH]
      simp only [pow_zero, mul_one]
      have hpow : m - 1 - 1 + 1 = m - 1 := by omega
      rw [← hpow, pow_succ]
      have hp : alpha ^ m = alpha ^ 2 * alpha ^ (m - 1 - 1) := by
        calc
          alpha ^ m = alpha ^ (2 + (m - 1 - 1)) := by congr 1; omega
          _ = alpha ^ 2 * alpha ^ (m - 1 - 1) := by rw [pow_add]
      rw [hp]
      ring
    · have hipos : 0 < i.val := by
        have : i.val ≠ 0 := by
          intro h
          exact hi (Fin.ext h)
        omega
      rw [if_neg hi]
      rw [p32Multiplier_zero, p32Multiplier_high _ _ _ _ i o (by simp [o])
        (by simp [o]; omega)]
      dsimp [o]
      have hH1 := p32High_step m A alpha beta z hn
      dsimp [z] at hH1
      rw [hH1, hH]
      have hpow : beta ^ i.val = beta ^ (i.val - 1) * beta := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      ring
  · have hm1 : m = 1 := by omega
    subst m
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    simp [p32Multiplier, p32Polynomial, p32Coeff, Fin.sum_univ_succ]
    ring

private theorem p32Multiplier_middle_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i j : Fin m)
    (hj : 0 < j.val) (hn : j.val + 1 < m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * p32Coeff m A (m - j.val - 1)) -
      beta * p32Multiplier m A alpha beta i ⟨j.val + 1, hn⟩ +
      alpha * p32Multiplier m A alpha beta i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  classical
  let t : Fin m := ⟨j.val + 1, hn⟩
  have htpos : 0 < t.val := by simp [t]
  have hL := p32Low_step m A alpha beta j hn
  have hH := p32High_step m A alpha beta j hn
  by_cases hij : i.val < j.val
  · have hit : i.val < t.val := by simp [t]; omega
    have hne : i ≠ j := by intro h; exact Nat.lt_irrefl _ (h ▸ hij)
    rw [if_neg hne, p32Multiplier_zero,
      p32Multiplier_low _ _ _ _ i j hj hij,
      p32Multiplier_low _ _ _ _ i t htpos hit]
    dsimp [t] at hL ⊢
    rw [hL]
    have he1 : j.val + 1 - i.val - 1 = (j.val - i.val - 1) + 1 := by omega
    rw [he1, pow_succ]
    have ha : alpha ^ (m - i.val - 1) =
        alpha ^ (j.val - i.val - 1) * alpha ^ (m - j.val - 1) * alpha := by
      calc
        alpha ^ (m - i.val - 1) =
            alpha ^ ((j.val - i.val - 1) + (m - j.val - 1) + 1) := by
              congr 1; omega
        _ = _ := by rw [pow_add, pow_succ]; ring
    rw [ha]
    ring
  · by_cases hji : j.val = i.val
    · have hieq : i = j := Fin.ext hji.symm
      subst i
      rw [if_pos rfl, p32Multiplier_zero,
        p32Multiplier_low _ _ _ _ j t htpos (by simp [t]),
        p32Multiplier_high _ _ _ _ j j hj (by omega)]
      dsimp [t] at hH ⊢
      rw [p32Polynomial_split m A alpha beta t, hH]
      dsimp [t]
      have he1 : j.val + 1 - j.val - 1 = 0 := by omega
      have he2 : j.val - j.val = 0 := by omega
      have he3 : m - (j.val + 1) = m - j.val - 1 := by omega
      have he4 : j.val + 1 + 1 = j.val + 2 := by omega
      rw [he1, he2, he3, he4]
      simp only [pow_zero, one_mul]
      have hb : beta ^ (j.val + 2) = beta ^ j.val * beta * beta := by
        rw [show j.val + 2 = (j.val + 1) + 1 by omega, pow_succ, pow_succ]
      rw [hb, pow_succ beta j.val]
      ring
    · have hjlt : j.val < i.val := by omega
      have htlei : t.val ≤ i.val := by simp [t]; omega
      have hne : i ≠ j := by intro h; exact hji (congrArg Fin.val h).symm
      rw [if_neg hne, p32Multiplier_zero,
        p32Multiplier_high _ _ _ _ i j hj (by omega),
        p32Multiplier_high _ _ _ _ i t htpos htlei]
      dsimp [t] at hH ⊢
      rw [hH]
      have hb1 : beta ^ i.val =
          beta ^ (i.val - j.val - 1) * beta ^ (j.val + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hb2 : beta ^ (i.val - j.val) =
          beta ^ (i.val - j.val - 1) * beta := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hb1, hb2]
      have he : i.val - (j.val + 1) = i.val - j.val - 1 := by omega
      rw [he]
      ring

private theorem p32Multiplier_last_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i j : Fin m)
    (hj : 0 < j.val) (hn : ¬j.val + 1 < m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * p32Coeff m A (m - j.val - 1)) +
      alpha * p32Multiplier m A alpha beta i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  classical
  have hlast : j.val + 1 = m := by omega
  have hcoeff : m - j.val - 1 = 0 := by omega
  by_cases hij : i.val < j.val
  · have hne : i ≠ j := by intro h; exact Nat.lt_irrefl _ (h ▸ hij)
    rw [if_neg hne, p32Multiplier_zero,
      p32Multiplier_low _ _ _ _ i j hj hij, hcoeff]
    rw [p32Low_last m A alpha beta j hlast]
    have ha : alpha ^ (m - i.val - 1) =
        alpha ^ (j.val - i.val - 1) * alpha := by
      rw [← pow_succ]
      congr 1
      omega
    rw [ha, pow_succ]
    ring
  · have hieq : i = j := Fin.ext (by omega)
    subst i
    rw [if_pos rfl, p32Multiplier_zero,
      p32Multiplier_high _ _ _ _ j j hj (by omega), hcoeff]
    rw [p32Polynomial_split m A alpha beta j,
      p32Low_last m A alpha beta j hlast]
    have he : m - j.val = 1 := by omega
    rw [he]
    simp only [pow_one, pow_zero, one_mul, Nat.sub_self]
    rw [pow_succ]
    ring

/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  funext i j
  rw [p32MatMul_companion_column]
  have htop :
      (if j.val = 0 then
        alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
       else beta * A ⟨m - 1 - j.val, by omega⟩) =
      (if j.val = 0 then
        alpha * p32Coeff m A m + beta * p32Coeff m A (m - 1)
       else beta * p32Coeff m A (m - j.val - 1)) := by
    by_cases hj0 : j.val = 0
    · simp only [if_pos hj0]
      rw [p32Coeff_of_le m A (show m ≤ m by omega),
        p32Coeff_of_le m A (show m - 1 ≤ m by omega)]
    · simp only [if_neg hj0]
      rw [p32Coeff_of_le m A (show m - j.val - 1 ≤ m by omega)]
      congr 1
      exact congrArg A (Fin.ext (by simp only []; omega))
  rw [htop]
  by_cases hj0 : j.val = 0
  · have hjeq : j = ⟨0, hm⟩ := Fin.ext hj0
    subst j
    simpa using
      (p32Multiplier_first_column m hm A alpha beta i)
  · by_cases hn : j.val + 1 < m
    · rw [if_neg hj0, dif_pos hn, if_neg hj0]
      simpa only [sub_eq_add_neg, add_assoc] using
        (p32Multiplier_middle_column m hm A alpha beta i j (by omega) hn)
    · rw [if_neg hj0, dif_neg hn, if_neg hj0]
      simpa only [add_zero] using
        (p32Multiplier_last_column m hm A alpha beta i j (by omega) hn)

end VSCLReuse

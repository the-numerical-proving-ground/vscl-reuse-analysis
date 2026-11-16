import VSCLReuse.P32.Definitions

namespace VSCLReuse

private lemma p32_low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : ℕ) (hj : j + 1 < m) :
    p32Low m A alpha beta ⟨j, by omega⟩ =
      beta * p32Low m A alpha beta ⟨j + 1, hj⟩ +
        alpha ^ (m - j - 1) * p32Coeff m A (m - j - 1) := by
  have hdiff : m - j = (m - (j + 1)) + 1 := by omega
  rw [p32Low, p32Low, hdiff, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right]
  have hsum :
      (∑ k ∈ Finset.range (m - (j + 1)),
          alpha ^ k * beta ^ (m - (j + 1) - k) * p32Coeff m A k) =
        beta * (∑ k ∈ Finset.range (m - (j + 1)),
          alpha ^ k * beta ^ (m - (j + 1) - 1 - k) * p32Coeff m A k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m - (j + 1) := Finset.mem_range.mp hk
    have he : m - (j + 1) - k = (m - (j + 1) - 1 - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [hsum]
  have he : m - (j + 1) - (m - (j + 1)) = 0 := by omega
  have he' : m - (j + 1) = m - j - 1 := by omega
  simp [he']

private lemma p32_high_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : ℕ) (hj : j + 1 < m) :
    p32High m A alpha beta ⟨j + 1, hj⟩ =
      beta ^ (j + 1) * p32Coeff m A (m - j - 1) +
        alpha * p32High m A alpha beta ⟨j, by omega⟩ := by
  rw [p32High, p32High, Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  have hsum :
      (∑ q ∈ Finset.range (j + 1),
        alpha ^ (q + 1) * beta ^ (j + 1 - (q + 1)) *
          p32Coeff m A (m - (j + 1) + (q + 1))) =
        alpha * (∑ q ∈ Finset.range (j + 1),
          alpha ^ q * beta ^ (j - q) * p32Coeff m A (m - j + q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q < j + 1 := Finset.mem_range.mp hq
    have he : j + 1 - (q + 1) = j - q := by omega
    have he' : m - (j + 1) + (q + 1) = m - j + q := by omega
    rw [he, he', pow_succ]
    ring
  rw [hsum]
  simp only [Nat.sub_zero, Nat.add_zero]
  have he : m - (j + 1) = m - j - 1 := by omega
  rw [he]
  ring

private lemma p32_polynomial_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      beta * p32Low m A alpha beta ⟨0, hm⟩ +
        alpha ^ m * p32High m A alpha beta ⟨0, hm⟩ := by
  have hpol : p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1), p32Term m A alpha beta k := by
    unfold p32Polynomial
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k.val < m + 1 := k.isLt
    simp [p32Term, p32Coeff, hk']
  rw [hpol, Finset.sum_range_succ]
  simp only [p32Low, p32High]
  simp only [Nat.sub_zero]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have he : m - k = (m - 1 - k) + 1 := by omega
    rw [p32Term, he, pow_succ]
    ring
  · simp [p32Term, p32Coeff]

private lemma p32_polynomial_split (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (j : Fin m) :
    p32Polynomial m A alpha beta =
      beta ^ (j.val + 1) * p32Low m A alpha beta j +
        alpha ^ (m - j.val) * p32High m A alpha beta j := by
  have haux : ∀ n (hn : n < m),
      p32Polynomial m A alpha beta =
        beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hn⟩ +
          alpha ^ (m - n) * p32High m A alpha beta ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn
      simpa using p32_polynomial_zero m hm A alpha beta
    | succ n ih =>
      intro hn
      have hn' : n < m := by omega
      have hlow := p32_low_step m A alpha beta n hn
      have hhigh := p32_high_step m A alpha beta n hn
      have hpow : m - n = (m - (n + 1)) + 1 := by omega
      have hpow' : m - n - 1 = m - (n + 1) := by omega
      calc
        p32Polynomial m A alpha beta =
            beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hn'⟩ +
              alpha ^ (m - n) * p32High m A alpha beta ⟨n, hn'⟩ := ih hn'
        _ = beta ^ (n + 1 + 1) * p32Low m A alpha beta ⟨n + 1, hn⟩ +
              alpha ^ (m - (n + 1)) * p32High m A alpha beta ⟨n + 1, hn⟩ := by
          rw [hlow, hhigh, hpow', hpow, pow_succ, pow_succ]
          ring
  exact haux j.val j.isLt

private lemma p32_companion_sparse (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (k j : Fin m) :
    p32FirstCompanion m hm A alpha beta k j =
      (if k.val = 0 then p32FirstCompanion m hm A alpha beta ⟨0, hm⟩ j else 0) +
      (if k.val = j.val + 1 then -beta else 0) +
      (if j.val = 0 then 0 else if k = j then alpha else 0) := by
  by_cases hk0 : k.val = 0
  · have hk : k = ⟨0, hm⟩ := Fin.ext hk0
    subst k
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · have hne : (⟨0, hm⟩ : Fin m) ≠ j := by
        intro h
        exact hj0 (by simpa using congrArg Fin.val h.symm)
      simp [hj0, hne]
  · by_cases hsub : k.val = j.val + 1
    · have hkj : k ≠ j := by
        intro h
        have : k.val = j.val := congrArg Fin.val h
        omega
      simp [p32FirstCompanion, hsub, hkj]
    · by_cases hkj : k = j
      · have hj0 : j.val ≠ 0 := by intro h; exact hk0 (hkj ▸ h)
        simp [p32FirstCompanion, hkj, hj0]
      · simp [p32FirstCompanion, hk0, hsub, hkj]

private lemma p32_sum_fin_val_ite (m n : ℕ) (F : Fin m → ℝ) :
    (∑ k : Fin m, if k.val = n then F k else 0) =
      if hn : n < m then F ⟨n, hn⟩ else 0 := by
  by_cases hn : n < m
  · have he : ∀ k : Fin m, (k.val = n) = (k = ⟨n, hn⟩) := by
      intro k
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
    simp_rw [he]
    simp [hn]
  · have he : ∀ k : Fin m, k.val ≠ n := by
      intro k h
      exact hn (h ▸ k.isLt)
    simp [hn, he]

private lemma p32_matmul_sparse (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (F : Fin m → ℝ) (j : Fin m) :
    (∑ k : Fin m, F k * p32FirstCompanion m hm A alpha beta k j) =
      F ⟨0, hm⟩ * p32FirstCompanion m hm A alpha beta ⟨0, hm⟩ j +
        (if h : j.val + 1 < m then F ⟨j.val + 1, h⟩ * (-beta) else 0) +
        (if j.val = 0 then 0 else F j * alpha) := by
  calc
    (∑ k : Fin m, F k * p32FirstCompanion m hm A alpha beta k j) =
        ∑ k : Fin m,
          ((if k.val = 0 then F k * p32FirstCompanion m hm A alpha beta ⟨0, hm⟩ j else 0) +
            (if k.val = j.val + 1 then F k * (-beta) else 0) +
            (if j.val = 0 then 0 else if k = j then F k * alpha else 0)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [p32_companion_sparse]
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [p32_sum_fin_val_ite m 0, p32_sum_fin_val_ite m (j.val + 1)]
      simp only [hm, dif_pos]
      by_cases hj0 : j.val = 0
      · simp [hj0]
      · simp [hj0]

private lemma p32_high_one (m : ℕ) (hm : 1 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32High m A alpha beta ⟨1, hm⟩ =
      alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩ := by
  rw [p32_high_step m A alpha beta 0 hm]
  simp [p32High, p32Coeff]
  ring

private lemma p32_first_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i ⟨0, hm⟩ =
      if i.val = 0 then p32Polynomial m A alpha beta else 0 := by
  by_cases h1 : m = 1
  · subst m
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [p32MatMul, p32Multiplier, p32FirstCompanion,
      p32Polynomial, Fin.sum_univ_succ]
    ring
  · have hm2 : 1 < m := by omega
    change (∑ k : Fin m, p32Multiplier m A alpha beta i k *
      p32FirstCompanion m hm A alpha beta k ⟨0, hm⟩) = _
    rw [p32_matmul_sparse]
    simp only [zero_add, hm2, dif_pos]
    by_cases hi0 : i.val = 0
    · have hi : i = ⟨0, hm⟩ := Fin.ext hi0
      subst i
      simp [p32Multiplier, p32FirstCompanion]
      rw [← p32_high_one m hm2 A alpha beta]
      have hpoly := p32_polynomial_split m hm A alpha beta (⟨1, hm2⟩ : Fin m)
      convert hpoly.symm using 1; ring
    · simp [p32Multiplier, p32FirstCompanion, hi0]
      rw [← p32_high_one m hm2 A alpha beta]
      have hpow : beta ^ i.val = beta ^ (i.val - 1) * beta := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpow]
      ring

private lemma p32_top_other (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (j : Fin m) (hj0 : j.val ≠ 0) :
    p32FirstCompanion m hm A alpha beta ⟨0, hm⟩ j =
      beta * p32Coeff m A (m - j.val - 1) := by
  have hidx : m - j.val - 1 = m - 1 - j.val := by omega
  rw [hidx]
  have hlt : m - 1 - j.val < m + 1 := by omega
  simp [p32FirstCompanion, p32Coeff, hj0, hlt]

private lemma p32_low_last (m : ℕ) (_hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (j : Fin m) (hj : ¬ j.val + 1 < m) :
    p32Low m A alpha beta j = p32Coeff m A 0 := by
  have hlast : m - j.val = 1 := by omega
  simp [p32Low, hlast]

private lemma p32_other_column (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj0 : j.val ≠ 0) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  change (∑ k : Fin m, p32Multiplier m A alpha beta i k *
    p32FirstCompanion m hm A alpha beta k j) = _
  rw [p32_matmul_sparse, p32_top_other m hm A alpha beta j hj0]
  simp only [hj0, if_false]
  by_cases hnext : j.val + 1 < m
  · simp only [hnext, dif_pos]
    by_cases hij : i.val < j.val
    · have hne : i ≠ j := by intro h; omega
      simp only [if_neg hne]
      have hij' : i.val < j.val + 1 := by omega
      simp [p32Multiplier, hj0, hij, hij']
      have hlow := p32_low_step m A alpha beta j.val hnext
      have he : j.val + 1 - i.val - 1 = j.val - i.val := by omega
      have hpow1 : alpha ^ (m - i.val - 1) =
          alpha ^ (j.val - i.val) * alpha ^ (m - j.val - 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow2 : alpha ^ (j.val - i.val) =
          alpha ^ (j.val - i.val - 1) * alpha := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hlow, he, hpow1, hpow2]
      ring
    · by_cases heq : i = j
      · subst i
        have hlt' : j.val < j.val + 1 := by omega
        simp [p32Multiplier, hj0, hlt']
        have hpoly := p32_polynomial_split m hm A alpha beta j
        rw [p32_low_step m A alpha beta j.val hnext] at hpoly
        have hpow : alpha ^ (m - j.val) =
            alpha ^ (m - j.val - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow] at hpoly
        convert hpoly.symm using 1; ring
      · simp only [if_neg heq]
        have hji : j.val < i.val := by
          have hne : i.val ≠ j.val := by intro h; exact heq (Fin.ext h)
          omega
        have hnot : ¬ i.val < j.val + 1 := by omega
        simp [p32Multiplier, hj0, hij, hnot]
        have hhigh := p32_high_step m A alpha beta j.val hnext
        have hpow1 : beta ^ i.val =
            beta ^ (i.val - (j.val + 1)) * beta ^ (j.val + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hpow2 : beta ^ (i.val - j.val) =
            beta ^ (i.val - (j.val + 1)) * beta := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hhigh, hpow1, hpow2]
        ring
  · simp only [hnext]
    by_cases hij : i.val < j.val
    · have hne : i ≠ j := by intro h; omega
      simp only [if_neg hne]
      simp [p32Multiplier, hj0, hij]
      rw [p32_low_last m hm A alpha beta j hnext]
      have hp : alpha ^ (m - i.val - 1) =
          alpha ^ (j.val - i.val - 1) * alpha := by
        rw [← pow_succ]
        congr 1
        omega
      have hzero : m - j.val - 1 = 0 := by omega
      rw [hp, hzero]
      ring
    · have heq : i = j := by apply Fin.ext; omega
      subst i
      simp [p32Multiplier, hj0]
      have hpoly := p32_polynomial_split m hm A alpha beta j
      rw [p32_low_last m hm A alpha beta j hnext] at hpoly
      have hpow : alpha ^ (m - j.val) =
          alpha ^ (m - j.val - 1) * alpha := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow, pow_succ] at hpoly
      have hzero : m - j.val - 1 = 0 := by omega
      rw [hzero] at hpoly ⊢
      simp only [pow_zero, one_mul] at hpoly ⊢
      convert hpoly.symm using 1; ring

/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  funext i j
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, hm⟩ := Fin.ext hj0
    subst j
    rw [p32_first_column]
    have he : (i = (⟨0, hm⟩ : Fin m)) ↔ i.val = 0 := by
      simp [Fin.ext_iff]
    simp [he]
  · exact p32_other_column m hm A alpha beta i j hj0

end VSCLReuse

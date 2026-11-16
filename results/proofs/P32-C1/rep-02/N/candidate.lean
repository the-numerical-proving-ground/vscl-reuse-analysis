import VSCLReuse.P32.Definitions

namespace VSCLReuse

private lemma p32_polynomial_range (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1), p32Term m A alpha beta k := by
  rw [p32Polynomial, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have h : k.val < m + 1 := k.isLt
  simp [p32Term, p32Coeff, h]

private lemma p32_polynomial_split (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) :
    p32Polynomial m A alpha beta =
      alpha ^ (m - j.val) * p32High m A alpha beta j +
      beta ^ (j.val + 1) * p32Low m A alpha beta j := by
  let d := m - j.val
  have hd : d + (j.val + 1) = m + 1 := by dsimp [d]; omega
  have hdpos : 0 < d := by dsimp [d]; omega
  rw [p32_polynomial_range, ← hd, Finset.sum_range_add]
  have hhigh :
      (∑ q ∈ Finset.range (j.val + 1), p32Term m A alpha beta (d + q)) =
        alpha ^ d * p32High m A alpha beta j := by
    simp only [p32High, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : q < j.val + 1 := Finset.mem_range.mp hq
    have h1 : d + q ≤ m := by dsimp [d] at *; omega
    have h2 : d + q < m + 1 := by omega
    have hp : m - (d + q) = j.val - q := by dsimp [d] at *; omega
    simp only [p32Term, hp]
    have he : d + q = m - j.val + q := rfl
    rw [he, pow_add]
    ring
  have hlow :
      (∑ k ∈ Finset.range d, p32Term m A alpha beta k) =
        beta ^ (j.val + 1) * p32Low m A alpha beta j := by
    simp only [p32Low, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < d := Finset.mem_range.mp hk
    have hp : m - k = (j.val + 1) + (d - 1 - k) := by dsimp [d] at *; omega
    simp only [p32Term, hp]
    rw [pow_add]
    ring
  rw [hhigh, hlow]
  ring

private lemma p32_low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32Low m A alpha beta j =
      alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) +
      beta * p32Low m A alpha beta ⟨j.val + 1, hj⟩ := by
  have hd : m - j.val = (m - j.val - 1) + 1 := by omega
  unfold p32Low
  rw [hd, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right]
  have hlast :
      alpha ^ (m - j.val - 1) * beta ^ (m - j.val - 1 - (m - j.val - 1)) *
        p32Coeff m A (m - j.val - 1) =
      alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) := by simp
  rw [hlast]
  conv_lhs => rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < m - j.val - 1 := Finset.mem_range.mp hk
  have he : m - j.val - 1 - k = 1 + (m - (j.val + 1) - 1 - k) := by omega
  rw [he, pow_add]
  ring

private lemma p32_high_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32High m A alpha beta ⟨j.val + 1, hj⟩ =
      beta ^ (j.val + 1) * p32Coeff m A (m - j.val - 1) +
      alpha * p32High m A alpha beta j := by
  unfold p32High
  change (∑ q ∈ Finset.range ((j.val + 1) + 1),
    alpha ^ q * beta ^ (j.val + 1 - q) *
      p32Coeff m A (m - (j.val + 1) + q)) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.add_zero, Nat.sub_zero]
  have he : m - (j.val + 1) = m - j.val - 1 := by omega
  rw [he, Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q < j.val + 1 := Finset.mem_range.mp hq
  have he1 : j.val + 1 - (q + 1) = j.val - q := by omega
  have he2 : m - j.val - 1 + (q + 1) = m - j.val + q := by omega
  rw [he1, he2, pow_succ]
  ring

private lemma p32_companion_entry (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (k j : Fin m) :
    p32FirstCompanion m hm A alpha beta k j =
      (if k.val = 0 then beta * p32Coeff m A (m - j.val - 1) else 0) +
      (if k = j then (if j.val = 0 then alpha * A ⟨m, by omega⟩ else alpha) else 0) +
      (if k.val = j.val + 1 then -beta else 0) := by
  by_cases hk : k.val = 0
  · by_cases hj : j.val = 0
    · have hkj : k = j := Fin.ext (by omega)
      have hs : k.val ≠ j.val + 1 := by omega
      simp [p32FirstCompanion, hj, hkj, p32Coeff]
      ring
    · have hkj : k ≠ j := by intro h; exact hj (congrArg Fin.val h ▸ hk)
      have hs : k.val ≠ j.val + 1 := by omega
      have hc : m - 1 - j.val = m - j.val - 1 := by omega
      have hlt : m - j.val - 1 < m + 1 := by omega
      simp [p32FirstCompanion, hk, hj, hkj, p32Coeff, hc, hlt]
  · by_cases hs : k.val = j.val + 1
    · have hkj : k ≠ j := by intro h; have := congrArg Fin.val h; omega
      simp [p32FirstCompanion, hs, hkj]
    · by_cases hkj : k = j
      · have hj : j.val ≠ 0 := by simpa [hkj] using hk
        simp [p32FirstCompanion, hkj, hj]
      · simp [p32FirstCompanion, hk, hs, hkj]

private lemma p32_product_entry (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i j : Fin m) :
    p32MatMul (p32Multiplier m A alpha beta)
      (p32FirstCompanion m hm A alpha beta) i j =
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * p32Coeff m A (m - j.val - 1)) +
      p32Multiplier m A alpha beta i j *
        (if j.val = 0 then alpha * A ⟨m, by omega⟩ else alpha) -
      (if hj : j.val + 1 < m then
        beta * p32Multiplier m A alpha beta i ⟨j.val + 1, hj⟩ else 0) := by
  simp only [p32MatMul, p32_companion_entry, mul_add, mul_ite, mul_zero,
    Finset.sum_add_distrib]
  have hzero :
      (∑ k : Fin m, if k.val = 0 then
          p32Multiplier m A alpha beta i k * (beta * p32Coeff m A (m - j.val - 1))
        else 0) =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * p32Coeff m A (m - j.val - 1)) := by
    refine Finset.sum_eq_single (⟨0, hm⟩ : Fin m) ?_ ?_
    · intro k hk hne
      have h : k.val ≠ 0 := by
        intro hv
        apply hne
        exact Fin.ext (by simpa using hv)
      simp [h]
    · simp
  have hdiag :
      (∑ k : Fin m, if k = j then
          (if j.val = 0 then
            p32Multiplier m A alpha beta i k * (alpha * A ⟨m, by omega⟩)
          else p32Multiplier m A alpha beta i k * alpha)
        else 0) =
      (if j.val = 0 then
        p32Multiplier m A alpha beta i j * (alpha * A ⟨m, by omega⟩)
       else p32Multiplier m A alpha beta i j * alpha) := by
    simp
  have hsub :
      (∑ k : Fin m, if k.val = j.val + 1 then
          p32Multiplier m A alpha beta i k * -beta else 0) =
      -(if hj : j.val + 1 < m then
        beta * p32Multiplier m A alpha beta i ⟨j.val + 1, hj⟩ else 0) := by
    split_ifs with hj
    · refine Finset.sum_eq_single ⟨j.val + 1, hj⟩ ?_ ?_ |>.trans ?_
      · intro k hk hne
        have h : k.val ≠ j.val + 1 := by
          intro hv
          apply hne
          exact Fin.ext (by simpa using hv)
        simp [h]
      · simp
      · simp; ring
    · have hall : ∀ k : Fin m, k.val ≠ j.val + 1 := by
        intro k hv
        have := k.isLt
        omega
      simp [hall]
  rw [hzero, hdiag, hsub]
  split_ifs <;> ring

private lemma p32_high_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32High m A alpha beta ⟨0, hm⟩ = A ⟨m, by omega⟩ := by
  simp [p32High, p32Coeff]

private lemma p32_low_last (m : ℕ)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (j : Fin m) (hj : j.val + 1 = m) :
    p32Low m A alpha beta j = p32Coeff m A 0 := by
  have h : m - j.val = 1 := by omega
  simp [p32Low, h]

/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  funext i j
  rw [p32_product_entry]
  by_cases hj0 : j.val = 0
  · have hj : j = ⟨0, hm⟩ := Fin.ext hj0
    subst j
    by_cases hn : 1 < m
    · by_cases hi0 : i.val = 0
      · have hi : i = ⟨0, hm⟩ := Fin.ext hi0
        subst i
        simp [p32Multiplier, hn]
        have hl := p32_low_step m A alpha beta (⟨0, hm⟩ : Fin m) hn
        simp only [Nat.sub_zero, zero_add] at hl
        have hp := p32_polynomial_split m A alpha beta (⟨0, hm⟩ : Fin m)
        simp only [Nat.sub_zero, zero_add, pow_one] at hp
        rw [p32_high_zero] at hp
        rw [hp, hl]
        have hpow : alpha ^ m = alpha ^ (m - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow]
        ring
      · simp [p32Multiplier, hn, hi0]
        have hine : i ≠ (⟨0, hm⟩ : Fin m) := by
          intro h
          apply hi0
          exact congrArg Fin.val h
        simp only [if_neg hine]
        have hh := p32_high_step m A alpha beta (⟨0, hm⟩ : Fin m) hn
        simp only [Nat.sub_zero, zero_add, pow_one] at hh
        rw [p32_high_zero] at hh
        rw [hh]
        have hpow : beta ^ i.val = beta ^ (i.val - 1) * beta := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow]
        ring
    · have hm1 : m = 1 := by omega
      subst m
      have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
      subst i
      simp [p32Multiplier, p32Polynomial, p32Coeff]
  · by_cases hn : j.val + 1 < m
    · rcases lt_trichotomy i.val j.val with hij | hij | hij
      · have hijN : i.val < j.val + 1 := by omega
        have hine : i ≠ j := by intro h; have := congrArg Fin.val h; omega
        simp [p32Multiplier, hj0, hn, hij, hijN, hine]
        have hl := p32_low_step m A alpha beta j hn
        have hpow1 : alpha ^ (m - i.val - 1) =
            alpha ^ (j.val - i.val - 1) * alpha ^ (m - j.val - 1) * alpha := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        have hpow2 : alpha ^ (j.val + 1 - i.val - 1) =
            alpha ^ (j.val - i.val - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow1, hpow2, hl, pow_succ beta i.val]
        ring
      · have hieq : i = j := Fin.ext hij
        subst i
        simp [p32Multiplier, hj0, hn]
        rw [p32_polynomial_split m A alpha beta j, p32_low_step m A alpha beta j hn]
        have hpow : alpha ^ (m - j.val) = alpha ^ (m - j.val - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow, pow_succ beta j.val]
        ring
      · have hijN : ¬ i.val < j.val + 1 := by omega
        have hij' : ¬ i.val < j.val := by omega
        have hine : i ≠ j := by intro h; have := congrArg Fin.val h; omega
        simp [p32Multiplier, hj0, hn, hij', hijN, hine]
        have hh := p32_high_step m A alpha beta j hn
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
        rw [hh, hpow1, hpow2]
        ring
    · rcases lt_trichotomy i.val j.val with hij | hij | hij
      · have hine : i ≠ j := by intro h; have := congrArg Fin.val h; omega
        simp [p32Multiplier, hj0, hn, hij, hine]
        have hjm : j.val + 1 = m := by omega
        rw [p32_low_last m A alpha beta j hjm]
        have hpow : alpha ^ (m - i.val - 1) =
            alpha ^ (j.val - i.val - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        rw [hpow, pow_succ beta i.val]
        have hz : m - j.val - 1 = 0 := by omega
        rw [hz]
        ring
      · have hieq : i = j := Fin.ext hij
        subst i
        simp [p32Multiplier, hj0, hn]
        have hjm : j.val + 1 = m := by omega
        rw [p32_polynomial_split m A alpha beta j,
          p32_low_last m A alpha beta j hjm]
        have hpow : alpha ^ (m - j.val) = alpha ^ (m - j.val - 1) * alpha := by
          rw [← pow_succ]
          congr 1
          omega
        have hz : m - j.val - 1 = 0 := by omega
        rw [hpow, pow_succ beta j.val, hz]
        ring
      · omega

end VSCLReuse

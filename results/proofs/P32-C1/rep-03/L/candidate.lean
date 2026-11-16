import VSCLReuse.P32.Definitions

namespace VSCLReuse

private lemma p32_poly_as_range (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1), p32Term m A alpha beta k := by
  have h : p32Polynomial m A alpha beta =
      ∑ k : Fin (m + 1), p32Term m A alpha beta k.val := by
    unfold p32Polynomial
    apply Finset.sum_congr rfl
    intro k hk
    simp [p32Term, p32Coeff, k.isLt]
  rw [h, Fin.sum_univ_eq_sum_range]

private lemma p32_low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32Low m A alpha beta j =
      beta * p32Low m A alpha beta ⟨j.val + 1, hj⟩ +
        alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) := by
  have hsub : m - j.val = (m - j.val - 1) + 1 := by omega
  rw [p32Low, hsub, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right, Nat.sub_self, pow_zero, mul_one]
  have hsum :
      (∑ k ∈ Finset.range (m - j.val - 1),
          alpha ^ k * beta ^ (m - j.val - 1 - k) * p32Coeff m A k) =
        beta * p32Low m A alpha beta ⟨j.val + 1, hj⟩ := by
    rw [p32Low, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m - j.val - 1 := Finset.mem_range.mp hk
    have he : m - j.val - 1 - k = (m - (j.val + 1) - 1 - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [hsum]

private lemma p32_high_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32High m A alpha beta ⟨j.val + 1, hj⟩ =
      beta ^ (j.val + 1) * p32Coeff m A (m - j.val - 1) +
        alpha * p32High m A alpha beta j := by
  rw [p32High, p32High]
  have hr : j.val + 1 + 1 = (j.val + 1) + 1 := by omega
  rw [hr, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero]
  have hindex : m - (j.val + 1) = m - j.val - 1 := by omega
  rw [hindex, add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q < j.val + 1 := Finset.mem_range.mp hq
  have he₁ : j.val + 1 - (q + 1) = j.val - q := by omega
  have he₂ : m - j.val - 1 + (q + 1) = m - j.val + q := by omega
  rw [he₁, he₂, pow_succ]
  ring

private lemma p32_poly_split_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      beta * p32Low m A alpha beta ⟨0, hm⟩ +
        alpha ^ m * p32High m A alpha beta ⟨0, hm⟩ := by
  rw [p32_poly_as_range, Finset.sum_range_succ]
  congr 1
  · rw [p32Low, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have he : m - k = (m - 0 - 1 - k) + 1 := by omega
    simp only [p32Term]
    rw [he, pow_succ]
    ring
  · simp [p32Term, p32High]

private lemma p32_poly_split (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (j : Fin m) :
    p32Polynomial m A alpha beta =
      alpha ^ (m - j.val) * p32High m A alpha beta j +
        beta ^ (j.val + 1) * p32Low m A alpha beta j := by
  have h (n : ℕ) : ∀ hn : n < m,
      p32Polynomial m A alpha beta =
        alpha ^ (m - n) * p32High m A alpha beta ⟨n, hn⟩ +
          beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hn⟩ := by
    induction n with
    | zero =>
        intro hn
        simpa [add_comm] using p32_poly_split_zero m hm A alpha beta
    | succ n ih =>
        intro hn
        have hn' : n < m := by omega
        have hnext : n + 1 < m := by omega
        have hlo := p32_low_step m A alpha beta ⟨n, hn'⟩ hnext
        have hhi := p32_high_step m A alpha beta ⟨n, hn'⟩ hnext
        have hexp : m - n = (m - (n + 1)) + 1 := by omega
        have he : m - n - 1 = m - (n + 1) := by omega
        rw [he] at hlo hhi
        calc
          p32Polynomial m A alpha beta =
              alpha ^ (m - n) * p32High m A alpha beta ⟨n, hn'⟩ +
                beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hn'⟩ := ih hn'
          _ = alpha ^ (m - (n + 1)) *
                p32High m A alpha beta ⟨n + 1, hnext⟩ +
              beta ^ (n + 1 + 1) *
                p32Low m A alpha beta ⟨n + 1, hnext⟩ := by
              rw [hlo, hhi, hexp, pow_succ, pow_succ]
              ring
  exact h j.val j.isLt

private lemma p32_companion_alt (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (k j : Fin m) :
    p32FirstCompanion m hm A alpha beta k j =
      (if k.val = 0 then
        if j.val = 0 then alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
        else beta * A ⟨m - 1 - j.val, by omega⟩
       else 0) +
      (if j.val = 0 then 0 else if k = j then alpha else 0) +
      (if k.val = j.val + 1 then -beta else 0) := by
  unfold p32FirstCompanion
  by_cases hk : k.val = 0
  · by_cases hj : j.val = 0
    · simp [hk, hj]
    · have hkj : k ≠ j := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hk, hj, hkj]
  · by_cases hs : k.val = j.val + 1
    · have hkj : k ≠ j := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [hs, hkj]
    · by_cases hkj : k = j
      · have hj : j.val ≠ 0 := by
          intro hj
          have := congrArg Fin.val hkj
          omega
        simp [hkj, hj]
      · simp [hk, hs, hkj]

private lemma p32_matmul_sparse (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i j : Fin m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (if j.val = 0 then alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
         else beta * A ⟨m - 1 - j.val, by omega⟩) +
      (if j.val = 0 then 0 else p32Multiplier m A alpha beta i j * alpha) +
      (if hn : j.val + 1 < m then
        p32Multiplier m A alpha beta i ⟨j.val + 1, hn⟩ * (-beta) else 0) := by
  let E := p32Multiplier m A alpha beta
  let top : ℝ := if j.val = 0 then
      alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
    else beta * A ⟨m - 1 - j.val, by omega⟩
  have h0 : (∑ k : Fin m, if k.val = 0 then E i k * top else 0) =
      E i ⟨0, hm⟩ * top := by
    have h : (∑ k : Fin m, if k.val = 0 then E i k * top else 0) =
        ∑ k : Fin m, if k = (⟨0, hm⟩ : Fin m) then E i k * top else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have he : k.val = 0 ↔ k = (⟨0, hm⟩ : Fin m) := by
        constructor
        · intro hv; exact Fin.ext hv
        · intro hv; exact congrArg Fin.val hv
      simp only [he]
    rw [h, Finset.sum_ite_eq']
    simp
  have hj : (∑ k : Fin m, if j.val = 0 then 0 else if k = j then E i k * alpha else 0) =
      if j.val = 0 then 0 else E i j * alpha := by
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp only [if_neg hj0, Finset.sum_ite_eq']
      simp
  have hn : (∑ k : Fin m, if k.val = j.val + 1 then E i k * (-beta) else 0) =
      if hnext : j.val + 1 < m then E i ⟨j.val + 1, hnext⟩ * (-beta) else 0 := by
    split_ifs with hnext
    · have h : (∑ k : Fin m, if k.val = j.val + 1 then E i k * (-beta) else 0) =
          ∑ k : Fin m, if k = (⟨j.val + 1, hnext⟩ : Fin m) then E i k * (-beta) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have he : k.val = j.val + 1 ↔ k = (⟨j.val + 1, hnext⟩ : Fin m) := by
          constructor
          · intro hv; exact Fin.ext hv
          · intro hv; exact congrArg Fin.val hv
        simp only [he]
      rw [h, Finset.sum_ite_eq']
      simp
    · apply Finset.sum_eq_zero
      intro k hk
      have hne : k.val ≠ j.val + 1 := by omega
      simp [hne]
  unfold p32MatMul
  calc
    (∑ k : Fin m, E i k * p32FirstCompanion m hm A alpha beta k j) =
        ∑ k : Fin m, (
          (if k.val = 0 then E i k * top else 0) +
          (if j.val = 0 then 0 else if k = j then E i k * alpha else 0) +
          (if k.val = j.val + 1 then E i k * (-beta) else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [p32_companion_alt]
        dsimp [top]
        split_ifs <;> ring
    _ = E i ⟨0, hm⟩ * top +
          (if j.val = 0 then 0 else E i j * alpha) +
          (if hnext : j.val + 1 < m then E i ⟨j.val + 1, hnext⟩ * (-beta) else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h0, hj, hn]

private lemma p32_matmul_sparse_coeff (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i j : Fin m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (if j.val = 0 then alpha * p32Coeff m A m + beta * p32Coeff m A (m - 1)
         else beta * p32Coeff m A (m - 1 - j.val)) +
      (if j.val = 0 then 0 else p32Multiplier m A alpha beta i j * alpha) +
      (if hn : j.val + 1 < m then
        p32Multiplier m A alpha beta i ⟨j.val + 1, hn⟩ * (-beta) else 0) := by
  have h₁ : m - 1 - j.val < m + 1 := by omega
  have h₂ : m - 1 < m + 1 := by omega
  have h₃ : m < m + 1 := by omega
  simpa [p32Coeff, h₁, h₂, h₃] using p32_matmul_sparse m hm A alpha beta i j

/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  funext i j
  rw [p32_matmul_sparse_coeff]
  by_cases hm1 : m = 1
  · subst m
    fin_cases i
    fin_cases j
    simp [p32Multiplier, p32Polynomial, p32Coeff]
    ring
  have hm2 : 1 < m := by omega
  by_cases hj0 : j.val = 0
  · have jeq : j = (⟨0, hm⟩ : Fin m) := Fin.ext hj0
    subst j
    by_cases hi0 : i.val = 0
    · have ieq : i = (⟨0, hm⟩ : Fin m) := Fin.ext hi0
      subst i
      simp [p32Multiplier, hm2]
      have hlo := p32_low_step m A alpha beta (⟨0, hm⟩ : Fin m) hm2
      have hpoly := p32_poly_split_zero m hm A alpha beta
      have hpow : alpha ^ m = alpha ^ (m - 1) * alpha := by
        conv_lhs => rw [show m = m - 1 + 1 by omega]
        rw [pow_succ]
      calc
        alpha ^ (m - 1) *
            (alpha * p32Coeff m A m + beta * p32Coeff m A (m - 1)) +
            beta * p32Low m A alpha beta ⟨1, hm2⟩ * beta =
          beta * p32Low m A alpha beta ⟨0, hm⟩ +
            alpha ^ m * p32High m A alpha beta ⟨0, hm⟩ := by
              rw [hlo, hpow]
              simp [p32High]
              ring
        _ = p32Polynomial m A alpha beta := hpoly.symm
    · have hnotlt : ¬ i.val < 1 := by omega
      have hne : i ≠ (⟨0, hm⟩ : Fin m) := by
        intro h
        have := congrArg Fin.val h
        omega
      simp [p32Multiplier, hm2, hnotlt, hne]
      have hhi := p32_high_step m A alpha beta (⟨0, hm⟩ : Fin m) hm2
      have hhigh0 : p32High m A alpha beta ⟨0, hm⟩ = p32Coeff m A m := by
        simp [p32High]
      rw [hhigh0] at hhi
      simp only [zero_add, pow_one, Nat.sub_zero] at hhi
      have hbeta : beta ^ i.val = beta ^ (i.val - 1) * beta := by
        conv_lhs => rw [show i.val = i.val - 1 + 1 by omega]
        rw [pow_succ]
      rw [hhi, hbeta]
      ring
  · by_cases hnext : j.val + 1 < m
    · by_cases hij : i.val < j.val
      · have hijnext : i.val < j.val + 1 := by omega
        have hne : i ≠ j := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [p32Multiplier, hj0, hnext, hij, hijnext, hne]
        have hlo := p32_low_step m A alpha beta j hnext
        have he₁ : m - 1 - j.val = m - j.val - 1 := by omega
        have he₂ : j.val + 1 - i.val - 1 = j.val - i.val := by omega
        have hp₁ : alpha ^ (j.val - i.val - 1) * alpha = alpha ^ (j.val - i.val) := by
          rw [← pow_succ]
          congr 1
          omega
        have hp₂ : alpha ^ (j.val - i.val) * alpha ^ (m - j.val - 1) =
            alpha ^ (m - i.val - 1) := by
          rw [← pow_add, show j.val - i.val + (m - j.val - 1) = m - i.val - 1 by omega]
        have hp₃ : beta ^ i.val * beta = beta ^ (i.val + 1) := by rw [pow_succ]
        rw [hlo, he₁, he₂]
        calc
          _ = (alpha ^ (m - i.val - 1) -
                 alpha ^ (j.val - i.val) * alpha ^ (m - j.val - 1)) *
                beta ^ (i.val + 1) * p32Coeff m A (m - j.val - 1) := by
              rw [← hp₃, ← hp₁]
              ring
          _ = 0 := by rw [hp₂]; ring
      · by_cases heq : i = j
        · subst i
          simp [p32Multiplier, hj0, hnext]
          have hlo := p32_low_step m A alpha beta j hnext
          have hpoly := p32_poly_split m hm A alpha beta j
          have he : m - 1 - j.val = m - j.val - 1 := by omega
          have hpalpha : alpha ^ (m - j.val - 1) * alpha = alpha ^ (m - j.val) := by
            rw [← pow_succ]
            congr 1
            omega
          have hpbeta : beta ^ j.val * beta = beta ^ (j.val + 1) := by rw [pow_succ]
          calc
            _ = alpha ^ (m - j.val) * p32High m A alpha beta j +
                  beta ^ (j.val + 1) * p32Low m A alpha beta j := by
                rw [hlo, he, ← hpalpha, ← hpbeta]
                ring
            _ = p32Polynomial m A alpha beta := hpoly.symm
        · have hgt : j.val < i.val := by
            have hvalne : i.val ≠ j.val := by
              intro h
              exact heq (Fin.ext h)
            omega
          have hnlt : ¬i.val < j.val + 1 := by omega
          have hi0 : i.val ≠ 0 := by omega
          simp [p32Multiplier, hj0, hnext, hij, hnlt, heq]
          have hhi := p32_high_step m A alpha beta j hnext
          have he : m - 1 - j.val = m - j.val - 1 := by omega
          have hp₁ : beta ^ (i.val - j.val) =
              beta ^ (i.val - (j.val + 1)) * beta := by
            calc
              beta ^ (i.val - j.val) = beta ^ (i.val - (j.val + 1) + 1) := by
                congr 1
                omega
              _ = beta ^ (i.val - (j.val + 1)) * beta := by rw [pow_succ]
          have hp₂ : beta ^ i.val =
              beta ^ (i.val - (j.val + 1)) * beta ^ (j.val + 1) := by
            rw [← pow_add, show i.val - (j.val + 1) + (j.val + 1) = i.val by omega]
          rw [hhi, he, hp₁, hp₂]
          ring
    · by_cases hij : i.val < j.val
      · have hne : i ≠ j := by
          intro h
          have := congrArg Fin.val h
          omega
        simp [p32Multiplier, hj0, hnext, hij, hne]
        have hlen : m - j.val = 1 := by omega
        have hlow : p32Low m A alpha beta j = p32Coeff m A 0 := by
          simp [p32Low, hlen]
        have hcoeff : m - 1 - j.val = 0 := by omega
        have hexp : m - i.val - 1 = j.val - i.val := by omega
        have hp₁ : alpha ^ (j.val - i.val - 1) * alpha = alpha ^ (j.val - i.val) := by
          rw [← pow_succ]
          congr 1
          omega
        have hp₂ : beta ^ i.val * beta = beta ^ (i.val + 1) := by rw [pow_succ]
        rw [hlow, hcoeff, hexp, ← hp₁, ← hp₂]
        ring
      · have heq : i = j := Fin.ext (by omega)
        subst i
        simp [p32Multiplier, hj0, hnext]
        have hlen : m - j.val = 1 := by omega
        have hlow : p32Low m A alpha beta j = p32Coeff m A 0 := by
          simp [p32Low, hlen]
        have hpoly := p32_poly_split m hm A alpha beta j
        have hcoeff : m - 1 - j.val = 0 := by omega
        have hzero : m - j.val - 1 = 0 := by omega
        have hpa : alpha ^ (m - j.val - 1) * alpha = alpha ^ (m - j.val) := by
          rw [← pow_succ]
          congr 1
          omega
        have hpb : beta ^ j.val * beta = beta ^ (j.val + 1) := by rw [pow_succ]
        calc
          _ = alpha ^ (m - j.val) * p32High m A alpha beta j +
                beta ^ (j.val + 1) * p32Low m A alpha beta j := by
              rw [hlow, hcoeff, ← hpa, ← hpb]
              simp only [hzero, pow_zero, one_mul]
              ring
          _ = p32Polynomial m A alpha beta := hpoly.symm

end VSCLReuse

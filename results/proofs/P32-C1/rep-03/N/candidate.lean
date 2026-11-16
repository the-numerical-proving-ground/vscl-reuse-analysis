import VSCLReuse.P32.Definitions

namespace VSCLReuse

private lemma p32_low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32Low m A alpha beta j =
      beta * p32Low m A alpha beta ⟨j.val + 1, hj⟩ +
        alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) := by
  let j' : Fin m := ⟨j.val + 1, hj⟩
  have hsub : m - j.val = (m - j.val - 1) + 1 := by omega
  rw [p32Low, hsub, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_right]
  have hsum :
      (∑ k ∈ Finset.range (m - j.val - 1),
        alpha ^ k * beta ^ (m - j.val - 1 - k) * p32Coeff m A k) =
      beta * p32Low m A alpha beta j' := by
    rw [p32Low, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m - j.val - 1 := Finset.mem_range.mp hk
    have hpow : m - j.val - 1 - k = (j'.val - j.val) + (m - j'.val - 1 - k) := by
      dsimp [j']; omega
    dsimp [j']
    have he : m - j.val - 1 - k = (m - (j.val + 1) - 1 - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [hsum]
  have hzero : m - j.val - 1 - (m - j.val - 1) = 0 := by omega
  simp only [hzero, pow_zero, mul_one]
  rfl

private lemma p32_high_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (hj : j.val + 1 < m) :
    p32High m A alpha beta ⟨j.val + 1, hj⟩ =
      beta ^ (j.val + 1) * p32Coeff m A (m - j.val - 1) +
        alpha * p32High m A alpha beta j := by
  rw [p32High]
  change (∑ q ∈ Finset.range ((j.val + 1) + 1),
      alpha ^ q * beta ^ (j.val + 1 - q) * p32Coeff m A (m - (j.val + 1) + q)) = _
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_zero]
  have hindex : m - (j.val + 1) = m - j.val - 1 := by omega
  rw [hindex]
  rw [add_comm (∑ k ∈ Finset.range (j.val + 1),
      alpha ^ (k + 1) * beta ^ (j.val + 1 - (k + 1)) *
        p32Coeff m A (m - j.val - 1 + (k + 1)))]
  congr 1
  rw [p32High, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' : q < j.val + 1 := Finset.mem_range.mp hq
  have he : j.val + 1 - (q + 1) = j.val - q := by omega
  have hi : m - j.val - 1 + (q + 1) = m - j.val + q := by omega
  rw [he, hi, pow_succ]
  ring

private lemma p32_poly_base (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      alpha ^ m * p32High m A alpha beta ⟨0, hm⟩ +
        beta * p32Low m A alpha beta ⟨0, hm⟩ := by
  have hpoly : p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1), p32Term m A alpha beta k := by
    rw [p32Polynomial, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp [p32Term, p32Coeff, k.isLt]
  rw [hpoly, Finset.sum_range_succ]
  have hlast : p32Term m A alpha beta m =
      alpha ^ m * p32High m A alpha beta ⟨0, hm⟩ := by
    simp [p32Term, p32High, p32Coeff]
  have hlow : (∑ k ∈ Finset.range m, p32Term m A alpha beta k) =
      beta * p32Low m A alpha beta ⟨0, hm⟩ := by
    rw [p32Low, Finset.mul_sum]
    simp only [Fin.val_zero, Nat.sub_zero, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have he : m - k = (m - 1 - k) + 1 := by omega
    simp only [p32Term]
    rw [he, pow_succ]
    ring
  rw [hlow, hlast]
  ring

private lemma p32_poly_split (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (j : Fin m) :
    p32Polynomial m A alpha beta =
      alpha ^ (m - j.val) * p32High m A alpha beta j +
        beta ^ (j.val + 1) * p32Low m A alpha beta j := by
  have hmain : ∀ n : ℕ, ∀ hn : n < m,
      p32Polynomial m A alpha beta =
        alpha ^ (m - n) * p32High m A alpha beta ⟨n, hn⟩ +
          beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa using p32_poly_base m hm A alpha beta
    | succ n ih =>
        intro hn
        have hp : n < m := by omega
        have hl := p32_low_step m A alpha beta ⟨n, hp⟩ hn
        have hh := p32_high_step m A alpha beta ⟨n, hp⟩ hn
        have he : m - n = (m - (n + 1)) + 1 := by omega
        have he2 : m - n - 1 = m - (n + 1) := by omega
        calc
          p32Polynomial m A alpha beta =
              alpha ^ (m - n) * p32High m A alpha beta ⟨n, hp⟩ +
                beta ^ (n + 1) * p32Low m A alpha beta ⟨n, hp⟩ := ih hp
          _ = alpha ^ (m - (n + 1)) *
                p32High m A alpha beta ⟨n + 1, hn⟩ +
              beta ^ (n + 1 + 1) *
                p32Low m A alpha beta ⟨n + 1, hn⟩ := by
              simp only [Fin.val_mk] at hl hh
              rw [hl, hh, he2, he, pow_succ, pow_succ]
              ring
  exact hmain j.val j.isLt

private lemma p32_mul_sparse (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (E : P32Matrix m) (i j : Fin m) :
    p32MatMul E (p32FirstCompanion m hm A alpha beta) i j =
      E i ⟨0, hm⟩ *
          (if j.val = 0 then
            alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
           else beta * A ⟨m - 1 - j.val, by omega⟩) +
        (if hj : j.val + 1 < m then -beta * E i ⟨j.val + 1, hj⟩ else 0) +
          (if j.val = 0 then 0 else alpha * E i j) := by
  let z : Fin m := ⟨0, hm⟩
  let head : ℝ := if j.val = 0 then
      alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩
    else beta * A ⟨m - 1 - j.val, by omega⟩
  have hentry (k : Fin m) :
      p32FirstCompanion m hm A alpha beta k j =
        (if k = z then head else 0) +
          (if k.val = j.val + 1 then -beta else 0) +
            (if k = j ∧ j.val ≠ 0 then alpha else 0) := by
    by_cases hk0 : k.val = 0
    · have hkz : k = z := Fin.ext hk0
      subst k
      by_cases hj0 : j.val = 0
      · simp [p32FirstCompanion, head, z, hj0]
      · have hne : z ≠ j := by
          intro h
          have : z.val = j.val := congrArg Fin.val h
          simp [z] at this
          exact hj0 this.symm
        simp [p32FirstCompanion, head, z, hj0, hne]
    · have hkz : k ≠ z := by
        intro h
        exact hk0 (congrArg Fin.val h)
      by_cases hs : k.val = j.val + 1
      · have hne : k ≠ j := by
          intro h
          have : k.val = j.val := congrArg Fin.val h
          omega
        simp [p32FirstCompanion, hk0, hkz, hs, hne]
      · by_cases heq : k = j
        · have hj0 : j.val ≠ 0 := by
            intro hj
            exact hk0 (heq ▸ hj)
          have hjz : j ≠ z := by
            intro h
            have : j.val = z.val := congrArg Fin.val h
            simp [z] at this
            exact hj0 this
          subst k
          simp [p32FirstCompanion, hj0, hjz, hs]
        · simp [p32FirstCompanion, hk0, hkz, hs, heq]
  unfold p32MatMul
  simp_rw [hentry, mul_add, Finset.sum_add_distrib]
  have hs0 : (∑ k : Fin m, E i k * if k = z then head else 0) = E i z * head := by
    simp [mul_ite]
  have hs1 : (∑ k : Fin m, E i k * if k.val = j.val + 1 then -beta else 0) =
      if hj : j.val + 1 < m then -beta * E i ⟨j.val + 1, hj⟩ else 0 := by
    split_ifs with hj
    · let s : Fin m := ⟨j.val + 1, hj⟩
      have hs (k : Fin m) : (k.val = j.val + 1) ↔ k = s := by
        constructor
        · intro h; exact Fin.ext h
        · intro h; exact congrArg Fin.val h
      simp_rw [hs]
      simp [mul_ite, s]
      ring
    · have hs (k : Fin m) : k.val ≠ j.val + 1 := by omega
      simp [hs]
  have hs2 : (∑ k : Fin m, E i k * if k = j ∧ j.val ≠ 0 then alpha else 0) =
      if j.val = 0 then 0 else alpha * E i j := by
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp [hj0, mul_ite]
      ring
  rw [hs0, hs1, hs2]

private lemma p32_high_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32High m A alpha beta ⟨0, hm⟩ = A ⟨m, by omega⟩ := by
  simp [p32High, p32Coeff]

private lemma p32_low_last (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) :
    p32Low m A alpha beta ⟨m - 1, by omega⟩ = A ⟨0, by omega⟩ := by
  have h : m - (m - 1) = 1 := by omega
  simp [p32Low, h, p32Coeff]

private lemma p32_e_first (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ =
      alpha ^ (m - i.val - 1) * beta ^ i.val := by
  simp [p32Multiplier]

private lemma p32_e_upper (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : j.val ≠ 0) (hij : i.val < j.val) :
    p32Multiplier m A alpha beta i j =
      -(alpha ^ (j.val - i.val - 1) * beta ^ (i.val + 1) *
          p32Low m A alpha beta j) := by
  simp [p32Multiplier, hj, hij]

private lemma p32_e_lower (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : j.val ≠ 0) (hij : j.val ≤ i.val) :
    p32Multiplier m A alpha beta i j =
      alpha ^ (m - i.val - 1) * beta ^ (i.val - j.val) *
        p32High m A alpha beta j := by
  have hnot : ¬i.val < j.val := by omega
  simp [p32Multiplier, hj, hnot]

private lemma p32_col_middle (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj0 : j.val ≠ 0) (hnext : j.val + 1 < m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * A ⟨m - 1 - j.val, by omega⟩) -
      beta * p32Multiplier m A alpha beta i ⟨j.val + 1, hnext⟩ +
        alpha * p32Multiplier m A alpha beta i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  let s : Fin m := ⟨j.val + 1, hnext⟩
  have hcoeff : p32Coeff m A (m - j.val - 1) =
      A ⟨m - 1 - j.val, by omega⟩ := by
    have he : m - j.val - 1 = m - 1 - j.val := by omega
    rw [he]
    simp [p32Coeff, show m - 1 - j.val < m + 1 by omega]
  have hl := p32_low_step m A alpha beta j hnext
  have hh := p32_high_step m A alpha beta j hnext
  have hp := p32_poly_split m hm A alpha beta j
  by_cases hlt : i.val < j.val
  · have hi : i ≠ j := by intro h; omega
    have hlt' : i.val < s.val := by dsimp [s]; omega
    rw [if_neg hi, p32_e_first, p32_e_upper m A alpha beta i s (by dsimp [s]; omega) hlt',
      p32_e_upper m A alpha beta i j hj0 hlt]
    simp only [Fin.val_mk, mul_neg, sub_neg, add_zero]
    rw [hl]
    dsimp [s]
    rw [← hcoeff]
    have e1 : m - i.val - 1 = (j.val - i.val - 1) + 1 + (m - j.val - 1) := by omega
    have e2 : j.val + 1 - i.val - 1 = (j.val - i.val - 1) + 1 := by omega
    rw [e1, e2, pow_add, pow_add, pow_succ, pow_succ]
    ring
  · by_cases heq : i = j
    · subst i
      rw [if_pos rfl, p32_e_first, p32_e_upper m A alpha beta j s (by dsimp [s]; omega)
        (by dsimp [s]; omega), p32_e_lower m A alpha beta j j hj0 (by omega)]
      simp only [Fin.val_mk, mul_neg, sub_neg, Nat.sub_self, pow_zero, one_mul]
      rw [hp, hl]
      dsimp [s]
      rw [← hcoeff]
      have e1 : m - j.val = (m - j.val - 1) + 1 := by omega
      rw [e1]
      have en : m - j.val - 1 + 1 - 1 = m - j.val - 1 := by omega
      rw [en]
      have ez : j.val + 1 - j.val - 1 = 0 := by omega
      simp only [ez, pow_zero, one_mul, pow_succ]
      ring
    · have hgt : j.val < i.val := by omega
      have hge : s.val ≤ i.val := by dsimp [s]; omega
      rw [if_neg heq, p32_e_first, p32_e_lower m A alpha beta i s
        (by dsimp [s]; omega) hge, p32_e_lower m A alpha beta i j hj0 (by omega)]
      rw [hh]
      dsimp [s]
      rw [← hcoeff]
      have hb1 : beta ^ i.val = beta ^ (i.val - j.val - 1) * beta ^ (j.val + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hb2 : beta ^ (i.val - j.val) = beta ^ (i.val - j.val - 1) * beta := by
        rw [← pow_succ]
        congr 1
        omega
      have e3 : i.val - (j.val + 1) = i.val - j.val - 1 := by omega
      rw [hb1, hb2, e3]
      ring

private lemma p32_col_last (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj0 : j.val ≠ 0) (hnext : ¬j.val + 1 < m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (beta * A ⟨m - 1 - j.val, by omega⟩) +
      alpha * p32Multiplier m A alpha beta i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  have hjlast : j.val = m - 1 := by omega
  have hja : A ⟨m - 1 - j.val, by omega⟩ = A ⟨0, by omega⟩ := by
    have hidx : m - 1 - j.val = 0 := by omega
    simp [hidx]
  have hlow : p32Low m A alpha beta j = A ⟨0, by omega⟩ := by
    have hje : j = ⟨m - 1, by omega⟩ := Fin.ext hjlast
    calc
      p32Low m A alpha beta j =
          p32Low m A alpha beta ⟨m - 1, by omega⟩ := congrArg _ hje
      _ = A ⟨0, by omega⟩ := p32_low_last m hm A alpha beta
  have hp := p32_poly_split m hm A alpha beta j
  by_cases hlt : i.val < j.val
  · have hi : i ≠ j := by intro h; omega
    rw [if_neg hi, p32_e_first, p32_e_upper m A alpha beta i j hj0 hlt,
      hja, hlow]
    have he : m - i.val - 1 = (j.val - i.val - 1) + 1 := by omega
    have hb : beta ^ i.val * beta = beta ^ (i.val + 1) := by rw [pow_succ]
    rw [he, pow_succ]
    ring
  · have heq : i = j := by
      apply Fin.ext
      have hi : i.val < m := i.isLt
      omega
    subst i
    rw [if_pos rfl, p32_e_first, p32_e_lower m A alpha beta j j hj0 (by omega),
      hja, hp, hlow]
    have h1 : m - j.val - 1 = 0 := by omega
    have h2 : m - j.val = 1 := by omega
    rw [h1, h2]
    simp only [pow_zero, pow_one, Nat.sub_self, one_mul]
    rw [pow_succ]
    ring

private lemma p32_col_first (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ *
        (alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩) +
      (if hnext : 1 < m then
        -beta * p32Multiplier m A alpha beta i ⟨1, hnext⟩ else 0) =
      if i = (⟨0, hm⟩ : Fin m) then p32Polynomial m A alpha beta else 0 := by
  by_cases hnext : 1 < m
  · simp only [dif_pos hnext]
    let s : Fin m := ⟨1, hnext⟩
    let z : Fin m := ⟨0, hm⟩
    have hl := p32_low_step m A alpha beta z hnext
    have hh := p32_high_step m A alpha beta z hnext
    have hp := p32_poly_base m hm A alpha beta
    have hz := p32_high_zero m hm A alpha beta
    have hl' : p32Low m A alpha beta z =
        beta * p32Low m A alpha beta s +
          alpha ^ (m - 1) * p32Coeff m A (m - 1) := by
      simpa [z, s] using hl
    have hh' : p32High m A alpha beta s =
        beta * p32Coeff m A (m - 1) +
          alpha * A ⟨m, by omega⟩ := by
      simpa [z, s, hz] using hh
    have hc1 : p32Coeff m A (m - 1) = A ⟨m - 1, by omega⟩ := by
      simp [p32Coeff, show m - 1 < m + 1 by omega]
    by_cases hi0 : i.val = 0
    · have hiz : i = z := Fin.ext hi0
      subst i
      rw [if_pos rfl, p32_e_first, p32_e_upper m A alpha beta z s
        (by dsimp [s]; omega) (by dsimp [s, z]; omega), hp, hz]
      dsimp [z, s]
      simp only [Nat.sub_zero, zero_add, pow_zero, one_mul]
      rw [hl', hc1]
      have ha : alpha ^ m = alpha ^ (m - 1) * alpha := by
        calc
          alpha ^ m = alpha ^ ((m - 1) + 1) := by congr 1; omega
          _ = alpha ^ (m - 1) * alpha := pow_succ _ _
      rw [ha]
      ring
    · have hiz : i ≠ z := by
        intro h
        exact hi0 (by simpa [z] using congrArg Fin.val h)
      have hge : s.val ≤ i.val := by dsimp [s]; omega
      rw [if_neg hiz, p32_e_first, p32_e_lower m A alpha beta i s
        (by dsimp [s]; omega) hge, hh', hc1]
      dsimp [z, s]
      have hb : beta ^ i.val = beta ^ (i.val - 1) * beta := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hb]
      ring
  · have hm1 : m = 1 := by omega
    subst m
    have hi0 : i = ⟨0, by omega⟩ := by apply Fin.ext; omega
    subst i
    simp only [dif_neg hnext, add_zero, if_pos rfl]
    rw [p32_e_first]
    have hp := p32_poly_base 1 (by omega) A alpha beta
    have hz := p32_high_zero 1 (by omega) A alpha beta
    have hl := p32_low_last 1 (by omega) A alpha beta
    rw [hp, hz]
    have hl0 : p32Low 1 A alpha beta ⟨0, hm⟩ = A ⟨0, by omega⟩ := by
      simpa using hl
    rw [hl0]
    simp


/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  funext i j
  rw [p32_mul_sparse]
  by_cases hj0 : j.val = 0
  · have hjz : j = ⟨0, hm⟩ := Fin.ext hj0
    subst j
    simpa using p32_col_first m hm A alpha beta i
  · simp only [if_neg hj0]
    by_cases hnext : j.val + 1 < m
    · simp only [dif_pos hnext]
      have h := p32_col_middle m hm A alpha beta i j hj0 hnext
      convert h using 1 <;> ring
    · simp only [dif_neg hnext, add_zero]
      exact p32_col_last m hm A alpha beta i j hj0 hnext

end VSCLReuse

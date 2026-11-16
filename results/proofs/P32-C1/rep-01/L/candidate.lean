import VSCLReuse.P32.Definitions

namespace VSCLReuse

private lemma p32_poly_range (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32Polynomial m A alpha beta =
      ∑ k ∈ Finset.range (m + 1), p32Term m A alpha beta k := by
  rw [p32Polynomial, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have h : k < m + 1 := Finset.mem_range.mp hk
  simp [p32Term, p32Coeff, h]

private lemma p32_low_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (h : j.val + 1 < m) :
    p32Low m A alpha beta j =
      beta * p32Low m A alpha beta ⟨j.val + 1, h⟩ +
      alpha ^ (m - j.val - 1) * p32Coeff m A (m - j.val - 1) := by
  simp only [p32Low]
  have hn : m - j.val = (m - (j.val + 1)) + 1 := by omega
  rw [hn, Finset.sum_range_succ]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m - (j.val + 1) := Finset.mem_range.mp hk
    have he : m - (j.val + 1) + 1 - 1 - k =
        (m - (j.val + 1) - 1 - k) + 1 := by omega
    rw [he, pow_succ]
    ring
  · have he : m - (j.val + 1) + 1 - 1 - (m - (j.val + 1)) = 0 := by omega
    rw [he, pow_zero, mul_one]
    congr 1

private lemma p32_high_step (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) (h : j.val + 1 < m) :
    p32High m A alpha beta ⟨j.val + 1, h⟩ =
      beta ^ (j.val + 1) * p32Coeff m A (m - j.val - 1) +
      alpha * p32High m A alpha beta j := by
  simp only [p32High]
  rw [Finset.sum_range_succ']
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  · simp only [pow_zero, one_mul, Nat.sub_zero, add_zero]
    congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < j.val + 1 := Finset.mem_range.mp hk
    have he : m - (j.val + 1) + (k + 1) = m - j.val + k := by omega
    rw [he]
    have he' : j.val + 1 - (k + 1) = j.val - k := by omega
    rw [he', pow_succ]
    ring

private lemma p32_poly_split (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (j : Fin m) :
    p32Polynomial m A alpha beta =
      beta ^ (j.val + 1) * p32Low m A alpha beta j +
      alpha ^ (m - j.val) * p32High m A alpha beta j := by
  rw [p32_poly_range]
  have hmj : (m - j.val) + (j.val + 1) = m + 1 := by omega
  conv_lhs => rw [← hmj, Finset.sum_range_add]
  simp only [p32Low, p32High]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m - j.val := Finset.mem_range.mp hk
    have he : m - k = (j.val + 1) + (m - j.val - 1 - k) := by omega
    unfold p32Term
    rw [he, pow_add]
    ring
  · apply Finset.sum_congr rfl
    intro q hq
    have hq' : q < j.val + 1 := Finset.mem_range.mp hq
    have he : m - (m - j.val + q) = j.val - q := by omega
    unfold p32Term
    rw [he]
    rw [pow_add]
    ring

private lemma p32_column_mid (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj : j.val ≠ 0) (hs : j.val + 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
          (beta * A ⟨m - 1 - j.val, by omega⟩) +
      p32Multiplier m A alpha beta i j * alpha -
      p32Multiplier m A alpha beta i ⟨j.val + 1, hs⟩ * beta := by
  let s : Fin m := ⟨j.val + 1, hs⟩
  have hentry (k : Fin m) :
      p32FirstCompanion m hm A alpha beta k j =
        (if k = ⟨0, hm⟩ then beta * A ⟨m - 1 - j.val, by omega⟩ else 0) +
        (if k = j then alpha else 0) +
        (if k = s then -beta else 0) := by
    by_cases hk0 : k = ⟨0, hm⟩
    · subst k
      have hj0 : (⟨0, hm⟩ : Fin m) ≠ j := by
        intro e
        exact hj (congrArg Fin.val e).symm
      simp [p32FirstCompanion, hj, hj0, s, Fin.ext_iff]
    by_cases hkj : k = j
    · subst k
      simp [p32FirstCompanion, hj, hk0, s, Fin.ext_iff]
    by_cases hks : k = s
    · subst k
      simp [p32FirstCompanion, hj, hk0, hkj, s, Fin.ext_iff]
    · have hv0 : k.val ≠ 0 := by simpa [Fin.ext_iff] using hk0
      have hvs : k.val ≠ j.val + 1 := by simpa [s, Fin.ext_iff] using hks
      simp [p32FirstCompanion, hv0, hvs, hk0, hkj, hks]
  simp only [p32MatMul]
  simp_rw [hentry, mul_add, mul_ite, mul_zero]
  simp [Finset.sum_add_distrib, s, sub_eq_add_neg]

private lemma p32_column_last (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj : j.val ≠ 0) (hs : ¬ j.val + 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
          (beta * A ⟨m - 1 - j.val, by omega⟩) +
      p32Multiplier m A alpha beta i j * alpha := by
  have hentry (k : Fin m) :
      p32FirstCompanion m hm A alpha beta k j =
        (if k = ⟨0, hm⟩ then beta * A ⟨m - 1 - j.val, by omega⟩ else 0) +
        (if k = j then alpha else 0) := by
    by_cases hk0 : k = ⟨0, hm⟩
    · subst k
      have hj0 : (⟨0, hm⟩ : Fin m) ≠ j := by
        intro e
        exact hj (congrArg Fin.val e).symm
      simp [p32FirstCompanion, hj, hj0]
    by_cases hkj : k = j
    · subst k
      simp [p32FirstCompanion, hj, hk0]
    · have hv0 : k.val ≠ 0 := by simpa [Fin.ext_iff] using hk0
      have hvs : k.val ≠ j.val + 1 := by omega
      simp [p32FirstCompanion, hv0, hvs, hk0, hkj]
  simp only [p32MatMul]
  simp_rw [hentry, mul_add, mul_ite, mul_zero]
  simp [Finset.sum_add_distrib]

private lemma p32_column_zero_mid (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i : Fin m) (hs : 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i ⟨0, hm⟩ =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
          (alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩) -
      p32Multiplier m A alpha beta i ⟨1, hs⟩ * beta := by
  have hentry (k : Fin m) :
      p32FirstCompanion m hm A alpha beta k ⟨0, hm⟩ =
        (if k = ⟨0, hm⟩ then
            alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩ else 0) +
        (if k = (⟨1, hs⟩ : Fin m) then -beta else 0) := by
    by_cases hk0 : k = ⟨0, hm⟩
    · subst k
      simp [p32FirstCompanion]
    by_cases hk1 : k = ⟨1, hs⟩
    · subst k
      simp [p32FirstCompanion]
    · have hv0 : k.val ≠ 0 := by simpa [Fin.ext_iff] using hk0
      have hv1 : k.val ≠ 1 := by simpa [Fin.ext_iff] using hk1
      simp [p32FirstCompanion, hv0, hv1, hk0, hk1]
  simp only [p32MatMul]
  simp_rw [hentry, mul_add, mul_ite, mul_zero]
  simp [Finset.sum_add_distrib, sub_eq_add_neg]
  ring

private lemma p32_column_zero_single (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i : Fin m) (hs : ¬ 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i ⟨0, hm⟩ =
      p32Multiplier m A alpha beta i ⟨0, hm⟩ *
          (alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩) := by
  have hentry (k : Fin m) :
      p32FirstCompanion m hm A alpha beta k ⟨0, hm⟩ =
        (if k = ⟨0, hm⟩ then
            alpha * A ⟨m, by omega⟩ + beta * A ⟨m - 1, by omega⟩ else 0) := by
    have hk0 : k = ⟨0, hm⟩ := Fin.ext (by omega)
    subst k
    simp [p32FirstCompanion]
  simp only [p32MatMul]
  simp_rw [hentry, mul_ite, mul_zero]
  simp

private lemma p32_mul_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32Multiplier m A alpha beta i ⟨0, hm⟩ =
      alpha ^ (m - i.val - 1) * beta ^ i.val := by
  simp [p32Multiplier]

private lemma p32_mul_upper (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : j.val ≠ 0) (hij : i.val < j.val) :
    p32Multiplier m A alpha beta i j =
      -(alpha ^ (j.val - i.val - 1) * beta ^ (i.val + 1) *
        p32Low m A alpha beta j) := by
  simp [p32Multiplier, hj, hij]

private lemma p32_mul_lower (m : ℕ) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) (i j : Fin m) (hj : j.val ≠ 0) (hij : j.val ≤ i.val) :
    p32Multiplier m A alpha beta i j =
      alpha ^ (m - i.val - 1) * beta ^ (i.val - j.val) *
        p32High m A alpha beta j := by
  have h : ¬ i.val < j.val := by omega
  simp [p32Multiplier, hj, h]

private lemma p32_column_zero (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ) (i : Fin m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i ⟨0, hm⟩ =
      if i = ⟨0, hm⟩ then p32Polynomial m A alpha beta else 0 := by
  by_cases hs : 1 < m
  · let z : Fin m := ⟨0, hm⟩
    let s : Fin m := ⟨1, hs⟩
    have hcoef : p32Coeff m A (m - 1) = A ⟨m - 1, by omega⟩ := by
      simp [p32Coeff, show m - 1 < m + 1 by omega]
    have hhigh : p32High m A alpha beta z = A ⟨m, by omega⟩ := by
      simp [p32High, z, p32Coeff, show m < m + 1 by omega]
    have hpol := p32_poly_split m A alpha beta z
    have hlow := p32_low_step m A alpha beta z hs
    have hhighstep := p32_high_step m A alpha beta z hs
    by_cases hi : i = z
    · subst i
      rw [if_pos rfl, p32_column_zero_mid m hm A alpha beta z hs]
      rw [p32_mul_zero, p32_mul_upper m A alpha beta z s
        (by change 1 ≠ 0; omega) (by change 0 < 1; omega)]
      simp only [z, s, Fin.val_zero, pow_zero, Nat.sub_zero, pow_one, one_mul] at *
      rw [hlow, hhigh] at hpol
      rw [hcoef] at hpol
      rw [hpol]
      have he : m = (m - 1) + 1 := by omega
      have hp : alpha ^ m = alpha ^ (m - 1) * alpha := by
        conv_lhs => rw [he]
        rw [pow_succ]
      rw [hp]
      ring
    · have hival : 0 < i.val := by
        have : i.val ≠ 0 := by simpa [z, Fin.ext_iff] using hi
        omega
      rw [if_neg hi, p32_column_zero_mid m hm A alpha beta i hs]
      rw [p32_mul_zero, p32_mul_lower m A alpha beta i s
        (by change 1 ≠ 0; omega) (by change 1 ≤ i.val; omega)]
      simp only [s, Fin.val_one] at *
      simp only [z, Fin.val_mk, zero_add, Nat.sub_zero] at hhighstep
      rw [hhigh, hcoef] at hhighstep
      rw [hhighstep]
      have he : i.val = (i.val - 1) + 1 := by omega
      have hp : beta ^ i.val = beta ^ (i.val - 1) * beta := by
        conv_lhs => rw [he]
        rw [pow_succ]
      rw [hp]
      ring
  · have hm1 : m = 1 := by omega
    subst m
    have hi : i = (⟨0, by decide⟩ : Fin 1) := Fin.ext (by omega)
    subst i
    rw [if_pos rfl]
    rw [p32_column_zero_single 1 (by decide) A alpha beta ⟨0, by decide⟩ (by omega)]
    simp [p32Multiplier, p32Polynomial, p32Coeff]
    ring

private lemma p32_column_pos_mid (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj : j.val ≠ 0) (hs : j.val + 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  let s : Fin m := ⟨j.val + 1, hs⟩
  have hsval : s.val = j.val + 1 := rfl
  have hspos : s.val ≠ 0 := by omega
  have hc : p32Coeff m A (m - 1 - j.val) =
      A ⟨m - 1 - j.val, by omega⟩ := by
    simp [p32Coeff, show m - 1 - j.val < m + 1 by omega]
  have hl := p32_low_step m A alpha beta j hs
  have hh := p32_high_step m A alpha beta j hs
  have hp := p32_poly_split m A alpha beta j
  have hidx : m - j.val - 1 = m - 1 - j.val := by omega
  rw [hidx, hc] at hl hh
  by_cases hij : i.val < j.val
  · have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
    rw [if_neg hne, p32_column_mid m hm A alpha beta i j hj hs]
    rw [p32_mul_zero, p32_mul_upper m A alpha beta i j hj hij,
      p32_mul_upper m A alpha beta i s hspos (by omega)]
    rw [hl]
    have he1 : (j.val - i.val - 1) + 1 = j.val - i.val := by omega
    have he2 : (j.val - i.val) + (m - j.val - 1) = m - i.val - 1 := by omega
    have hα1 : alpha ^ (j.val - i.val - 1) * alpha = alpha ^ (j.val - i.val) := by
      rw [← pow_succ, he1]
    have hα2 : alpha ^ (j.val - i.val) * alpha ^ (m - j.val - 1) =
        alpha ^ (m - i.val - 1) := by rw [← pow_add, he2]
    simp only [s, Fin.val_mk] at *
    have he3 : j.val + 1 - i.val - 1 = j.val - i.val := by omega
    rw [he3]
    have hβ1 : beta ^ i.val * beta = beta ^ (i.val + 1) := by rw [← pow_succ]
    have hβ2 : beta ^ (i.val + 1) * beta = beta ^ (i.val + 2) := by
      rw [← pow_succ]
    have hα3 : alpha ^ (j.val - i.val) * alpha ^ (m - 1 - j.val) =
        alpha ^ (m - i.val - 1) := by simpa only [← hidx] using hα2
    calc
      _ = alpha ^ (m - i.val - 1) * (beta ^ i.val * beta) *
              A ⟨m - 1 - j.val, by omega⟩ -
            (alpha ^ (j.val - i.val - 1) * alpha) * beta ^ (i.val + 1) *
              (beta * p32Low m A alpha beta ⟨j.val + 1, hs⟩ +
                alpha ^ (m - 1 - j.val) * A ⟨m - 1 - j.val, by omega⟩) +
            alpha ^ (j.val - i.val) * (beta ^ (i.val + 1) * beta) *
              p32Low m A alpha beta ⟨j.val + 1, hs⟩ := by ring
      _ = 0 := by
        rw [hα1, hβ1]
        calc
          _ = alpha ^ (m - i.val - 1) * beta ^ (i.val + 1) *
                  A ⟨m - 1 - j.val, by omega⟩ -
                (alpha ^ (j.val - i.val) * alpha ^ (m - 1 - j.val)) *
                  beta ^ (i.val + 1) * A ⟨m - 1 - j.val, by omega⟩ := by ring
          _ = 0 := by rw [hα3]; ring
  · by_cases heq : i = j
    · subst i
      rw [if_pos rfl, p32_column_mid m hm A alpha beta j j hj hs]
      rw [p32_mul_zero, p32_mul_lower m A alpha beta j j hj (by omega),
        p32_mul_upper m A alpha beta j s hspos (by omega)]
      rw [hp, hl]
      simp only [s, Fin.val_mk, Nat.sub_self, pow_zero, mul_one]
      have he : m - j.val = (m - j.val - 1) + 1 := by omega
      have hα : alpha ^ (m - j.val) = alpha ^ (m - j.val - 1) * alpha := by
        conv_lhs => rw [he]
        rw [pow_succ]
      rw [hα]
      rw [pow_succ beta j.val]
      have he0 : j.val + 1 - j.val - 1 = 0 := by omega
      have hpow0 : alpha ^ (j.val + 1 - j.val - 1) = 1 := by
        rw [he0, pow_zero]
      rw [hpow0]
      simp only [hidx]
      ring
    · have hgt : j.val < i.val := by
        have : i.val ≠ j.val := by simpa [Fin.ext_iff] using heq
        omega
      rw [if_neg heq, p32_column_mid m hm A alpha beta i j hj hs]
      rw [p32_mul_zero, p32_mul_lower m A alpha beta i j hj (by omega),
        p32_mul_lower m A alpha beta i s hspos (by omega)]
      rw [hh]
      have he1 : i.val - j.val = (i.val - (j.val + 1)) + 1 := by omega
      have he2 : (i.val - (j.val + 1)) + (j.val + 1) = i.val := by omega
      have hβ1 : beta ^ (i.val - j.val) = beta ^ (i.val - (j.val + 1)) * beta := by
        conv_lhs => rw [he1]
        rw [pow_succ]
      have hβ2 : beta ^ (i.val - (j.val + 1)) * beta ^ (j.val + 1) =
          beta ^ i.val := by rw [← pow_add, he2]
      simp only [s, Fin.val_mk] at *
      rw [hβ1]
      calc
        _ = alpha ^ (m - i.val - 1) * beta *
              (beta ^ i.val - beta ^ (i.val - (j.val + 1)) *
                beta ^ (j.val + 1)) *
              A ⟨m - 1 - j.val, by omega⟩ := by ring
        _ = 0 := by rw [hβ2]; ring

private lemma p32_column_pos_last (m : ℕ) (hm : 0 < m)
    (A : Fin (m + 1) → ℝ) (alpha beta : ℝ)
    (i j : Fin m) (hj : j.val ≠ 0) (hs : ¬ j.val + 1 < m) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) i j =
      if i = j then p32Polynomial m A alpha beta else 0 := by
  have hjlast : j.val + 1 = m := by omega
  have hidx : m - 1 - j.val = 0 := by omega
  have hn : m - j.val = 1 := by omega
  have hc : A ⟨m - 1 - j.val, by omega⟩ = A ⟨0, by omega⟩ := by
    exact congrArg A (Fin.ext hidx)
  have hlow : p32Low m A alpha beta j = A ⟨0, by omega⟩ := by
    simp [p32Low, hn, p32Coeff]
  have hp := p32_poly_split m A alpha beta j
  rw [hlow] at hp
  by_cases hij : i.val < j.val
  · have hne : i ≠ j := by intro e; have := congrArg Fin.val e; omega
    rw [if_neg hne, p32_column_last m hm A alpha beta i j hj hs]
    rw [p32_mul_zero, p32_mul_upper m A alpha beta i j hj hij]
    rw [hc, hlow]
    have he1 : (j.val - i.val - 1) + 1 = j.val - i.val := by omega
    have hα1 : alpha ^ (j.val - i.val - 1) * alpha = alpha ^ (j.val - i.val) := by
      rw [← pow_succ, he1]
    have he2 : j.val - i.val = m - i.val - 1 := by omega
    have hβ : beta ^ i.val * beta = beta ^ (i.val + 1) := by rw [← pow_succ]
    calc
      _ = alpha ^ (m - i.val - 1) * (beta ^ i.val * beta) * A ⟨0, by omega⟩ -
            (alpha ^ (j.val - i.val - 1) * alpha) * beta ^ (i.val + 1) *
              A ⟨0, by omega⟩ := by ring
      _ = 0 := by rw [hα1, he2, hβ]; ring
  · have heq : i = j := Fin.ext (by omega)
    subst i
    rw [if_pos rfl, p32_column_last m hm A alpha beta j j hj hs]
    rw [p32_mul_zero, p32_mul_lower m A alpha beta j j hj (by omega)]
    rw [hc, hp]
    have he0 : m - j.val - 1 = 0 := by omega
    have he1 : m - j.val = 1 := by omega
    have he2 : j.val + 1 = m := by omega
    simp only [he0, he1, he2, Nat.sub_self, pow_zero, pow_one, one_mul, mul_one]
    have hb : beta ^ m = beta ^ j.val * beta := by
      conv_lhs => rw [← hjlast]
      rw [pow_succ]
    rw [hb]
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
  by_cases hj : j.val = 0
  · have hzero : j = ⟨0, hm⟩ := Fin.ext hj
    subst j
    exact p32_column_zero m hm A alpha beta i
  · by_cases hs : j.val + 1 < m
    · exact p32_column_pos_mid m hm A alpha beta i j hj hs
    · exact p32_column_pos_last m hm A alpha beta i j hj hs

end VSCLReuse

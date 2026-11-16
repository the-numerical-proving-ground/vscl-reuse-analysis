import VSCLReuse.P52.Definitions

namespace VSCLReuse

open scoped BigOperators

private def p52Quad : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * p52Quad n + n

private theorem p52_comp_bound {u p q r s x y : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : |x - 1| ≤ p * u + q * u ^ 2)
    (hy : |y - 1| ≤ r * u + s * u ^ 2) :
    |x * y - 1| ≤ (p + r) * u +
      (q + s + (p + q) * (r + s)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith [sq_nonneg u]
  have hxu : |x - 1| ≤ (p + q) * u := by nlinarith
  have hyu : |y - 1| ≤ (r + s) * u := by nlinarith
  have hprod : |x - 1| * |y - 1| ≤ (p + q) * (r + s) * u ^ 2 := by
    calc
      |x - 1| * |y - 1| ≤ ((p + q) * u) * ((r + s) * u) :=
        mul_le_mul hxu hyu (abs_nonneg _) (by positivity)
      _ = (p + q) * (r + s) * u ^ 2 := by ring
  have htri : |x * y - 1| ≤ |x - 1| + |y - 1| + |x - 1| * |y - 1| := by
    calc
      |x * y - 1| = |(x - 1) + (y - 1) + (x - 1) * (y - 1)| := by congr 1; ring
      _ ≤ |x - 1| + |y - 1| + |(x - 1) * (y - 1)| := by
        calc
          _ ≤ |(x - 1) + (y - 1)| + |(x - 1) * (y - 1)| := abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_mul]
  nlinarith

private theorem p52_sum_coeff (fp : P52FPModel) (hu : fp.u ≤ 1) :
    ∀ n : ℕ, ∀ v : Fin (n + 1) → ℝ,
      ∃ c : Fin (n + 1) → ℝ,
        Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) 0 =
          ∑ i : Fin (n + 1), v i * c i ∧
        ∀ i, |c i - 1| ≤ (n : ℝ) * fp.u + (p52Quad n : ℝ) * fp.u ^ 2 := by
  intro n
  induction n with
  | zero =>
      intro v
      refine ⟨fun _ => 1, ?_, ?_⟩
      · simp [Fin.foldl_succ, Fin.foldl_zero, fp.fl_add_zero, Fin.sum_univ_succ]
      · intro i
        simp
  | succ n ih =>
      intro v
      let v' : Fin (n + 1) → ℝ := fun i => v i.castSucc
      obtain ⟨c, hc, hcb⟩ := ih v'
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v' i)) 0)
        (v (Fin.last (n + 1)))
      let c' : Fin (n + 2) → ℝ :=
        Fin.snoc (fun i => c i * (1 + δ)) (1 + δ)
      refine ⟨c', ?_, ?_⟩
      · rw [Fin.foldl_succ_last]
        change fp.fl_add
          (Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v' i)) 0)
          (v (Fin.last (n + 1))) = _
        rw [hfl, hc]
        conv_rhs => rw [Fin.sum_univ_castSucc]
        simp only [c', Fin.snoc_castSucc, Fin.snoc_last]
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simp only [c', Fin.snoc_last]
          have hq : 0 ≤ (p52Quad n : ℝ) := Nat.cast_nonneg _
          simp only [p52Quad, Nat.cast_add, Nat.cast_mul, Nat.cast_succ]
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
          have hδ' : |(1 + δ : ℝ) - 1| ≤ fp.u := by simpa using hδ
          nlinarith [mul_nonneg hn fp.u_nonneg,
            mul_nonneg hq (sq_nonneg fp.u), mul_nonneg hn (sq_nonneg fp.u)]
        · intro j
          simp only [c', Fin.snoc_castSucc]
          have hq : 0 ≤ (p52Quad n : ℝ) := Nat.cast_nonneg _
          have hδ' : |(1 + δ : ℝ) - 1| ≤ (1 : ℝ) * fp.u + 0 * fp.u ^ 2 := by
            simpa using hδ
          have hb := p52_comp_bound fp.u_nonneg hu (Nat.cast_nonneg n) hq
            (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
            (hcb j) hδ'
          simp only [p52Quad, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
            Nat.cast_ofNat, Nat.cast_succ] at *
          nlinarith [sq_nonneg fp.u]

private theorem p52_dot_coeff (fp : P52FPModel) (hu : fp.u ≤ 1)
    (N : ℕ) (hN : 0 < N) (x y : Fin N → ℝ) :
    ∃ c : Fin N → ℝ,
      p52RoundedDotProduct fp N x y = ∑ i : Fin N, x i * y i * c i ∧
      ∀ i, |c i - 1| ≤ (N : ℝ) * fp.u +
        (2 * p52Quad (N - 1) + (N - 1) : ℕ) * fp.u ^ 2 := by
  cases N with
  | zero => omega
  | succ n =>
      let v : Fin (n + 1) → ℝ := fun i => fp.fl_mul (x i) (y i)
      obtain ⟨s, hs, hsb⟩ := p52_sum_coeff fp hu n v
      choose δ hδ hmul using (fun i : Fin (n + 1) => fp.model_mul (x i) (y i))
      let c : Fin (n + 1) → ℝ := fun i => (1 + δ i) * s i
      refine ⟨c, ?_, ?_⟩
      · have hdot : p52RoundedDotProduct fp (n + 1) x y =
            Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (v i)) 0 := by
          simp [p52RoundedDotProduct, v, Fin.foldl_succ, fp.fl_add_zero]
        rw [hdot, hs]
        apply Finset.sum_congr rfl
        intro i _
        simp only [c, v, hmul i]
        ring
      · intro i
        have hδi : |(1 + δ i : ℝ) - 1| ≤ (1 : ℝ) * fp.u + 0 * fp.u ^ 2 := by
          simpa using hδ i
        have hq : 0 ≤ (p52Quad n : ℝ) := Nat.cast_nonneg _
        have hb := p52_comp_bound fp.u_nonneg hu
          (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
          (Nat.cast_nonneg n) hq hδi (hsb i)
        simp only [c, Nat.succ_sub_one, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_succ] at *
        nlinarith

private theorem p52_recursive_coeff (fp : P52FPModel) (hu : fp.u ≤ 1)
    (M : ℕ) (hM : 0 < M) (v : Fin M → ℝ) :
    ∃ c : Fin M → ℝ,
      p52RecursiveSum fp M v = ∑ j : Fin M, v j * c j ∧
      ∀ j, |c j - 1| ≤ ((M - 1 : ℕ) : ℝ) * fp.u +
        (p52Quad (M - 1) : ℝ) * fp.u ^ 2 := by
  cases M with
  | zero => omega
  | succ m =>
      obtain ⟨c, hc, hcb⟩ := p52_sum_coeff fp hu m v
      refine ⟨c, ?_, ?_⟩
      · exact hc
      · simpa using hcb

private theorem p52_weighted_sum_error {n : ℕ} (v c : Fin n → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (hc : ∀ i, |c i - 1| ≤ E) :
    |(∑ i : Fin n, v i * c i) - ∑ i : Fin n, v i| ≤
      E * ∑ i : Fin n, |v i| := by
  have heq : (∑ i : Fin n, v i * c i) - ∑ i : Fin n, v i =
      ∑ i : Fin n, v i * (c i - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  calc
    |∑ i : Fin n, v i * (c i - 1)| ≤ ∑ i : Fin n, |v i * (c i - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, E * |v i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hc i) (abs_nonneg (v i))]
    _ = E * ∑ i : Fin n, |v i| := by rw [Finset.mul_sum]

private theorem p52_div_coeff_bound {u P Q K L t e : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (ht : |t - 1| ≤ P * u + Q * u ^ 2)
    (he : |e| ≤ K * u + L * u ^ 2)
    (hsmall : (K + L) * u ≤ 1 / 2) :
    |t / (1 + e) - 1| ≤
      (P + K) * u +
        (Q + L + 2 * (P + Q + K + L) * (K + L)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith [sq_nonneg u]
  have he' : |e| ≤ (K + L) * u := by nlinarith
  have hehalf : |e| ≤ 1 / 2 := he'.trans hsmall
  have hdenlow : 1 - |e| ≤ |1 + e| := by
    have h := abs_add_le (1 + e) (-e)
    simp only [add_neg_cancel_right, abs_one, abs_neg] at h
    linarith
  have hden : 0 < |1 + e| := by linarith
  have hinv : 1 / |1 + e| ≤ 1 + 2 * |e| := by
    apply (div_le_iff₀ hden).2
    have hmul := mul_le_mul_of_nonneg_left hdenlow (by positivity : 0 ≤ 1 + 2 * |e|)
    have hnon : 0 ≤ |e| * (1 - 2 * |e|) :=
      mul_nonneg (abs_nonneg _) (by linarith)
    nlinarith
  let E := (P + K) * u + (Q + L) * u ^ 2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnum : |t - (1 + e)| ≤ E := by
    have htri : |t - (1 + e)| ≤ |t - 1| + |e| := by
      calc
        |t - (1 + e)| = |(t - 1) + (-e)| := by congr 1; ring
        _ ≤ |t - 1| + |-e| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    dsimp [E]
    linarith
  have hEu : E ≤ (P + Q + K + L) * u := by dsimp [E]; nlinarith
  have hprod : E * |e| ≤ (P + Q + K + L) * (K + L) * u ^ 2 := by
    calc
      E * |e| ≤ ((P + Q + K + L) * u) * ((K + L) * u) :=
        mul_le_mul hEu he' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hrew : |t / (1 + e) - 1| = |t - (1 + e)| / |1 + e| := by
    have hne : 1 + e ≠ 0 := abs_pos.mp hden
    have hraw : t / (1 + e) - 1 = (t - (1 + e)) / (1 + e) := by
      field_simp
    rw [hraw, abs_div]
  rw [hrew]
  calc
    |t - (1 + e)| / |1 + e| ≤ E / |1 + e| :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ ≤ E * (1 + 2 * |e|) := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul_of_nonneg_left hinv hE
    _ ≤ (P + K) * u +
        (Q + L + 2 * (P + Q + K + L) * (K + L)) * u ^ 2 := by
      dsimp [E]
      nlinarith

theorem p52_c3_theorem2_full_named
    (N M : ℕ) (a f : Fin N → ℝ) (b : Fin M → ℝ)
    (A B CA CB betaBound : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hN : 0 < N) (hM : 0 < M)
    (hD0 : (∑ j : Fin M, b j) ≠ 0)
    (hbetaBound : p52DenominatorCondition M b ≤ betaBound)
    (hbetaBound0 : 0 ≤ betaBound) :
    ∃ u0 C : ℝ, 0 < u0 ∧ 0 ≤ C ∧
      ∀ (fp : P52FPModel) (ahat : Fin N → ℝ) (bhat : Fin M → ℝ),
      fp.u ≤ u0 →
      (∀ i, ∃ alpha_i : ℝ,
        ahat i = a i * (1 + alpha_i) ∧
          |alpha_i| ≤ A * fp.u + CA * fp.u ^ 2) →
      (∀ j, ∃ beta_j : ℝ,
        bhat j = b j * (1 + beta_j) ∧
          |beta_j| ≤ B * fp.u + CB * fp.u ^ 2) →
      ∃ fhat : Fin N → ℝ,
        p52ComputedQuotient fp N M ahat f bhat =
          (∑ i : Fin N, a i * fhat i) / (∑ j : Fin M, b j) ∧
        ‖fhat - f‖ ≤
          ((((N : ℝ) + 1 + A) +
            (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
            C * fp.u ^ 2) * ‖f‖ := by
  -- PROOF_START P52-C3-H001
  let qN : ℝ := (2 * p52Quad (N - 1) + (N - 1) : ℕ)
  let qM : ℝ := (p52Quad (M - 1) : ℕ)
  let P : ℝ := (N : ℝ) + A
  let Q : ℝ := CA + qN + (A + CA) * ((N : ℝ) + qN)
  let R : ℝ := ((M - 1 : ℕ) : ℝ) + B
  let S : ℝ := CB + qM + (B + CB) * (((M - 1 : ℕ) : ℝ) + qM)
  let P₁ : ℝ := P + 1
  let Q₁ : ℝ := Q + P + Q
  let K : ℝ := R * betaBound
  let L : ℝ := S * betaBound
  let u0 : ℝ := min 1 (1 / (2 * (K + L + 1)))
  let C : ℝ := Q₁ + L + 2 * (P₁ + Q₁ + K + L) * (K + L)
  have hqN : 0 ≤ qN := Nat.cast_nonneg _
  have hqM : 0 ≤ qM := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hQ₁ : 0 ≤ Q₁ := by dsimp [Q₁]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hKL : 0 < 2 * (K + L + 1) := by positivity
  have hu0 : 0 < u0 := by
    dsimp [u0]
    exact lt_min_iff.mpr ⟨by norm_num, div_pos (by norm_num) hKL⟩
  refine ⟨u0, C, hu0, hC, ?_⟩
  intro fp ahat bhat hu hAlpha hBeta
  have hu1 : fp.u ≤ 1 := hu.trans (by dsimp [u0]; exact min_le_left _ _)
  have hsmall : (K + L) * fp.u ≤ 1 / 2 := by
    have hu' : fp.u ≤ 1 / (2 * (K + L + 1)) :=
      hu.trans (by dsimp [u0]; exact min_le_right _ _)
    have hh := (le_div_iff₀ hKL).mp hu'
    nlinarith [fp.u_nonneg]
  choose α hαeq hαb using hAlpha
  choose β hβeq hβb using hBeta
  obtain ⟨cd, hdot, hcdb⟩ := p52_dot_coeff fp hu1 N hN ahat f
  obtain ⟨cs, hsum, hcsb⟩ := p52_recursive_coeff fp hu1 M hM bhat
  let pn : Fin N → ℝ := fun i => (1 + α i) * cd i
  let pd : Fin M → ℝ := fun j => (1 + β j) * cs j
  have hpnb (i : Fin N) : |pn i - 1| ≤ P * fp.u + Q * fp.u ^ 2 := by
    dsimp [pn, P, Q, qN]
    have hαi : |(1 + α i : ℝ) - 1| ≤ A * fp.u + CA * fp.u ^ 2 := by
      simpa using hαb i
    have hb := p52_comp_bound (x := 1 + α i) (y := cd i)
      fp.u_nonneg hu1 hA hCA (Nat.cast_nonneg N)
      (Nat.cast_nonneg _) hαi (hcdb i)
    convert hb using 1 <;> ring
  have hpdb (j : Fin M) : |pd j - 1| ≤ R * fp.u + S * fp.u ^ 2 := by
    dsimp [pd, R, S, qM]
    have hβj : |(1 + β j : ℝ) - 1| ≤ B * fp.u + CB * fp.u ^ 2 := by
      simpa using hβb j
    have hb := p52_comp_bound (x := 1 + β j) (y := cs j)
      fp.u_nonneg hu1 hB hCB
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hβj (hcsb j)
    convert hb using 1 <;> ring
  let X : ℝ := p52RoundedDotProduct fp N ahat f
  let Y : ℝ := p52RecursiveSum fp M bhat
  let D : ℝ := ∑ j : Fin M, b j
  have hX : X = ∑ i : Fin N, a i * f i * pn i := by
    dsimp [X]
    rw [hdot]
    apply Finset.sum_congr rfl
    intro i _
    simp only [pn, hαeq i]
    ring
  have hY : Y = ∑ j : Fin M, b j * pd j := by
    dsimp [Y]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [pd, hβeq j]
    ring
  have hD : D ≠ 0 := hD0
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hdenCond : (∑ j : Fin M, |b j|) / |D| ≤ betaBound := hbetaBound
  have hYerr : |Y - D| ≤ (R * fp.u + S * fp.u ^ 2) *
      ∑ j : Fin M, |b j| := by
    rw [hY]
    exact p52_weighted_sum_error b pd
      (by nlinarith only [mul_nonneg hR fp.u_nonneg,
        mul_nonneg hS (sq_nonneg fp.u)]) hpdb
  let e : ℝ := (Y - D) / D
  have he : |e| ≤ K * fp.u + L * fp.u ^ 2 := by
    have hdiv : |e| ≤
        ((R * fp.u + S * fp.u ^ 2) * ∑ j : Fin M, |b j|) / |D| := by
      dsimp [e]
      rw [abs_div]
      exact div_le_div_of_nonneg_right hYerr (le_of_lt hDabs)
    calc
      |e| ≤ ((R * fp.u + S * fp.u ^ 2) * ∑ j : Fin M, |b j|) / |D| := hdiv
      _ = (R * fp.u + S * fp.u ^ 2) *
          ((∑ j : Fin M, |b j|) / |D|) := by rw [mul_div_assoc]
      _ ≤ (R * fp.u + S * fp.u ^ 2) * betaBound :=
        mul_le_mul_of_nonneg_left hdenCond (by
          nlinarith only [mul_nonneg hR fp.u_nonneg,
            mul_nonneg hS (sq_nonneg fp.u)])
      _ = K * fp.u + L * fp.u ^ 2 := by dsimp [K, L]; ring
  have hehalf : |e| ≤ 1 / 2 := by
    have hu2 : fp.u ^ 2 ≤ fp.u := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hu1 fp.u_nonneg
    have hLu := mul_le_mul_of_nonneg_left hu2 hL
    calc
      |e| ≤ K * fp.u + L * fp.u ^ 2 := he
      _ ≤ K * fp.u + L * fp.u := add_le_add_right hLu _
      _ = (K + L) * fp.u := by ring
      _ ≤ 1 / 2 := hsmall
  have hepos : 0 < 1 + e := by
    have := (abs_le.mp hehalf).1
    linarith
  have he0 : 1 + e ≠ 0 := ne_of_gt hepos
  have hYeq : Y = D * (1 + e) := by
    dsimp [e]
    field_simp [hD]
    ring
  have hY0 : Y ≠ 0 := by rw [hYeq]; exact mul_ne_zero hD he0
  obtain ⟨δ, hδ, hfl⟩ := fp.model_div X Y hY0
  let t : Fin N → ℝ := fun i => pn i * (1 + δ)
  have htb (i : Fin N) : |t i - 1| ≤ P₁ * fp.u + Q₁ * fp.u ^ 2 := by
    dsimp [t, P₁, Q₁]
    have hδ' : |(1 + δ : ℝ) - 1| ≤ (1 : ℝ) * fp.u + 0 * fp.u ^ 2 := by
      simpa using hδ
    have hb := p52_comp_bound fp.u_nonneg hu1 hP hQ
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 0)
      (hpnb i) hδ'
    convert hb using 1 <;> ring
  let fhat : Fin N → ℝ := fun i => f i * (t i / (1 + e))
  refine ⟨fhat, ?_, ?_⟩
  · have hfsum : (∑ i : Fin N, a i * fhat i) =
        X * ((1 + δ) / (1 + e)) := by
      rw [hX]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [fhat, t]
      ring
    rw [p52ComputedQuotient, hfl, hYeq, hfsum]
    field_simp [hD, he0]
    ring
  · have hbound0 : 0 ≤ (P₁ + K) * fp.u + C * fp.u ^ 2 := by
      exact add_nonneg (mul_nonneg (add_nonneg hP₁ hK) fp.u_nonneg)
        (mul_nonneg hC (sq_nonneg fp.u))
    have hcoefeq :
        ((((N : ℝ) + 1 + A) + (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
          C * fp.u ^ 2) = (P₁ + K) * fp.u + C * fp.u ^ 2 := by
      dsimp [P₁, P, K, R]
      ring
    rw [hcoefeq]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hbound0 (norm_nonneg f))).2
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    have hcoef := p52_div_coeff_bound fp.u_nonneg hu1 hP₁ hQ₁ hK hL
      (htb i) he hsmall
    have hcoef' : |t i / (1 + e) - 1| ≤
        (P₁ + K) * fp.u + C * fp.u ^ 2 := by
      simpa only [C] using hcoef
    have hpoint : |fhat i - f i| ≤
        ((P₁ + K) * fp.u + C * fp.u ^ 2) * |f i| := by
      have heq : fhat i - f i = f i * (t i / (1 + e) - 1) := by
        dsimp [fhat]
        ring
      rw [heq, abs_mul]
      calc
        |f i| * |t i / (1 + e) - 1| =
            |t i / (1 + e) - 1| * |f i| := by ring
        _ ≤ ((P₁ + K) * fp.u + C * fp.u ^ 2) * |f i| :=
          mul_le_mul_of_nonneg_right hcoef' (abs_nonneg _)
    calc
      |fhat i - f i| ≤ ((P₁ + K) * fp.u + C * fp.u ^ 2) * |f i| := hpoint
      _ ≤ ((P₁ + K) * fp.u + C * fp.u ^ 2) * ‖f‖ := by
        have hfi : |f i| ≤ ‖f‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm f i
        exact mul_le_mul_of_nonneg_left hfi hbound0

end VSCLReuse

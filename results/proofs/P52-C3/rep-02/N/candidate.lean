import VSCLReuse.P52.Definitions

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p52Err (u : ℝ) (k : ℕ) : ℝ := (1 + u) ^ k - 1

private def p52Join (e d : ℝ) : ℝ := e + d + e * d

private theorem p52_one_join (e d : ℝ) :
    (1 + e) * (1 + d) = 1 + p52Join e d := by
  unfold p52Join
  ring

private theorem p52_err_nonneg {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    0 ≤ p52Err u k := by
  unfold p52Err
  have h : 1 ≤ 1 + u := by linarith
  have hp : 1 ≤ (1 + u) ^ k := by simpa using (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) h k)
  linarith

private theorem p52_join_bound {u e d : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (he : |e| ≤ p52Err u k) (hd : |d| ≤ u) :
    |p52Join e d| ≤ p52Err u (k + 1) := by
  have hE := p52_err_nonneg hu k
  have h₁ : |p52Join e d| ≤ |e| + |d| + |e| * |d| := by
    unfold p52Join
    calc
      |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
      _ ≤ |e| + |d| + |e| * |d| := by
        rw [abs_mul]
        linarith [abs_add_le e d]
  have h₂ : |e| + |d| + |e| * |d| ≤
      p52Err u k + u + p52Err u k * u := by
    gcongr
  calc
    |p52Join e d| ≤ |e| + |d| + |e| * |d| := h₁
    _ ≤ p52Err u k + u + p52Err u k * u := h₂
    _ = p52Err u (k + 1) := by
      unfold p52Err
      rw [pow_succ]
      ring

private theorem p52_fold_add_rep (fp : P52FPModel) (n : ℕ)
    (v : Fin n → ℝ) (z : ℝ) :
    ∃ (e0 : ℝ) (e : Fin n → ℝ),
      Fin.foldl n (fun acc i => fp.fl_add acc (v i)) z =
        z * (1 + e0) + ∑ i : Fin n, v i * (1 + e i) ∧
      |e0| ≤ p52Err fp.u n ∧
      ∀ i, |e i| ≤ p52Err fp.u n := by
  induction n generalizing z with
  | zero =>
      refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · simp
      · simp [p52Err]
      · intro i
        exact i.elim0
  | succ n ih =>
      obtain ⟨e0, e, heq, he0, he⟩ := ih (fun i => v i.castSucc) z
      obtain ⟨d, hd, hfl⟩ := fp.model_add
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) z)
        (v (Fin.last n))
      refine ⟨p52Join e0 d, Fin.snoc (fun i => p52Join (e i) d) d, ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ_last, hfl, heq]
        simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
        simp_rw [← p52_one_join]
        calc
          (z * (1 + e0) + ∑ i, v i.castSucc * (1 + e i) + v (Fin.last n)) * (1 + d) =
              z * ((1 + e0) * (1 + d)) +
                (∑ i, (v i.castSucc * (1 + e i)) * (1 + d)) +
                v (Fin.last n) * (1 + d) := by
                  simp only [add_mul, Finset.sum_mul]
                  ring
          _ = _ := by
            simp only [mul_assoc]
            ring
      · exact p52_join_bound fp.u_nonneg he0 hd
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa using hd.trans (by
            have : fp.u ≤ p52Err fp.u (n + 1) := by
              have h0 := p52_err_nonneg fp.u_nonneg n
              unfold p52Err at *
              rw [pow_succ]
              nlinarith [mul_nonneg h0 fp.u_nonneg]
            exact this)
        · intro j
          simpa using p52_join_bound fp.u_nonneg (he j) hd

private theorem p52_recursive_sum_rep (fp : P52FPModel) (k : ℕ)
    (v : Fin (k + 1) → ℝ) :
    ∃ e : Fin (k + 1) → ℝ,
      p52RecursiveSum fp (k + 1) v = ∑ i, v i * (1 + e i) ∧
      ∀ i, |e i| ≤ p52Err fp.u k := by
  obtain ⟨e0, e, heq, he0, he⟩ :=
    p52_fold_add_rep fp k (fun i => v i.succ) (v 0)
  refine ⟨Fin.cons e0 e, ?_, ?_⟩
  · simp only [p52RecursiveSum, Fin.foldl_succ, fp.fl_add_zero]
    rw [heq, Fin.sum_univ_succ]
    simp
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa using he0
    · intro j
      simpa using he j

private theorem p52_dot_rep (fp : P52FPModel) (k : ℕ)
    (x y : Fin (k + 1) → ℝ) :
    ∃ e : Fin (k + 1) → ℝ,
      p52RoundedDotProduct fp (k + 1) x y =
        ∑ i, (x i * y i) * (1 + e i) ∧
      ∀ i, |e i| ≤ p52Err fp.u (k + 1) := by
  classical
  let d : Fin (k + 1) → ℝ := fun i =>
    Classical.choose (fp.model_mul (x i) (y i))
  have hd (i : Fin (k + 1)) : |d i| ≤ fp.u :=
    (Classical.choose_spec (fp.model_mul (x i) (y i))).1
  have hmul (i : Fin (k + 1)) :
      fp.fl_mul (x i) (y i) = (x i * y i) * (1 + d i) :=
    (Classical.choose_spec (fp.model_mul (x i) (y i))).2
  obtain ⟨e0, e, heq, he0, he⟩ :=
    p52_fold_add_rep fp k
      (fun i => fp.fl_mul (x i.succ) (y i.succ))
      (fp.fl_mul (x 0) (y 0))
  refine ⟨Fin.cons (p52Join e0 (d 0))
    (fun i => p52Join (e i) (d i.succ)), ?_, ?_⟩
  · simp only [p52RoundedDotProduct]
    rw [heq, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hmul 0]
    simp_rw [hmul]
    simp_rw [← p52_one_join]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      ring
  · intro i
    refine Fin.cases ?_ ?_ i
    · simpa using p52_join_bound fp.u_nonneg he0 (hd 0)
    · intro j
      simpa using p52_join_bound fp.u_nonneg (he j) (hd j.succ)

private theorem p52_nat_le_three_pow (k : ℕ) :
    (k : ℝ) ≤ (3 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hp : 1 ≤ (3 : ℝ) ^ k := by
        exact one_le_pow₀ (by norm_num)
      rw [pow_succ]
      push_cast
      nlinarith

private theorem p52_err_quad {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (k : ℕ) :
    p52Err u k ≤ (k : ℝ) * u + (3 : ℝ) ^ k * u ^ 2 := by
  induction k with
  | zero =>
      simp [p52Err]
      positivity
  | succ k ih =>
      have hrec : p52Err u (k + 1) = p52Err u k * (1 + u) + u := by
        unfold p52Err
        rw [pow_succ]
        ring
      have hp : 0 ≤ (3 : ℝ) ^ k := pow_nonneg (by norm_num) _
      have hku : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
      have hu2 : 0 ≤ u ^ 2 := sq_nonneg _
      have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith [mul_nonneg hu2 (sub_nonneg.mpr hu1)]
      have hk := p52_nat_le_three_pow k
      rw [hrec, pow_succ]
      push_cast
      calc
        p52Err u k * (1 + u) + u ≤
            ((k : ℝ) * u + (3 : ℝ) ^ k * u ^ 2) * (1 + u) + u := by
              gcongr
        _ ≤ ((k : ℝ) + 1) * u + (3 : ℝ) ^ k * 3 * u ^ 2 := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hk) hu2,
                mul_nonneg hp (sub_nonneg.mpr hu3)]
        _ = ((k : ℝ) + 1) * u + ((3 : ℝ) ^ k * 3) * u ^ 2 := by ring

private theorem p52_join_quad {u x y p q cp cq : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hcp : 0 ≤ cp) (hcq : 0 ≤ cq)
    (hx : |x| ≤ p * u + cp * u ^ 2)
    (hy : |y| ≤ q * u + cq * u ^ 2) :
    |p52Join x y| ≤
      (p + q) * u + (cp + cq + (p + cp) * (q + cq)) * u ^ 2 := by
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hx' : |x| ≤ (p + cp) * u := by
    nlinarith [mul_nonneg hcp (sub_nonneg.mpr hu2)]
  have hy' : |y| ≤ (q + cq) * u := by
    nlinarith [mul_nonneg hcq (sub_nonneg.mpr hu2)]
  have hxy : |x| * |y| ≤ (p + cp) * (q + cq) * u ^ 2 := by
    calc
      |x| * |y| ≤ ((p + cp) * u) * ((q + cq) * u) := by gcongr
      _ = (p + cp) * (q + cq) * u ^ 2 := by ring
  have htri : |p52Join x y| ≤ |x| + |y| + |x| * |y| := by
    unfold p52Join
    calc
      |x + y + x * y| ≤ |x + y| + |x * y| := abs_add_le _ _
      _ ≤ |x| + |y| + |x| * |y| := by
        rw [abs_mul]
        linarith [abs_add_le x y]
  linarith

private theorem p52_sum_error {n : ℕ} (v e : Fin n → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (he : ∀ i, |e i| ≤ t) :
    |(∑ i, v i * (1 + e i)) - ∑ i, v i| ≤
      t * ∑ i, |v i| := by
  have hid : (∑ i, v i * (1 + e i)) - ∑ i, v i = ∑ i, v i * e i := by
    simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
    ring
  rw [hid]
  calc
    |∑ i, v i * e i| ≤ ∑ i, |v i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |v i| * |e i| := by simp only [abs_mul]
    _ ≤ ∑ i, |v i| * t := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (he i) (abs_nonneg _)
    _ = t * ∑ i, |v i| := by rw [← Finset.sum_mul]; ring

private noncomputable def p52CoeffC (P CP : ℝ) (k : ℕ) : ℝ :=
  CP + (3 : ℝ) ^ k + (P + CP) * ((k : ℝ) + (3 : ℝ) ^ k)

private theorem p52_coeffC_nonneg {P CP : ℝ} (hP : 0 ≤ P)
    (hCP : 0 ≤ CP) (k : ℕ) : 0 ≤ p52CoeffC P CP k := by
  unfold p52CoeffC
  positivity

private theorem p52_coeff_join {u α e P CP : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hP : 0 ≤ P) (hCP : 0 ≤ CP)
    (hα : |α| ≤ P * u + CP * u ^ 2)
    (he : |e| ≤ p52Err u k) :
    |p52Join α e| ≤
      (P + (k : ℝ)) * u + p52CoeffC P CP k * u ^ 2 := by
  have he' : |e| ≤ (k : ℝ) * u + (3 : ℝ) ^ k * u ^ 2 :=
    he.trans (p52_err_quad hu hu1 k)
  have h := p52_join_quad hu hu1 hP (Nat.cast_nonneg k) hCP
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) k) hα he'
  simpa only [p52CoeffC] using h

private noncomputable def p52RatioC (Ln Cn Ld Cd : ℝ) : ℝ :=
  Cn + Cd + 2 * (Ld + Cd) * (Ln + Ld + Cn + Cd)

private theorem p52_ratio_bound
    {u D Dh g Ln Cn Ld Cd : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hLn : 0 ≤ Ln) (hCn : 0 ≤ Cn)
    (hLd : 0 ≤ Ld) (hCd : 0 ≤ Cd)
    (hD : D ≠ 0)
    (hsmall : (Ld + Cd) * u ≤ 1 / 2)
    (hnum : |g - 1| ≤ Ln * u + Cn * u ^ 2)
    (hden : |Dh - D| ≤ (Ld * u + Cd * u ^ 2) * |D|) :
    Dh ≠ 0 ∧
      |g * D / Dh - 1| ≤
        (Ln + Ld) * u + p52RatioC Ln Cn Ld Cd * u ^ 2 := by
  let s := Ln * u + Cn * u ^ 2
  let t := Ld * u + Cd * u ^ 2
  let L := Ln + Ld
  let Q := Cn + Cd
  let K := Ld + Cd
  let R := L * u + p52RatioC Ln Cn Ld Cd * u ^ 2
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hX0 : 0 ≤ s + t := by linarith
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have htK : t ≤ K * u := by
    dsimp [t, K]
    nlinarith [mul_nonneg hCd (sub_nonneg.mpr hu2)]
  have htHalf : t ≤ 1 / 2 := htK.trans hsmall
  have htm : 0 < 1 - t := by linarith
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hDhLower : |D| * (1 - t) ≤ |Dh| := by
    have htri : |D| - |Dh| ≤ |Dh - D| := by
      calc
        |D| - |Dh| ≤ |D - Dh| := abs_sub_abs_le_abs_sub D Dh
        _ = |Dh - D| := by rw [abs_sub_comm]
    nlinarith [hden]
  have hDhAbs : 0 < |Dh| := lt_of_lt_of_le (mul_pos hDabs htm) hDhLower
  have hDh : Dh ≠ 0 := abs_pos.mp hDhAbs
  have hnumabs : |g * D - Dh| ≤ |D| * (s + t) := by
    have hid : g * D - Dh = (g - 1) * D + (D - Dh) := by ring
    rw [hid]
    calc
      |(g - 1) * D + (D - Dh)| ≤ |(g - 1) * D| + |D - Dh| := abs_add_le _ _
      _ = |g - 1| * |D| + |Dh - D| := by
        rw [abs_mul, abs_sub_comm D Dh]
      _ ≤ s * |D| + t * |D| := by
        gcongr
      _ = |D| * (s + t) := by ring
  have hX : s + t ≤ L * u + Q * u ^ 2 := by
    dsimp [s, t, L, Q]
    nlinarith
  have hXweak : s + t ≤ (L + Q) * u := by
    nlinarith [mul_nonneg hQ0 (sub_nonneg.mpr hu2)]
  have hXt : (s + t) * t ≤ (L + Q) * K * u ^ 2 := by
    calc
      (s + t) * t ≤ ((L + Q) * u) * (K * u) := by gcongr
      _ = (L + Q) * K * u ^ 2 := by ring
  have hR : (s + t) * (1 + 2 * t) ≤ R := by
    dsimp [R, p52RatioC, L, Q, K] at *
    nlinarith [hX, hXt]
  have hinv : 1 / (1 - t) ≤ 1 + 2 * t := by
    apply (div_le_iff₀ htm).2
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr (by linarith : 0 ≤ 1 - 2 * t))]
  have hratio : |g * D / Dh - 1| = |g * D - Dh| / |Dh| := by
    have hid : g * D / Dh - 1 = (g * D - Dh) / Dh := by
      field_simp [hDh]
    rw [hid, abs_div]
  refine ⟨hDh, ?_⟩
  rw [hratio]
  calc
    |g * D - Dh| / |Dh| ≤ (|D| * (s + t)) / |Dh| := by
      exact div_le_div_of_nonneg_right hnumabs hDhAbs.le
    _ ≤ (|D| * (s + t)) / (|D| * (1 - t)) := by
      apply div_le_div_of_nonneg_left (mul_nonneg hDabs.le hX0)
        (mul_pos hDabs htm) hDhLower
    _ = (s + t) / (1 - t) := by
      field_simp [ne_of_gt hDabs]
    _ = (s + t) * (1 / (1 - t)) := by ring
    _ ≤ (s + t) * (1 + 2 * t) := mul_le_mul_of_nonneg_left hinv hX0
    _ ≤ R := hR

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
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hM)
  let cn0 : ℝ := p52CoeffC A CA (n + 1)
  let ln0 : ℝ := A + ((n + 1 : ℕ) : ℝ)
  let cn : ℝ := cn0 + (ln0 + cn0)
  let ln : ℝ := ln0 + 1
  let cd0 : ℝ := p52CoeffC B CB m
  let ld0 : ℝ := B + (m : ℝ)
  let ld : ℝ := ld0 * betaBound
  let cd : ℝ := cd0 * betaBound
  let u0 : ℝ := 1 / (2 * (ld + cd + 1))
  let C : ℝ := p52RatioC ln cn ld cd
  have hcn0 : 0 ≤ cn0 := p52_coeffC_nonneg hA hCA _
  have hcd0 : 0 ≤ cd0 := p52_coeffC_nonneg hB hCB _
  have hln0 : 0 ≤ ln0 := by dsimp [ln0]; positivity
  have hld0 : 0 ≤ ld0 := by dsimp [ld0]; positivity
  have hcn : 0 ≤ cn := by dsimp [cn]; positivity
  have hln : 0 ≤ ln := by dsimp [ln]; positivity
  have hld : 0 ≤ ld := by dsimp [ld]; positivity
  have hcd : 0 ≤ cd := by dsimp [cd]; positivity
  have hC : 0 ≤ C := by dsimp [C, p52RatioC]; positivity
  have hu0 : 0 < u0 := by dsimp [u0]; positivity
  have hu01 : u0 ≤ 1 := by
    dsimp [u0]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (ld + cd + 1))).2
    nlinarith
  have hu0small : (ld + cd) * u0 ≤ 1 / 2 := by
    dsimp [u0]
    have hp : 0 < 2 * (ld + cd + 1) := by positivity
    rw [mul_one_div]
    apply (div_le_iff₀ hp).2
    nlinarith
  refine ⟨u0, C, hu0, hC, ?_⟩
  intro fp ahat bhat hu hα hβ
  have hu1 : fp.u ≤ 1 := hu.trans hu01
  have hsmall : (ld + cd) * fp.u ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hu (by positivity)).trans hu0small
  let α : Fin (n + 1) → ℝ := fun i => Classical.choose (hα i)
  let β : Fin (m + 1) → ℝ := fun j => Classical.choose (hβ j)
  have hαeq (i : Fin (n + 1)) : ahat i = a i * (1 + α i) :=
    (Classical.choose_spec (hα i)).1
  have hαerr (i : Fin (n + 1)) :
      |α i| ≤ A * fp.u + CA * fp.u ^ 2 :=
    (Classical.choose_spec (hα i)).2
  have hβeq (j : Fin (m + 1)) : bhat j = b j * (1 + β j) :=
    (Classical.choose_spec (hβ j)).1
  have hβerr (j : Fin (m + 1)) :
      |β j| ≤ B * fp.u + CB * fp.u ^ 2 :=
    (Classical.choose_spec (hβ j)).2
  obtain ⟨ed, hdot, hed⟩ := p52_dot_rep fp n ahat f
  obtain ⟨es, hsum, hes⟩ := p52_recursive_sum_rep fp m bhat
  let η : Fin (n + 1) → ℝ := fun i => p52Join (α i) (ed i)
  let θ : Fin (m + 1) → ℝ := fun j => p52Join (β j) (es j)
  have hη (i : Fin (n + 1)) :
      |η i| ≤ ln0 * fp.u + cn0 * fp.u ^ 2 := by
    simpa [η, ln0, cn0] using
      p52_coeff_join fp.u_nonneg hu1 hA hCA (hαerr i) (hed i)
  have hθ (j : Fin (m + 1)) :
      |θ j| ≤ ld0 * fp.u + cd0 * fp.u ^ 2 := by
    simpa [θ, ld0, cd0] using
      p52_coeff_join fp.u_nonneg hu1 hB hCB (hβerr j) (hes j)
  have hnumrep : p52RoundedDotProduct fp (n + 1) ahat f =
      ∑ i : Fin (n + 1), (a i * f i) * (1 + η i) := by
    rw [hdot]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hαeq i]
    dsimp [η]
    rw [← p52_one_join]
    ring
  have hdenrep : p52RecursiveSum fp (m + 1) bhat =
      ∑ j : Fin (m + 1), b j * (1 + θ j) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hβeq j]
    dsimp [θ]
    rw [← p52_one_join]
    ring
  let D : ℝ := ∑ j : Fin (m + 1), b j
  let Dh : ℝ := p52RecursiveSum fp (m + 1) bhat
  have hD : D ≠ 0 := hD0
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hsumabs : (∑ j : Fin (m + 1), |b j|) ≤ betaBound * |D| := by
    have hb := hbetaBound
    unfold p52DenominatorCondition at hb
    exact (div_le_iff₀ hDabs).1 hb
  have ht0 : 0 ≤ ld0 * fp.u + cd0 * fp.u ^ 2 :=
    add_nonneg (mul_nonneg hld0 fp.u_nonneg)
      (mul_nonneg hcd0 (sq_nonneg _))
  have hdenerror : |Dh - D| ≤
      (ld * fp.u + cd * fp.u ^ 2) * |D| := by
    calc
      |Dh - D| ≤
          (ld0 * fp.u + cd0 * fp.u ^ 2) *
            (∑ j : Fin (m + 1), |b j|) := by
              change |p52RecursiveSum fp (m + 1) bhat -
                (∑ j : Fin (m + 1), b j)| ≤ _
              rw [hdenrep]
              exact p52_sum_error b θ _ ht0 hθ
      _ ≤ (ld0 * fp.u + cd0 * fp.u ^ 2) * (betaBound * |D|) :=
        mul_le_mul_of_nonneg_left hsumabs ht0
      _ = (ld * fp.u + cd * fp.u ^ 2) * |D| := by
        dsimp [ld, cd]
        ring
  have hDh : Dh ≠ 0 := by
    have hzero : |(1 : ℝ) - 1| ≤ ln * fp.u + cn * fp.u ^ 2 := by
      simp
      exact add_nonneg (mul_nonneg hln fp.u_nonneg)
        (mul_nonneg hcn (sq_nonneg _))
    exact (p52_ratio_bound fp.u_nonneg hu1 hln hcn hld hcd hD
      hsmall hzero hdenerror).1
  obtain ⟨δ, hδ, hdiv⟩ :=
    fp.model_div (p52RoundedDotProduct fp (n + 1) ahat f) Dh hDh
  let ξ : Fin (n + 1) → ℝ := fun i => p52Join (η i) δ
  have hξ (i : Fin (n + 1)) :
      |ξ i| ≤ ln * fp.u + cn * fp.u ^ 2 := by
    have h := p52_join_quad fp.u_nonneg hu1 hln0 (by norm_num : (0 : ℝ) ≤ 1)
      hcn0 (by norm_num : (0 : ℝ) ≤ 0) (hη i)
      (by simpa using hδ)
    simpa [ξ, ln, cn] using h
  let fhat : Fin (n + 1) → ℝ := fun i =>
    f i * ((1 + ξ i) * D / Dh)
  refine ⟨fhat, ?_, ?_⟩
  · dsimp [p52ComputedQuotient]
    rw [hdiv, hnumrep]
    have hprod :
        (∑ i : Fin (n + 1), (a i * f i) * (1 + η i)) * (1 + δ) =
          ∑ i : Fin (n + 1), (a i * f i) * (1 + ξ i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      change (a i * f i * (1 + η i)) * (1 + δ) =
        a i * f i * (1 + p52Join (η i) δ)
      calc
        (a i * f i * (1 + η i)) * (1 + δ) =
            (a i * f i) * ((1 + η i) * (1 + δ)) := by ring
        _ = (a i * f i) * (1 + p52Join (η i) δ) := by
          rw [p52_one_join]
    have hfhatsum : (∑ i : Fin (n + 1), a i * fhat i) =
        (∑ i : Fin (n + 1), (a i * f i) * (1 + ξ i)) * (D / Dh) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      change a i * (f i * ((1 + ξ i) * D / Dh)) =
        (a i * f i * (1 + ξ i)) * (D / Dh)
      ring
    change (∑ i : Fin (n + 1), a i * f i * (1 + η i)) / Dh * (1 + δ) =
      (∑ i : Fin (n + 1), a i * fhat i) / D
    rw [hfhatsum, ← hprod]
    field_simp [hD, hDh]
  · have hR0 : 0 ≤ (ln + ld) * fp.u + C * fp.u ^ 2 :=
      add_nonneg (mul_nonneg (add_nonneg hln hld) fp.u_nonneg)
        (mul_nonneg hC (sq_nonneg _))
    have hnorm : ‖fhat - f‖ ≤
        ((ln + ld) * fp.u + C * fp.u ^ 2) * ‖f‖ := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR0 (norm_nonneg f))).2
      intro i
      have hnum_i : |(1 + ξ i) - 1| ≤ ln * fp.u + cn * fp.u ^ 2 := by
        simpa only [add_sub_cancel_left] using hξ i
      have hratio := (p52_ratio_bound (g := 1 + ξ i) fp.u_nonneg hu1
        hln hcn hld hcd hD hsmall hnum_i hdenerror).2
      have hfi : |f i| ≤ ‖f‖ := by simpa using norm_le_pi_norm f i
      have hid : fhat i - f i =
          f i * (((1 + ξ i) * D / Dh) - 1) := by dsimp [fhat]; ring
      simp only [Pi.sub_apply, Real.norm_eq_abs, hid, abs_mul]
      calc
        |f i| * |(1 + ξ i) * D / Dh - 1| =
            |(1 + ξ i) * D / Dh - 1| * |f i| := mul_comm _ _
        _ ≤ ((ln + ld) * fp.u + C * fp.u ^ 2) * ‖f‖ :=
          mul_le_mul hratio hfi (abs_nonneg _) hR0
    simpa [ln, ln0, ld, ld0, C, Nat.succ_eq_add_one, add_assoc, add_comm,
      add_left_comm, mul_add, add_mul] using hnorm

end VSCLReuse

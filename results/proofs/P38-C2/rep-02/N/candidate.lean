import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p38_mul_err (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul]
  have heq : a * b * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b)))

private lemma p38_mul_abs (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_mul a b| ≤ (1 + fp.u) * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul, abs_mul]
  have h : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simp only [abs_one]; linarith
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left h (abs_nonneg (a * b)))

private lemma p38_add_err (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * (|a| + |b|) := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  rw [hadd]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  calc
    |a + b| * |δ| ≤ |a + b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|a| + |b|) * fp.u :=
      mul_le_mul_of_nonneg_right (abs_add_le _ _) fp.u_nonneg
    _ = fp.u * (|a| + |b|) := by ring

private lemma p38_step_err (fp : P38FPModel) (R S a b : ℝ) :
    |fp.fl_add R (fp.fl_mul a b) - (S + a * b)| ≤
      (1 + fp.u) * |R - S| + fp.u * |S| +
        (2 * fp.u + fp.u ^ 2) * |a * b| := by
  let M := fp.fl_mul a b
  have h₁ := p38_add_err fp R M
  have h₂ := p38_mul_err fp a b
  have h₃ := p38_mul_abs fp a b
  have hR : |R| ≤ |R - S| + |S| := by
    convert abs_add_le (R - S) S using 1 <;> ring
  have ht : |fp.fl_add R M - (S + a * b)| ≤
      |fp.fl_add R M - (R + M)| + |R - S| + |M - a * b| := by
    have heq : fp.fl_add R M - (S + a * b) =
        (fp.fl_add R M - (R + M)) + (R - S) + (M - a * b) := by ring
    rw [heq]
    calc
      |(fp.fl_add R M - (R + M)) + (R - S) + (M - a * b)| ≤
          |(fp.fl_add R M - (R + M)) + (R - S)| + |M - a * b| := abs_add_le _ _
      _ ≤ |fp.fl_add R M - (R + M)| + |R - S| + |M - a * b| := by
        linarith [abs_add_le (fp.fl_add R M - (R + M)) (R - S)]
  dsimp [M] at *
  nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hR),
    mul_nonneg fp.u_nonneg (sub_nonneg.mpr h₃)]

private lemma p38_coeff_step (u q N k : ℝ)
    (hu : 0 ≤ u) (hq : 0 ≤ q) (hN : 1 ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N)
    (hqu : q = u + N * u * q) :
    (1 + u) * (k * q) + u ≤ (k + 1) * q ∧
      2 * u + u ^ 2 ≤ (k + 1) * q := by
  have huq : 0 ≤ u * q := mul_nonneg hu hq
  have hkn : 0 ≤ (N - k) * (u * q) :=
    mul_nonneg (sub_nonneg.mpr hkN) huq
  have hN1 : 0 ≤ (N - 1) * (u * q) :=
    mul_nonneg (sub_nonneg.mpr hN) huq
  have hq_u : u ≤ q := by nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ N) hu) hq]
  have hsq : u ^ 2 ≤ u * q := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hq_u)]
  have hnew : 2 * u + u ^ 2 ≤ 2 * q := by nlinarith [hN1]
  have hkq : 0 ≤ (k - 1) * q := mul_nonneg (sub_nonneg.mpr hk) hq
  constructor <;> nlinarith [hkn, hnew, hkq]

private lemma p38_fold_bound (fp : P38FPModel) (n : ℕ)
    (hvalid : P38GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x y : Fin k → ℝ),
      |Fin.foldl k
          (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 -
        ∑ i : Fin k, x i * y i| ≤
      ((k : ℝ) * (fp.u / (1 - (n : ℝ) * fp.u))) *
        ∑ i : Fin k, |x i * y i| := by
  let q : ℝ := fp.u / (1 - (n : ℝ) * fp.u)
  have hden : 0 < 1 - (n : ℝ) * fp.u := sub_pos.mpr hvalid
  have hq : 0 ≤ q := div_nonneg fp.u_nonneg (le_of_lt hden)
  have hqu : q = fp.u + (n : ℝ) * fp.u * q := by
    have hmul : q * (1 - (n : ℝ) * fp.u) = fp.u := by
      exact div_mul_cancel₀ fp.u (ne_of_gt hden)
    nlinarith [hmul]
  have hq_u : fp.u ≤ q := by
    rw [hqu]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) hq)
  intro k
  induction k with
  | zero =>
      intro hk x y
      simp
  | succ k ih =>
      intro hk x y
      let xp : Fin k → ℝ := fun i => x i.castSucc
      let yp : Fin k → ℝ := fun i => y i.castSucc
      let R : ℝ := Fin.foldl k
        (fun acc i => fp.fl_add acc (fp.fl_mul (xp i) (yp i))) 0
      let S : ℝ := ∑ i : Fin k, xp i * yp i
      let T : ℝ := ∑ i : Fin k, |xp i * yp i|
      let a : ℝ := x (Fin.last k)
      let b : ℝ := y (Fin.last k)
      have hk' : k ≤ n := Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      have hih : |R - S| ≤ ((k : ℝ) * q) * T := by
        simpa only [R, S, T, xp, yp, q] using ih hk' xp yp
      have hS : |S| ≤ T := by
        simpa only [S, T] using
          (Finset.abs_sum_le_sum_abs (fun i : Fin k => xp i * yp i) Finset.univ)
      have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => abs_nonneg _)
      have hprod : 0 ≤ |a * b| := abs_nonneg _
      have hfold : Fin.foldl (k + 1)
          (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 =
          fp.fl_add R (fp.fl_mul a b) := by
        simp only [Fin.foldl_succ_last, R, xp, yp, a, b]
      have hsum : (∑ i : Fin (k + 1), x i * y i) = S + a * b := by
        simp only [Fin.sum_univ_castSucc, S, xp, yp, a, b]
      have hmass : (∑ i : Fin (k + 1), |x i * y i|) = T + |a * b| := by
        simp only [Fin.sum_univ_castSucc, T, xp, yp, a, b]
      rw [hfold, hsum, hmass]
      by_cases hk0 : k = 0
      · subst k
        have hm := (p38_mul_err fp a b).trans
          (mul_le_mul_of_nonneg_right hq_u hprod)
        simpa [R, S, T, fp.fl_add_zero, q] using hm
      · have hk1 : (1 : ℝ) ≤ k := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0)
        have hN : (1 : ℝ) ≤ n := by
          exact_mod_cast (Nat.le_trans (Nat.one_le_iff_ne_zero.mpr hk0) hk')
        have hkN : (k : ℝ) ≤ n := by exact_mod_cast hk'
        obtain ⟨hcold, hcnew⟩ :=
          p38_coeff_step fp.u q (n : ℝ) (k : ℝ)
            fp.u_nonneg hq hN hk1 hkN hqu
        have hstep := p38_step_err fp R S a b
        have hcoeffold :
            (1 + fp.u) * |R - S| ≤ (1 + fp.u) * (((k : ℝ) * q) * T) :=
          mul_le_mul_of_nonneg_left hih (by linarith [fp.u_nonneg])
        have hcoeffS : fp.u * |S| ≤ fp.u * T :=
          mul_le_mul_of_nonneg_left hS fp.u_nonneg
        have hboundold :
            ((1 + fp.u) * ((k : ℝ) * q) + fp.u) * T ≤
              (((k : ℝ) + 1) * q) * T :=
          mul_le_mul_of_nonneg_right hcold hT
        have hboundnew :
            (2 * fp.u + fp.u ^ 2) * |a * b| ≤
              (((k : ℝ) + 1) * q) * |a * b| :=
          mul_le_mul_of_nonneg_right hcnew hprod
        push_cast
        nlinarith

private lemma p38_dot_bound (fp : P38FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P38GammaValid fp.u n) :
    |p38RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p38Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  have hfold : p38RoundedDotProduct fp n x y =
      Fin.foldl n
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) 0 := by
    cases n with
    | zero => simp [p38RoundedDotProduct]
    | succ n =>
        simp only [p38RoundedDotProduct, Fin.foldl_succ, fp.fl_add_zero]
  rw [hfold]
  have hcoeff : (n : ℝ) * (fp.u / (1 - (n : ℝ) * fp.u)) =
      p38Gamma fp.u n := by
    unfold p38Gamma
    ring
  rw [← hcoeff]
  simpa only [abs_mul] using p38_fold_bound fp n hvalid n le_rfl x y

/-- One fan-in node product error propagated through a left factor. -/
theorem p38_c2_fanin_one_node_propagated_error
    (fp : P38FPModel) (r m n p : ℕ)
    (L : P38Matrix r m) (A : P38Matrix m n) (B : P38Matrix n p)
    (hvalid : P38GammaValid fp.u n) :
    ∀ i : Fin r, ∀ j : Fin p,
      |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| ≤
      p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
  -- PROOF_START P38-C2-H001
  intro i j
  have hlocal (k : Fin m) :
      |p38RoundedMatMul fp A B k j - p38MatMul A B k j| ≤
        p38Gamma fp.u n *
          ∑ t : Fin n, |A k t| * |B t j| := by
    simpa [p38RoundedMatMul, p38MatMul] using
      p38_dot_bound fp n (A k) (fun t => B t j) hvalid
  calc
    |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| ≤
        ∑ k : Fin m, |L i k| *
          |p38RoundedMatMul fp A B k j - p38MatMul A B k j| := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs
          (fun k : Fin m => L i k *
            (p38RoundedMatMul fp A B k j - p38MatMul A B k j)) Finset.univ)
    _ ≤ ∑ k : Fin m, |L i k| *
        (p38Gamma fp.u n *
          ∑ t : Fin n, |A k t| * |B t j|) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hlocal k) (abs_nonneg _)
    _ = p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end VSCLReuse

import VSCLReuse.P39.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p39_mul_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * (|x| * |y|) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_mul x y
  rw [h]
  have hh : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [hh, abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg x) (abs_nonneg y))]

private lemma p39_mul_abs (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_mul x y| ≤ (1 + fp.u) * (|x| * |y|) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_mul x y
  rw [h, abs_mul, abs_mul]
  have hδ' : |1 + δ| ≤ 1 + fp.u := by
    calc |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ = 1 + |δ| := by simp
      _ ≤ 1 + fp.u := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hδ' (mul_nonneg (abs_nonneg x) (abs_nonneg y))]

private lemma p39_add_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, h⟩ := fp.model_add x y
  rw [h]
  have hh : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [hh, abs_mul]
  calc
    |x + y| * |δ| ≤ (|x| + |y|) * |δ| :=
      mul_le_mul_of_nonneg_right (abs_add_le x y) (abs_nonneg _)
    _ ≤ (|x| + |y|) * fp.u :=
      mul_le_mul_of_nonneg_left hδ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = fp.u * (|x| + |y|) := by ring

private lemma p39_dot_step_error (fp : P39FPModel) (a s x y : ℝ) :
    |fp.fl_add a (fp.fl_mul x y) - (s + x * y)| ≤
      (1 + fp.u) * |a - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by
  let b := fp.fl_mul x y
  have hb : |b| ≤ (1 + fp.u) * (|x| * |y|) := p39_mul_abs fp x y
  have hbe : |b - x * y| ≤ fp.u * (|x| * |y|) := p39_mul_error fp x y
  have ha : |a| ≤ |a - s| + |s| := by
    calc |a| = |(a - s) + s| := by ring
      _ ≤ |a - s| + |s| := abs_add_le _ _
  have hsum : |a| + |b| ≤ |a - s| + |s| +
      (1 + fp.u) * (|x| * |y|) := by linarith
  have hsum' := mul_le_mul_of_nonneg_left hsum fp.u_nonneg
  have htri : |fp.fl_add a b - (s + x * y)| ≤
      |fp.fl_add a b - (a + b)| + |a - s| + |b - x * y| := by
    have he : fp.fl_add a b - (s + x * y) =
        (fp.fl_add a b - (a + b)) + (a - s) + (b - x * y) := by ring
    rw [he]
    calc
      |(fp.fl_add a b - (a + b)) + (a - s) + (b - x * y)| ≤
          |(fp.fl_add a b - (a + b)) + (a - s)| + |b - x * y| :=
            abs_add_le _ _
      _ ≤ |fp.fl_add a b - (a + b)| + |a - s| + |b - x * y| := by
          linarith [abs_add_le (fp.fl_add a b - (a + b)) (a - s)]
  have hae := p39_add_error fp a b
  have hp : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  dsimp [b] at *
  nlinarith

private lemma p39_gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P39GammaValid u n) : 0 ≤ p39Gamma u n := by
  unfold p39Gamma P39GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p39_pow_denom_bound (u : ℝ) (hu : 0 ≤ u) :
    ∀ m : ℕ, (m : ℝ) * u < 1 →
      (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ 1 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      intro hv
      have hv' : (m : ℝ) * u < 1 := by
        have hc : (↑(m + 1) : ℝ) * u = (m : ℝ) * u + u := by
          push_cast; ring
        rw [hc] at hv
        linarith
      have hp : 0 ≤ (1 + u) ^ m := pow_nonneg (by linarith) _
      have hs : (1 + u) * (1 - (↑(m + 1) : ℝ) * u) ≤
          1 - (m : ℝ) * u := by
        have hm : 0 ≤ (↑(m + 1) : ℝ) := by positivity
        have hsq := mul_nonneg hm (sq_nonneg u)
        push_cast at *
        nlinarith
      calc
        (1 + u) ^ (m + 1) * (1 - (↑(m + 1) : ℝ) * u) =
            (1 + u) ^ m * ((1 + u) * (1 - (↑(m + 1) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ m * (1 - (m : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hs hp
        _ ≤ 1 := ih hv'

private lemma p39_pow_le_gamma (u : ℝ) (hu : 0 ≤ u)
    (n : ℕ) (hv : P39GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p39Gamma u n := by
  have hd : 0 < 1 - (n : ℝ) * u := by unfold P39GammaValid at hv; linarith
  unfold p39Gamma
  apply (le_div_iff₀ hd).2
  have hh := p39_pow_denom_bound u hu n hv
  nlinarith

private lemma p39_pow_le_pow (u : ℝ) (hu : 0 ≤ u) {m n : ℕ} (h : m ≤ n) :
    (1 + u) ^ m ≤ (1 + u) ^ n := by
  exact pow_le_pow_right₀ (by linarith) h

private lemma p39_dot_bound (fp : P39FPModel) (m : ℕ)
    (x y : Fin m → ℝ) :
    |p39RoundedDotProduct fp m x y - ∑ t : Fin m, x t * y t| ≤
      ((1 + fp.u) ^ m - 1) *
        ∑ t : Fin m, |x t| * |y t| := by
  induction m with
  | zero => simp [p39RoundedDotProduct]
  | succ m ih =>
      cases m with
      | zero =>
          have h := p39_mul_error fp (x 0) (y 0)
          simpa [p39RoundedDotProduct, Fin.sum_univ_one] using h
      | succ m =>
          let x' : Fin (m + 1) → ℝ := fun t => x t.castSucc
          let y' : Fin (m + 1) → ℝ := fun t => y t.castSucc
          let a := p39RoundedDotProduct fp (m + 1) x' y'
          let s := ∑ t : Fin (m + 1), x' t * y' t
          let A := ∑ t : Fin (m + 1), |x' t| * |y' t|
          let b := |x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|
          have hprev : |a - s| ≤ ((1 + fp.u) ^ (m + 1) - 1) * A :=
            ih x' y'
          have hs : |s| ≤ A := by
            dsimp [s, A]
            calc
              |∑ t : Fin (m + 1), x' t * y' t| ≤
                  ∑ t : Fin (m + 1), |x' t * y' t| :=
                    Finset.abs_sum_le_sum_abs _ _
              _ = ∑ t : Fin (m + 1), |x' t| * |y' t| := by
                    simp_rw [abs_mul]
          have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hb : 0 ≤ b := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hstep := p39_dot_step_error fp a s
            (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          have hfactor : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hprev' := mul_le_mul_of_nonneg_left hprev hfactor
          have hs' := mul_le_mul_of_nonneg_left hs fp.u_nonneg
          have hpow : (1 + fp.u) ^ (2 : ℕ) ≤
              (1 + fp.u) ^ (m + 2) :=
            p39_pow_le_pow fp.u fp.u_nonneg (by omega)
          have hcoef : 2 * fp.u + fp.u ^ 2 ≤
              (1 + fp.u) ^ (m + 2) - 1 := by
            norm_num [pow_two] at hpow ⊢
            nlinarith
          have hcoef' := mul_le_mul_of_nonneg_right hcoef hb
          have hpow' : (1 + fp.u) * ((1 + fp.u) ^ (m + 1) - 1) + fp.u =
              (1 + fp.u) ^ (m + 2) - 1 := by
            rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
            ring
          have hdot : p39RoundedDotProduct fp (m + 2) x y =
              fp.fl_add a (fp.fl_mul (x (Fin.last (m + 1)))
                (y (Fin.last (m + 1)))) := by
            rw [p39RoundedDotProduct, Fin.foldl_succ_last]
            simp [a, x', y', p39RoundedDotProduct, Fin.foldl_succ,
              Fin.succ_last, Fin.castSucc_succ]
          have hsum : (∑ t : Fin (m + 2), x t * y t) =
              s + x (Fin.last (m + 1)) * y (Fin.last (m + 1)) := by
            rw [Fin.sum_univ_castSucc]
          have habs : (∑ t : Fin (m + 2), |x t| * |y t|) = A + b := by
            rw [Fin.sum_univ_castSucc]
          rw [hdot, hsum, habs]
          dsimp [b] at *
          have hfin : |fp.fl_add a
                (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) -
                (s + x (Fin.last (m + 1)) * y (Fin.last (m + 1)))| ≤
              ((1 + fp.u) ^ (m + 2) - 1) *
                (A + |x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|) := by
            calc
              _ ≤ (1 + fp.u) * |a - s| + fp.u * |s| +
                  (2 * fp.u + fp.u ^ 2) *
                    (|x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|) := hstep
              _ ≤ (1 + fp.u) * (((1 + fp.u) ^ (m + 1) - 1) * A) +
                  fp.u * A +
                  (2 * fp.u + fp.u ^ 2) *
                    (|x (Fin.last (m + 1))| * |y (Fin.last (m + 1))|) := by
                    gcongr
              _ ≤ _ := by
                nlinarith [hcoef']
          exact hfin

private lemma p39_dot_gamma_bound (fp : P39FPModel) (n m : ℕ)
    (hv : P39GammaValid fp.u n) (hm : m ≤ n) (x y : Fin m → ℝ) :
    |p39RoundedDotProduct fp m x y - ∑ t : Fin m, x t * y t| ≤
      p39Gamma fp.u n * ∑ t : Fin m, |x t| * |y t| := by
  have hcoef : (1 + fp.u) ^ m - 1 ≤ p39Gamma fp.u n := by
    have hp := p39_pow_le_pow fp.u fp.u_nonneg hm
    have hg := p39_pow_le_gamma fp.u fp.u_nonneg n hv
    linarith
  have hsum : 0 ≤ ∑ t : Fin m, |x t| * |y t| :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact (p39_dot_bound fp m x y).trans
    (mul_le_mul_of_nonneg_right hcoef hsum)

private lemma p39_steps_preserve (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) : ∀ (k : ℕ) (hk : k ≤ n)
    (X : P39Matrix n n) (i j : Fin n), k ≤ j.val →
      p39Method2SourceSteps fp n L k hk X i j = X i j := by
  intro k
  induction k with
  | zero =>
      intro hk X i j hj
      rfl
  | succ k ih =>
      intro hk X i j hj
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hne : j ≠ (⟨k, hk⟩ : Fin n) := by
        intro he
        have he' := congrArg Fin.val he
        simp at he'
        omega
      change p39Method2SourceSteps fp n L k hk'
        (p39Method2SourceStep fp n L X ⟨k, hk⟩) i j = X i j
      rw [ih hk' _ i j (by omega)]
      simp [p39Method2SourceStep, hne]

private lemma p39_step_tail_congr (fp : P39FPModel) (n : ℕ)
    (L X Y : P39Matrix n n) (j i : Fin n)
    (h : ∀ t : Fin n, j.val < t.val → X i t = Y i t) :
    p39Method2SourceStep fp n L X j i j =
      p39Method2SourceStep fp n L Y j i j := by
  by_cases hi : i = j
  · simp [p39Method2SourceStep, hi]
  by_cases hlt : j.val < i.val
  · have ht : (fun t : Fin (n - j.val - 1) =>
        X i ⟨j.val + 1 + t.val, by omega⟩) =
        (fun t : Fin (n - j.val - 1) =>
        Y i ⟨j.val + 1 + t.val, by omega⟩) := by
      funext t
      apply h
      change j.val < j.val + 1 + t.val
      omega
    have hlt' : j < i := hlt
    simp [p39Method2SourceStep, hi, hlt', ht]
  · have hlt' : ¬ j < i := hlt
    simp [p39Method2SourceStep, hi, hlt']

private lemma p39_steps_rule (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) : ∀ (k : ℕ) (hk : k ≤ n)
    (X : P39Matrix n n) (i j : Fin n), j.val < k →
      let Y := p39Method2SourceSteps fp n L k hk X
      Y i j = p39Method2SourceStep fp n L Y j i j := by
  intro k
  induction k with
  | zero =>
      intro hk X i j hj
      omega
  | succ k ih =>
      intro hk X i j hj
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      let q : Fin n := ⟨k, hk⟩
      let X' := p39Method2SourceStep fp n L X q
      let Y := p39Method2SourceSteps fp n L k hk' X'
      change Y i j = p39Method2SourceStep fp n L Y j i j
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · exact ih hk' X' i j hlt
      · have hjq : j = q := Fin.ext (by simpa [q] using heq)
        subst j
        have hentry : Y i q = X' i q :=
          p39_steps_preserve fp n L k hk' X' i q (by simp [q])
        have htail : ∀ t : Fin n, q.val < t.val → X' i t = Y i t := by
          intro t ht
          exact (p39_steps_preserve fp n L k hk' X' i t (by simp [q] at ht ⊢; omega)).symm
        have htail' : ∀ t : Fin n, q.val < t.val → X i t = X' i t := by
          intro t ht
          have hne : t ≠ q := ne_of_gt ht
          simp [X', p39Method2SourceStep, hne]
        calc
          Y i q = X' i q := hentry
          _ = p39Method2SourceStep fp n L X q i q := rfl
          _ = p39Method2SourceStep fp n L X' q i q :=
            p39_step_tail_congr fp n L X X' q i htail'
          _ = p39Method2SourceStep fp n L Y q i q :=
            p39_step_tail_congr fp n L X' Y q i htail

private def p39_tailEquiv (n : ℕ) (j : Fin n) :
    Fin (n - j.val - 1) ≃ {k : Fin n // j < k} where
  toFun t := ⟨⟨j.val + 1 + t.val, by omega⟩, by
    change j.val < j.val + 1 + t.val
    omega⟩
  invFun k := ⟨k.val.val - j.val - 1, by
    have hk : j.val < k.val.val := k.property
    have hkn : k.val.val < n := k.val.isLt
    omega⟩
  left_inv t := by
    apply Fin.ext
    change (j.val + 1 + t.val - j.val - 1) = t.val
    omega
  right_inv k := by
    apply Subtype.ext
    apply Fin.ext
    change j.val + 1 + (k.val.val - j.val - 1) = k.val.val
    have hk : j.val < k.val.val := k.property
    omega

private lemma p39_sum_tail (n : ℕ) (j : Fin n) (f : Fin n → ℝ)
    (hz : ∀ k : Fin n, k.val < j.val → f k = 0) :
    (∑ k : Fin n, f k) = f j +
      ∑ t : Fin (n - j.val - 1), f ((p39_tailEquiv n j t).val) := by
  classical
  have htail : (∑ k : Fin n, if j < k then f k else 0) =
      ∑ t : Fin (n - j.val - 1), f ((p39_tailEquiv n j t).val) := by
    calc
      (∑ k : Fin n, if j < k then f k else 0) =
          ∑ k ∈ (Finset.univ.filter (fun k : Fin n => j < k)), f k := by
            rw [Finset.sum_filter]
      _ = ∑ k : {k : Fin n // j < k}, f k.val := by
        rw [← Finset.sum_subtype_eq_sum_filter]
        simp
      _ = ∑ t : Fin (n - j.val - 1), f ((p39_tailEquiv n j t).val) := by
        exact (Fintype.sum_equiv (p39_tailEquiv n j)
          (fun t => f ((p39_tailEquiv n j t).val))
          (fun k => f k.val) (by intro t; rfl)).symm
  calc
    (∑ k : Fin n, f k) =
        ∑ k : Fin n, ((if k = j then f k else 0) +
          (if j < k then f k else 0)) := by
            apply Finset.sum_congr rfl
            intro k hk
            by_cases he : k = j
            · simp [he]
            by_cases hlt : j < k
            · simp [he, hlt]
            · have hkj : k.val < j.val := by
                have hne : k.val ≠ j.val := by
                  intro h
                  exact he (Fin.ext h)
                omega
              simp [he, hlt, hz k hkj]
    _ = f j + ∑ k : Fin n, if j < k then f k else 0 := by
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [htail]

private lemma p39_reciprocal_model (fp : P39FPModel) (l : ℝ)
    (hl : l ≠ 0) :
    ∃ δ : ℝ, |δ| ≤ fp.u ∧ fp.fl_div 1 l * l = 1 + δ := by
  obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 l hl
  refine ⟨δ, hδ, ?_⟩
  rw [hd]
  field_simp

private lemma p39_reciprocal_residual (fp : P39FPModel) (l : ℝ)
    (hl : l ≠ 0) (hu : fp.u < 1) :
    |fp.fl_div 1 l * l - 1| ≤
      (fp.u / (1 - fp.u)) * (|fp.fl_div 1 l| * |l|) := by
  obtain ⟨δ, hδ, hd⟩ := p39_reciprocal_model fp l hl
  have hδlo : -fp.u ≤ δ := (abs_le.mp hδ).1
  have hpos : 0 ≤ 1 + δ := by linarith
  have hab : |1 + δ| = 1 + δ := abs_of_nonneg hpos
  have hden : 0 < 1 - fp.u := by linarith
  have hcomp : fp.u ≤ (fp.u / (1 - fp.u)) * (1 + δ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    have hh : fp.u * (1 - fp.u) ≤ fp.u * (1 + δ) :=
      mul_le_mul_of_nonneg_left (by linarith) fp.u_nonneg
    nlinarith
  calc
    |fp.fl_div 1 l * l - 1| = |δ| := by rw [hd]; ring
    _ ≤ fp.u := hδ
    _ ≤ (fp.u / (1 - fp.u)) * (1 + δ) := hcomp
    _ = (fp.u / (1 - fp.u)) * (|fp.fl_div 1 l| * |l|) := by
      rw [← abs_mul, hd, hab]

private lemma p39_offdiag_scalar (fp : P39FPModel) (n : ℕ)
    (l p s A : ℝ) (hl : l ≠ 0) (hA : 0 ≤ A)
    (hpe : |p - s| ≤ p39Gamma fp.u n * A) (hs : |s| ≤ A) :
    |fp.fl_mul (-fp.fl_div 1 l) p * l + s| ≤
      (p39Gamma fp.u n +
        (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n)) * A := by
  let d := fp.fl_div 1 l
  let e := fp.fl_mul (-d) p - (-d) * p
  obtain ⟨δ, hδ, hd⟩ := p39_reciprocal_model fp l hl
  have hδup : δ ≤ fp.u := (abs_le.mp hδ).2
  have hdl : |d| * |l| ≤ 1 + fp.u := by
    rw [← abs_mul, hd]
    calc |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have he : |e| ≤ fp.u * (|d| * |p|) := by
    simpa [e, abs_neg] using p39_mul_error fp (-d) p
  have hel : |e * l| ≤ fp.u * (1 + fp.u) * |p| := by
    rw [abs_mul]
    calc
      |e| * |l| ≤ (fp.u * (|d| * |p|)) * |l| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ = fp.u * (|d| * |l|) * |p| := by ring
      _ ≤ fp.u * (1 + fp.u) * |p| := by
        have hh := mul_le_mul_of_nonneg_right hdl (abs_nonneg p)
        have hh' := mul_le_mul_of_nonneg_left hh fp.u_nonneg
        nlinarith
  have hδp : |δ * p| ≤ fp.u * |p| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  have htri : |fp.fl_mul (-d) p * l + s| ≤
      |e * l| + |p - s| + |δ * p| := by
    have hd' : d * l = 1 + δ := hd
    have hid : fp.fl_mul (-d) p * l + s = e * l - (p - s) - δ * p := by
      calc
        fp.fl_mul (-d) p * l + s = (e - d * p) * l + s := by
          dsimp [e]; ring
        _ = e * l - (d * l) * p + s := by ring
        _ = e * l - (1 + δ) * p + s := by rw [hd']
        _ = e * l - (p - s) - δ * p := by ring
    rw [hid]
    calc
      |e * l - (p - s) - δ * p| ≤
          |e * l - (p - s)| + |δ * p| := by
            simpa only [sub_eq_add_neg, abs_neg, neg_mul] using
              abs_add_le (e * l - (p - s)) (-(δ * p))
      _ ≤ |e * l| + |p - s| + |δ * p| := by
        linarith [abs_sub (e * l) (p - s)]
  have hp : |p| ≤ (1 + p39Gamma fp.u n) * A := by
    have hh : |p| ≤ |p - s| + |s| := by
      calc |p| = |(p - s) + s| := by ring
        _ ≤ |p - s| + |s| := abs_add_le _ _
    nlinarith
  have hc : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hp' := mul_le_mul_of_nonneg_left hp hc
  calc
    |fp.fl_mul (-d) p * l + s| ≤ |e * l| + |p - s| + |δ * p| := htri
    _ ≤ p39Gamma fp.u n * A + (2 * fp.u + fp.u ^ 2) * |p| := by
      nlinarith [hel, hpe, hδp]
    _ ≤ p39Gamma fp.u n * A +
        (2 * fp.u + fp.u ^ 2) * ((1 + p39Gamma fp.u n) * A) := by
          linarith
    _ = _ := by ring

/-- Complete Method 2 left-residual result of Lemma 2.1. -/
theorem p39_c2_method2_lemma21_left_residual
    (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (hdiag : ∀ j : Fin n, L j j ≠ 0)
    (hvalid : P39GammaValid fp.u n) (i j : Fin n) :
    let X := p39Method2SourceInverse fp n L
    |p39MatMul X L i j - if i = j then 1 else 0| ≤
      p39Method2SourceUniformCoefficient fp n *
        ∑ k : Fin n, |X i k| * |L k j| := by
  -- PROOF_START P39-C2-H001
  let X := p39Method2SourceInverse fp n L
  change |p39MatMul X L i j - (if i = j then 1 else 0)| ≤
    p39Method2SourceUniformCoefficient fp n *
      ∑ k : Fin n, |X i k| * |L k j|
  have hu : fp.u < 1 := by
    have hnNat : 1 ≤ n := by have := j.isLt; omega
    have hn : 1 ≤ (n : ℝ) := by exact_mod_cast hnNat
    have hv : (n : ℝ) * fp.u < 1 := hvalid
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
  have hg : 0 ≤ p39Gamma fp.u n :=
    p39_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hc : 0 ≤ p39Gamma fp.u n +
      (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n) := by
    have hu2 : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact add_nonneg hg (mul_nonneg hu2 (by linarith))
  have hfrac : 0 ≤ fp.u / (1 - fp.u) :=
    div_nonneg fp.u_nonneg (by linarith)
  have hcoef : 0 ≤ p39Method2SourceUniformCoefficient fp n := by
    unfold p39Method2SourceUniformCoefficient
    linarith
  have hrule (r c : Fin n) :
      X r c = p39Method2SourceStep fp n L X c r c := by
    exact p39_steps_rule fp n L n (le_refl n) 0 r c c.isLt
  have hXzero (r c : Fin n) (h : r.val < c.val) : X r c = 0 := by
    have hr := hrule r c
    have hne : r ≠ c := by
      intro he
      have := congrArg Fin.val he
      omega
    have hnot : ¬ c < r := by
      intro hcr
      exact (Nat.lt_asymm h hcr)
    simpa [p39Method2SourceStep, hne, hnot] using hr
  have hXdiag (c : Fin n) : X c c = fp.fl_div 1 (L c c) := by
    simpa [p39Method2SourceStep] using hrule c c
  have hXbelow (r c : Fin n) (h : c.val < r.val) :
      X r c = fp.fl_mul (-fp.fl_div 1 (L c c))
        (p39RoundedDotProduct fp (n - c.val - 1)
          (fun t => X r ⟨c.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨c.val + 1 + t.val, by omega⟩ c)) := by
    have hne : r ≠ c := by
      intro he
      have := congrArg Fin.val he
      omega
    have hlt : c < r := h
    simpa [p39Method2SourceStep, hne, hlt] using hrule r c
  let m := n - j.val - 1
  let q : Fin m → Fin n := fun t => ⟨j.val + 1 + t.val, by omega⟩
  let s := ∑ t : Fin m, X i (q t) * L (q t) j
  let A := ∑ t : Fin m, |X i (q t)| * |L (q t) j|
  have hq (t : Fin m) : (p39_tailEquiv n j t).val = q t := rfl
  have hsum : p39MatMul X L i j = X i j * L j j + s := by
    unfold p39MatMul
    have hh := p39_sum_tail n j (fun k => X i k * L k j)
      (by intro k hk; change X i k * L k j = 0; rw [hL k j hk]; ring)
    simpa only [hq] using hh
  have habs : (∑ k : Fin n, |X i k| * |L k j|) =
      |X i j| * |L j j| + A := by
    have hh := p39_sum_tail n j (fun k => |X i k| * |L k j|)
      (by intro k hk; change |X i k| * |L k j| = 0; rw [hL k j hk]; simp)
    simpa only [hq] using hh
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hs : |s| ≤ A := by
    dsimp [s, A]
    calc
      |∑ t : Fin m, X i (q t) * L (q t) j| ≤
        ∑ t : Fin m, |X i (q t) * L (q t) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t : Fin m, |X i (q t)| * |L (q t) j| := by
        simp_rw [abs_mul]
  rcases lt_trichotomy i.val j.val with hij | heq | hji
  · have hzero : p39MatMul X L i j = 0 := by
      unfold p39MatMul
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hkj : k.val < j.val
      · rw [hL k j hkj]; ring
      · have hik : i.val < k.val := by omega
        rw [hXzero i k hik]; ring
    have hne : i ≠ j := by
      intro he
      have := congrArg Fin.val he
      omega
    rw [hzero, if_neg hne]
    simp only [sub_zero, abs_zero]
    exact mul_nonneg hcoef (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hij : i = j := Fin.ext heq
    subst i
    have htail0 : s = 0 := by
      dsimp [s]
      apply Finset.sum_eq_zero
      intro t ht
      have hjq : j.val < (q t).val := by
        change j.val < j.val + 1 + t.val
        omega
      rw [hXzero j (q t) hjq]
      ring
    have hdiagbound := p39_reciprocal_residual fp (L j j) (hdiag j) hu
    rw [hsum, htail0, add_zero, hXdiag, if_pos rfl, habs]
    have hterm : 0 ≤ |X j j| * |L j j| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hcoef' : fp.u / (1 - fp.u) ≤
        p39Method2SourceUniformCoefficient fp n := by
      unfold p39Method2SourceUniformCoefficient
      linarith
    calc
      |fp.fl_div 1 (L j j) * L j j - 1| ≤
          (fp.u / (1 - fp.u)) * (|fp.fl_div 1 (L j j)| * |L j j|) :=
            hdiagbound
      _ ≤ p39Method2SourceUniformCoefficient fp n *
          (|X j j| * |L j j|) := by
            rw [hXdiag]
            exact mul_le_mul_of_nonneg_right hcoef'
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ p39Method2SourceUniformCoefficient fp n *
          (|X j j| * |L j j| + A) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hcoef
  · have hne : i ≠ j := by
      intro he
      have := congrArg Fin.val he
      omega
    let p := p39RoundedDotProduct fp m
      (fun t => X i (q t)) (fun t => L (q t) j)
    have hpe : |p - s| ≤ p39Gamma fp.u n * A := by
      have hm : m ≤ n := by dsimp [m]; omega
      exact p39_dot_gamma_bound fp n m hvalid hm _ _
    have hbelow : X i j = fp.fl_mul (-fp.fl_div 1 (L j j)) p := by
      simpa [p, q, m] using hXbelow i j hji
    have hmain := p39_offdiag_scalar fp n (L j j) p s A (hdiag j) hA hpe hs
    rw [hsum, hbelow, if_neg hne, sub_zero, habs]
    have hterm : 0 ≤ |X i j| * |L j j| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hcoef' : p39Gamma fp.u n +
        (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n) ≤
        p39Method2SourceUniformCoefficient fp n := by
      unfold p39Method2SourceUniformCoefficient
      linarith
    calc
      |fp.fl_mul (-fp.fl_div 1 (L j j)) p * L j j + s| ≤
          (p39Gamma fp.u n +
            (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n)) * A := hmain
      _ ≤ p39Method2SourceUniformCoefficient fp n * A :=
        mul_le_mul_of_nonneg_right hcoef' hA
      _ ≤ p39Method2SourceUniformCoefficient fp n *
          (|X i j| * |L j j| + A) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef

end VSCLReuse

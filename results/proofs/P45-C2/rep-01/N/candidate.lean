import VSCLReuse.P45.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p45_gamma_ge_u (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P45GammaValid u (n + 1)) : u ≤ p45Gamma u (n + 1) := by
  unfold p45Gamma P45GammaValid at *
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hd : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  rw [le_div_iff₀ hd]
  push_cast
  nlinarith [mul_nonneg hn hu, sq_nonneg u]

private lemma p45_gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P45GammaValid u (n + 2)) :
    (1 + u) * p45Gamma u (n + 1) + u ≤ p45Gamma u (n + 2) := by
  unfold P45GammaValid at hv
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hd1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by
    push_cast at *
    nlinarith
  have hd2 : 0 < 1 - ((n + 2 : ℕ) : ℝ) * u := by linarith
  have heq : (1 + u) * p45Gamma u (n + 1) + u =
      ((n + 2 : ℕ) : ℝ) * u / (1 - ((n + 1 : ℕ) : ℝ) * u) := by
    have hid (t : ℝ) (ht : 1 - t ≠ 0) :
        (1 + u) * (t / (1 - t)) + u = (t + u) / (1 - t) := by
      field_simp
      ring
    unfold p45Gamma
    convert hid (((n + 1 : ℕ) : ℝ) * u) (ne_of_gt hd1) using 1
    push_cast
    ring
  rw [heq]
  unfold p45Gamma
  rw [div_le_div_iff₀ hd1 hd2]
  push_cast at *
  nlinarith [mul_nonneg hu hn, sq_nonneg u]

private lemma p45_mul_error (fp : P45FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : x * y * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x * y| * |δ| ≤ |x * y| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = _ := by ring

private lemma p45_add_error (fp : P45FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x + y| * |δ| ≤ (|x| + |y|) * |δ| :=
      mul_le_mul_of_nonneg_right (abs_add_le x y) (abs_nonneg _)
    _ ≤ (|x| + |y|) * fp.u :=
      mul_le_mul_of_nonneg_left hδ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

private lemma p45_dot_step_error (fp : P45FPModel) (A S B p : ℝ)
    (hm : |B - p| ≤ fp.u * |p|) :
    |fp.fl_add A B - (S + p)| ≤
      (1 + fp.u) * |A - S| + fp.u * |S| +
        (2 * fp.u + fp.u ^ 2) * |p| := by
  have ha : |fp.fl_add A B - (A + B)| ≤ fp.u * (|A| + |B|) :=
    p45_add_error fp A B
  have hA : |A| ≤ |A - S| + |S| := by
    conv_lhs => rw [show A = (A - S) + S by ring]
    exact abs_add_le _ _
  have hB : |B| ≤ |B - p| + |p| := by
    conv_lhs => rw [show B = (B - p) + p by ring]
    exact abs_add_le _ _
  have ht : |fp.fl_add A B - (S + p)| ≤
      |fp.fl_add A B - (A + B)| + |A - S| + |B - p| := by
    calc
      _ ≤ |fp.fl_add A B - (A + B)| + |(A + B) - (S + p)| := by
        convert abs_add_le (fp.fl_add A B - (A + B)) ((A + B) - (S + p))
          using 1 <;> ring
      _ ≤ _ := by
        have ht' : |(A + B) - (S + p)| ≤ |A - S| + |B - p| := by
          convert abs_add_le (A - S) (B - p) using 1 <;> ring
        linarith
  have hAu := mul_le_mul_of_nonneg_left hA fp.u_nonneg
  have hBu := mul_le_mul_of_nonneg_left hB fp.u_nonneg
  have hmu := mul_le_mul_of_nonneg_left hm fp.u_nonneg
  nlinarith [mul_nonneg fp.u_nonneg (abs_nonneg p)]

private lemma p45_fold_dot_error (fp : P45FPModel) :
    ∀ (n : ℕ) (v r : Fin (n + 1) → ℝ),
      (∀ j, |r j - v j| ≤ fp.u * |v j|) →
      P45GammaValid fp.u (n + 1) →
      |Fin.foldl n (fun acc i => fp.fl_add acc (r i.succ)) (r 0) -
          ∑ j : Fin (n + 1), v j| ≤
        p45Gamma fp.u (n + 1) * ∑ j : Fin (n + 1), |v j| := by
  intro n
  induction n with
  | zero =>
      intro v r hr hv
      simpa using (hr 0).trans
        (mul_le_mul_of_nonneg_right (p45_gamma_ge_u fp.u 0 fp.u_nonneg hv)
          (abs_nonneg _))
  | succ n ih =>
      intro v r hr hv
      let v' : Fin (n + 1) → ℝ := fun j => v j.castSucc
      let r' : Fin (n + 1) → ℝ := fun j => r j.castSucc
      let A : ℝ := Fin.foldl n (fun acc i => fp.fl_add acc (r' i.succ)) (r' 0)
      let S : ℝ := ∑ j : Fin (n + 1), v' j
      let T : ℝ := ∑ j : Fin (n + 1), |v' j|
      let B : ℝ := r (Fin.last (n + 1))
      let p : ℝ := v (Fin.last (n + 1))
      have hv' : P45GammaValid fp.u (n + 1) := by
        unfold P45GammaValid at *
        push_cast at *
        nlinarith [fp.u_nonneg]
      have hi : |A - S| ≤ p45Gamma fp.u (n + 1) * T := by
        exact ih v' r' (fun j => hr j.castSucc) hv'
      have hm : |B - p| ≤ fp.u * |p| := hr _
      have hfold :
          Fin.foldl (n + 1) (fun acc i => fp.fl_add acc (r i.succ)) (r 0) =
            fp.fl_add A B := by
        rw [Fin.foldl_succ_last]
        rfl
      have hsum : (∑ j : Fin (n + 2), v j) = S + p := by
        simp [S, p, v', Fin.sum_univ_castSucc]
      have habsum : (∑ j : Fin (n + 2), |v j|) = T + |p| := by
        simp [T, p, v', Fin.sum_univ_castSucc]
      have hS : |S| ≤ T := by
        simpa [S, T] using Finset.abs_sum_le_sum_abs v' Finset.univ
      have hT : 0 ≤ T := by
        dsimp [T]
        positivity
      have hge : fp.u ≤ p45Gamma fp.u (n + 1) :=
        p45_gamma_ge_u fp.u n fp.u_nonneg hv'
      have hstep : (1 + fp.u) * p45Gamma fp.u (n + 1) + fp.u ≤
          p45Gamma fp.u (n + 2) := p45_gamma_step fp.u n fp.u_nonneg hv
      have hc : 2 * fp.u + fp.u ^ 2 ≤
          (1 + fp.u) * p45Gamma fp.u (n + 1) + fp.u := by
        nlinarith [mul_nonneg (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
          (sub_nonneg.mpr hge)]
      have hmain := p45_dot_step_error fp A S B p hm
      rw [hfold, hsum, habsum]
      have h1 := mul_le_mul_of_nonneg_left hi
        (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
      have h2 := mul_le_mul_of_nonneg_left hS fp.u_nonneg
      have h3 := mul_le_mul_of_nonneg_right hc (abs_nonneg p)
      have h4 := mul_le_mul_of_nonneg_right hstep (add_nonneg hT (abs_nonneg p))
      nlinarith

/-- One already represented bucket of Algorithm 3.1: classical gamma form of (3.1). -/
theorem p45_c2_one_bucket_dot_error (fp : P45FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P45GammaValid fp.u n) :
    |p45BlockDot fp n a x - ∑ j : Fin n, a j * x j| ≤
      p45Gamma fp.u n * ∑ j : Fin n, |a j * x j| := by
  -- PROOF_START P45-C2-H001
  cases n with
  | zero => simp [p45BlockDot]
  | succ m =>
      let v : Fin (m + 1) → ℝ := fun j => a j * x j
      let r : Fin (m + 1) → ℝ := fun j => fp.fl_mul (a j) (x j)
      have h := p45_fold_dot_error fp m v r
        (fun j => p45_mul_error fp (a j) (x j)) hv
      simpa [p45BlockDot, v, r] using h

end VSCLReuse

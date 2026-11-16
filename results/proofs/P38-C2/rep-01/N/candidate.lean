import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators


private theorem p38_pow_mul_sub_le_one (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
    have hcoeff :
        (1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤
          1 - (n : ℝ) * u := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) (sq_nonneg u)]
    calc
      (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
          (1 + u) ^ n * ((1 + u) * (1 - ((n + 1 : ℕ) : ℝ) * u)) := by
            rw [pow_succ]; ring
      _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) :=
        mul_le_mul_of_nonneg_left hcoeff hpow
      _ ≤ 1 := ih

private theorem p38_pow_error_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hvalid : P38GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p38Gamma u n := by
  have hden : 0 < 1 - (n : ℝ) * u := by
    unfold P38GammaValid at hvalid
    linarith
  unfold p38Gamma
  apply (le_div_iff₀ hden).2
  calc
    ((1 + u) ^ n - 1) * (1 - (n : ℝ) * u) =
        (1 + u) ^ n * (1 - (n : ℝ) * u) - 1 + (n : ℝ) * u := by ring
    _ ≤ 1 - 1 + (n : ℝ) * u :=
      add_le_add (sub_le_sub_right (p38_pow_mul_sub_le_one u hu n) 1) le_rfl
    _ = (n : ℝ) * u := by ring

private theorem p38_round_step (fp : P38FPModel) (k : ℕ)
    (acc exact mass x y : ℝ) (hk : 1 ≤ k)
    (hmass : 0 ≤ mass) (hexact : |exact| ≤ mass)
    (herr : |acc - exact| ≤ ((1 + fp.u) ^ k - 1) * mass) :
    |fp.fl_add acc (fp.fl_mul x y) - (exact + x * y)| ≤
      ((1 + fp.u) ^ (k + 1) - 1) * (mass + |x| * |y|) := by
  let u := fp.u
  let P := (1 + u) ^ k
  let T := |x| * |y|
  have hu : 0 ≤ u := fp.u_nonneg
  have hT : 0 ≤ T := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hP : 0 ≤ P := pow_nonneg (by dsimp [u]; linarith) _
  have hacc : |acc| ≤ P * mass := by
    calc
      |acc| = |(acc - exact) + exact| := by ring
      _ ≤ |acc - exact| + |exact| := abs_add_le _ _
      _ ≤ (P - 1) * mass + mass := add_le_add herr hexact
      _ = P * mass := by ring
  rcases fp.model_mul x y with ⟨δm, hδm, hm⟩
  rcases fp.model_add acc (fp.fl_mul x y) with ⟨δa, hδa, ha⟩
  have hmerr : |fp.fl_mul x y - x * y| ≤ u * T := by
    rw [hm]
    have heq : (x * y) * (1 + δm) - x * y = (x * y) * δm := by ring
    rw [heq, abs_mul, abs_mul]
    calc
      |x| * |y| * |δm| ≤ (|x| * |y|) * u :=
        mul_le_mul_of_nonneg_left hδm hT
      _ = u * T := by ring
  have hmabs : |fp.fl_mul x y| ≤ (1 + u) * T := by
    calc
      |fp.fl_mul x y| = |(fp.fl_mul x y - x * y) + x * y| := by ring
      _ ≤ |fp.fl_mul x y - x * y| + |x * y| := abs_add_le _ _
      _ ≤ u * T + T := by rw [abs_mul]; exact add_le_add hmerr le_rfl
      _ = (1 + u) * T := by ring
  have hsumabs : |acc + fp.fl_mul x y| ≤ P * mass + (1 + u) * T := by
    calc
      _ ≤ |acc| + |fp.fl_mul x y| := abs_add_le _ _
      _ ≤ P * mass + (1 + u) * T := add_le_add hacc hmabs
  have hδprod : |acc + fp.fl_mul x y| * |δa| ≤
      (P * mass + (1 + u) * T) * u := by
    calc
      _ ≤ (P * mass + (1 + u) * T) * |δa| :=
        mul_le_mul_of_nonneg_right hsumabs (abs_nonneg _)
      _ ≤ (P * mass + (1 + u) * T) * u :=
        mul_le_mul_of_nonneg_left hδa (by positivity)
  have hmain :
      |fp.fl_add acc (fp.fl_mul x y) - (exact + x * y)| ≤
        (P - 1) * mass + u * T + (P * mass + (1 + u) * T) * u := by
    calc
      _ = |(acc - exact) + (fp.fl_mul x y - x * y) +
            (acc + fp.fl_mul x y) * δa| := by rw [ha]; congr 1; ring
      _ ≤ |acc - exact| + |fp.fl_mul x y - x * y| +
            |acc + fp.fl_mul x y| * |δa| := by
              calc
                _ ≤ |(acc - exact) + (fp.fl_mul x y - x * y)| +
                      |(acc + fp.fl_mul x y) * δa| := abs_add_le _ _
                _ ≤ (|acc - exact| + |fp.fl_mul x y - x * y|) +
                      |acc + fp.fl_mul x y| * |δa| := by
                    rw [abs_mul]
                    exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by linarith
  have hcoeff : 2 * u + u ^ 2 ≤ (1 + u) ^ (k + 1) - 1 := by
    calc
      2 * u + u ^ 2 = (1 + u) ^ 2 - 1 := by ring
      _ ≤ (1 + u) ^ (k + 1) - 1 :=
        sub_le_sub_right (pow_le_pow_right₀ (by dsimp [u]; linarith) (by omega : 2 ≤ k + 1)) 1
  calc
    _ ≤ (P - 1) * mass + u * T + (P * mass + (1 + u) * T) * u := hmain
    _ = ((1 + u) ^ (k + 1) - 1) * mass + (2 * u + u ^ 2) * T := by
      dsimp [P]; rw [pow_succ]; ring
    _ ≤ ((1 + u) ^ (k + 1) - 1) * mass +
          ((1 + u) ^ (k + 1) - 1) * T :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoeff hT)
    _ = ((1 + u) ^ (k + 1) - 1) * (mass + T) := by ring

private theorem p38_roundedDot_succ_succ (fp : P38FPModel) (n : ℕ)
    (x y : Fin (n + 2) → ℝ) :
    p38RoundedDotProduct fp (n + 2) x y =
      fp.fl_add
        (p38RoundedDotProduct fp (n + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))) := by
  change Fin.foldl (n + 1)
    (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
    (fp.fl_mul (x 0) (y 0)) = _
  rw [Fin.foldl_succ_last]
  rfl

private theorem p38_roundedDot_error_bound (fp : P38FPModel) :
    ∀ n : ℕ, ∀ x y : Fin n → ℝ,
      |p38RoundedDotProduct fp n x y - ∑ t : Fin n, x t * y t| ≤
        ((1 + fp.u) ^ n - 1) * ∑ t : Fin n, |x t| * |y t| := by
  intro n
  induction n with
  | zero =>
      intro x y
      simp [p38RoundedDotProduct]
  | succ n ih =>
      intro x y
      cases n with
      | zero =>
          simp only [p38RoundedDotProduct, Fin.foldl_zero]
          change |fp.fl_mul (x 0) (y 0) - ∑ t : Fin 1, x t * y t| ≤
            ((1 + fp.u) ^ 1 - 1) * ∑ t : Fin 1, |x t| * |y t|
          simp only [Fin.sum_univ_one, pow_one]
          rcases fp.model_mul (x 0) (y 0) with ⟨δ, hδ, hmul⟩
          rw [hmul]
          have heq : (x 0 * y 0) * (1 + δ) - x 0 * y 0 = (x 0 * y 0) * δ := by ring
          rw [heq, abs_mul, abs_mul]
          have hxy : 0 ≤ |x 0| * |y 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          calc
            |x 0| * |y 0| * |δ| ≤ (|x 0| * |y 0|) * fp.u :=
              mul_le_mul_of_nonneg_left hδ hxy
            _ = ((1 + fp.u) - 1) * (|x 0| * |y 0|) := by ring
      | succ n =>
          let x' : Fin (n + 1) → ℝ := fun i => x i.castSucc
          let y' : Fin (n + 1) → ℝ := fun i => y i.castSucc
          have hmass : 0 ≤ ∑ t : Fin (n + 1), |x' t| * |y' t| :=
            Finset.sum_nonneg (by intro t ht; positivity)
          have hexact :
              |∑ t : Fin (n + 1), x' t * y' t| ≤
                ∑ t : Fin (n + 1), |x' t| * |y' t| := by
            calc
              _ ≤ ∑ t : Fin (n + 1), |x' t * y' t| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = _ := by simp_rw [abs_mul]
          have hstep := p38_round_step fp (n + 1)
            (p38RoundedDotProduct fp (n + 1) x' y')
            (∑ t : Fin (n + 1), x' t * y' t)
            (∑ t : Fin (n + 1), |x' t| * |y' t|)
            (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
            (by omega) hmass hexact (ih x' y')
          simpa only [p38_roundedDot_succ_succ, Fin.sum_univ_castSucc,
            x', y'] using hstep

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
  have hcoeff := p38_pow_error_le_gamma fp.u fp.u_nonneg n hvalid
  have hentry (k : Fin m) :
      |p38RoundedMatMul fp A B k j - p38MatMul A B k j| ≤
        p38Gamma fp.u n * ∑ t : Fin n, |A k t| * |B t j| := by
    have hdot := p38_roundedDot_error_bound fp n (A k) (fun t => B t j)
    have hmass : 0 ≤ ∑ t : Fin n, |A k t| * |B t j| :=
      Finset.sum_nonneg (by intro t ht; positivity)
    calc
      _ ≤ ((1 + fp.u) ^ n - 1) *
          ∑ t : Fin n, |A k t| * |B t j| := by
            simpa only [p38RoundedMatMul, p38MatMul] using hdot
      _ ≤ p38Gamma fp.u n * ∑ t : Fin n, |A k t| * |B t j| :=
        mul_le_mul_of_nonneg_right hcoeff hmass
  calc
    |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| ≤
      ∑ k : Fin m, |L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, |L i k| *
        |p38RoundedMatMul fp A B k j - p38MatMul A B k j| := by
          simp_rw [abs_mul]
    _ ≤ ∑ k : Fin m, |L i k| *
        (p38Gamma fp.u n * ∑ t : Fin n, |A k t| * |B t j|) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hentry k) (abs_nonneg _)
    _ = p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
            rw [Finset.mul_sum]
            congr 1
            ext k
            ring

end VSCLReuse

import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p38_gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P38GammaValid u n) : 0 ≤ p38Gamma u n := by
  unfold p38Gamma P38GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p38_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hv : P38GammaValid u (k + 1)) :
    (1 + u) * p38Gamma u k + u ≤ p38Gamma u (k + 1) := by
  have hk : 0 < 1 - (k : ℝ) * u := by
    unfold P38GammaValid at hv
    push_cast at hv
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hu]
  have hk' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold P38GammaValid at hv
    linarith
  unfold p38Gamma
  have heq : (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
      (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
    push_cast
    have hden : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hk]
    field_simp [hden]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hk hk').2
  push_cast
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) hu,
    sq_nonneg u]

private lemma p38_gamma_valid_mono (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hv : P38GammaValid u b) : P38GammaValid u a := by
  unfold P38GammaValid at *
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu) hv

private lemma p38_gamma_step_two (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hv : P38GammaValid u (k + 1)) :
    2 * u + u ^ 2 ≤ p38Gamma u (k + 1) := by
  cases k with
  | zero => omega
  | succ q =>
  have hq : P38GammaValid u (q + 1) :=
    p38_gamma_valid_mono u hu (a := q + 1) (b := q + 1 + 1)
      (by omega) (by simpa [Nat.succ_eq_add_one] using hv)
  have hq0 : P38GammaValid u q :=
    p38_gamma_valid_mono u hu (a := q) (b := q + 1) (by omega) hq
  have hgq : 0 ≤ p38Gamma u q := p38_gamma_nonneg u q hu hq0
  have hs1 := p38_gamma_step u q hu hq
  have hs2 := p38_gamma_step u (q + 1) hu (by simpa [Nat.succ_eq_add_one] using hv)
  have hu1 : 0 ≤ 1 + u := by linarith
  have hm : (1 + u) * u ≤ (1 + u) * p38Gamma u (q + 1) :=
    mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hu hgq]) hu1
  simpa [Nat.succ_eq_add_one] using (show
    2 * u + u ^ 2 ≤ p38Gamma u (q + 1 + 1) by nlinarith)

private lemma p38_gamma_step_mass (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hv : P38GammaValid u (k + 1))
    (mass term : ℝ) (hmass : 0 ≤ mass) (hterm : 0 ≤ term) :
    ((1 + u) * p38Gamma u k + u) * mass +
      (2 * u + u ^ 2) * term ≤
      p38Gamma u (k + 1) * (mass + term) := by
  have hs := p38_gamma_step u k hu hv
  have ht := p38_gamma_step_two u k hu hk hv
  have hsm := mul_le_mul_of_nonneg_right hs hmass
  have htt := mul_le_mul_of_nonneg_right ht hterm
  nlinarith

private lemma p38_mul_error (fp : P38FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * (|x| * |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul, abs_mul]
  have h := mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg x) (abs_nonneg y))
  nlinarith

private lemma p38_add_error (fp : P38FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  have h1 := mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))
  have h2 := mul_le_mul_of_nonneg_right (abs_add_le x y) fp.u_nonneg
  nlinarith

private lemma p38_add_mul_step (fp : P38FPModel)
    (acc exact x y : ℝ) :
    |fp.fl_add acc (fp.fl_mul x y) - (exact + x * y)| ≤
      (1 + fp.u) * |acc - exact| + fp.u * |exact| +
        (2 * fp.u + fp.u ^ 2) * (|x| * |y|) := by
  let prod := fp.fl_mul x y
  let term := x * y
  let mass := |x| * |y|
  have hmul : |prod - term| ≤ fp.u * mass := by
    simpa [prod, term, mass] using p38_mul_error fp x y
  have hadd : |fp.fl_add acc prod - (acc + prod)| ≤
      fp.u * (|acc| + |prod|) := p38_add_error fp acc prod
  have hacc : |acc| ≤ |exact| + |acc - exact| := by
    have := abs_add_le (acc - exact) exact
    have heq : (acc - exact) + exact = acc := by ring
    rw [heq] at this
    linarith
  have hprod : |prod| ≤ mass + |prod - term| := by
    have := abs_add_le (prod - term) term
    simpa [term, mass, abs_mul, add_comm] using this
  have ht : |fp.fl_add acc prod - (exact + term)| ≤
      |fp.fl_add acc prod - (acc + prod)| +
        |acc - exact| + |prod - term| := by
    have ha := abs_add_le
      (fp.fl_add acc prod - (acc + prod))
      ((acc - exact) + (prod - term))
    have hb := abs_add_le (acc - exact) (prod - term)
    have heq : fp.fl_add acc prod - (exact + term) =
      (fp.fl_add acc prod - (acc + prod)) + ((acc - exact) + (prod - term)) := by ring
    rw [heq]
    linarith
  have hmass : 0 ≤ mass := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hacc fp.u_nonneg
  have h2 := mul_le_mul_of_nonneg_left hprod fp.u_nonneg
  have h3 := mul_le_mul_of_nonneg_left hmul fp.u_nonneg
  dsimp [prod, term, mass] at *
  nlinarith

private lemma p38_fold_bound (fp : P38FPModel) :
    ∀ (n k : ℕ) (x y : Fin n → ℝ) (acc exact mass : ℝ),
      1 ≤ k → P38GammaValid fp.u (k + n) →
      |acc - exact| ≤ p38Gamma fp.u k * mass →
      |exact| ≤ mass → 0 ≤ mass →
      |Fin.foldl n (fun s i => fp.fl_add s (fp.fl_mul (x i) (y i))) acc -
        (exact + ∑ i : Fin n, x i * y i)| ≤
        p38Gamma fp.u (k + n) *
          (mass + ∑ i : Fin n, |x i| * |y i|) := by
  intro n
  induction n with
  | zero =>
      intro k x y acc exact mass hk hv herr hex hmass
      simpa using herr
  | succ n ih =>
      intro k x y acc exact mass hk hv herr hex hmass
      let term := x 0 * y 0
      let a := |x 0| * |y 0|
      let acc' := fp.fl_add acc (fp.fl_mul (x 0) (y 0))
      have ha : 0 ≤ a := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hvstep : P38GammaValid fp.u (k + 1) :=
        p38_gamma_valid_mono fp.u fp.u_nonneg (a := k + 1) (b := k + (n + 1))
          (by omega) hv
      have hstep := p38_add_mul_step fp acc exact (x 0) (y 0)
      have hbound : |acc' - (exact + term)| ≤
          p38Gamma fp.u (k + 1) * (mass + a) := by
        calc
          _ ≤ (1 + fp.u) * |acc - exact| + fp.u * |exact| +
              (2 * fp.u + fp.u ^ 2) * a := by simpa [acc', term, a] using hstep
          _ ≤ ((1 + fp.u) * p38Gamma fp.u k + fp.u) * mass +
              (2 * fp.u + fp.u ^ 2) * a := by
                have h1 := mul_le_mul_of_nonneg_left herr (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
                have h2 := mul_le_mul_of_nonneg_left hex fp.u_nonneg
                nlinarith
          _ ≤ _ := p38_gamma_step_mass fp.u k fp.u_nonneg hk hvstep mass a hmass ha
      have hex' : |exact + term| ≤ mass + a := by
        calc
          _ ≤ |exact| + |term| := abs_add_le _ _
          _ ≤ mass + a := by simpa [term, a, abs_mul] using add_le_add_right hex a
      have hrec := ih (k + 1) (fun i => x i.succ) (fun i => y i.succ)
        acc' (exact + term) (mass + a) (by omega)
        (by convert hv using 1; omega)
        hbound hex' (add_nonneg hmass ha)
      have hkn : (k + 1) + n = k + (n + 1) := by omega
      rw [hkn] at hrec
      simpa [Fin.foldl_succ, Fin.sum_univ_succ, acc', term, a,
        add_assoc] using hrec

private lemma p38_rounded_dot_error (fp : P38FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hv : P38GammaValid fp.u n) :
    |p38RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p38Gamma fp.u n * ∑ i : Fin n, |x i| * |y i| := by
  cases n with
  | zero => simp [p38RoundedDotProduct]
  | succ q =>
      let term := x 0 * y 0
      let mass := |x 0| * |y 0|
      let seed := fp.fl_mul (x 0) (y 0)
      have hv1 : P38GammaValid fp.u 1 :=
        p38_gamma_valid_mono fp.u fp.u_nonneg (a := 1) (b := q + 1)
          (by omega) (by simpa [Nat.succ_eq_add_one] using hv)
      have hgamma : fp.u ≤ p38Gamma fp.u 1 := by
        have hs := p38_gamma_step fp.u 0 fp.u_nonneg hv1
        simpa [p38Gamma] using hs
      have hseed : |seed - term| ≤ p38Gamma fp.u 1 * mass := by
        have hm := p38_mul_error fp (x 0) (y 0)
        have hmul := mul_le_mul_of_nonneg_right hgamma
          (mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (y 0)))
        simpa [seed, term, mass] using (le_trans hm hmul)
      have hrec := p38_fold_bound fp q 1 (fun i => x i.succ) (fun i => y i.succ)
        seed term mass (by omega)
        (by convert hv using 1; omega)
        hseed (by simp [term, mass, abs_mul])
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      simpa [p38RoundedDotProduct, Fin.sum_univ_succ, seed, term, mass,
        Nat.add_comm 1 q] using hrec

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
      p38_rounded_dot_error fp n (A k) (fun t => B t j) hvalid
  calc
    |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)|
        ≤ ∑ k : Fin m, |L i k *
            (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, |L i k| *
          |p38RoundedMatMul fp A B k j - p38MatMul A B k j| := by
          simp_rw [abs_mul]
    _ ≤ ∑ k : Fin m, |L i k| *
          (p38Gamma fp.u n * ∑ t : Fin n, |A k t| * |B t j|) := by
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

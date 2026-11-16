import VSCLReuse.P43.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p43_pow_linear (u : ℝ) (hu : 0 ≤ u) (n : ℕ) :
    (1 + u) ^ n * (1 - (n : ℝ) * u) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
      have hd : 0 ≤ ((n + 1 : ℕ) : ℝ) * u ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg u)
      calc
        (1 + u) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ n * (1 - (n : ℝ) * u) -
              (1 + u) ^ n * (((n + 1 : ℕ) : ℝ) * u ^ 2) := by
                push_cast
                ring
        _ ≤ (1 + u) ^ n * (1 - (n : ℝ) * u) :=
          sub_le_self _ (mul_nonneg hp hd)
        _ ≤ 1 := ih

private theorem p43_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hn : P43GammaValid u n) :
    (1 + u) ^ n - 1 ≤ p43Gamma u n := by
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hp := p43_pow_linear u hu n
  unfold p43Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private theorem p43_pow_mono (u : ℝ) (hu : 0 ≤ u) {m n : ℕ} (hmn : m ≤ n) :
    (1 + u) ^ m ≤ (1 + u) ^ n := by
  exact pow_le_pow_right₀ (by linarith : 1 ≤ 1 + u) hmn

private theorem p43_round_add_bound (fp : P43FPModel) (j : ℕ)
    (x y a c A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a| ≤ A) (hc : |c| ≤ B)
    (hx : |x - a| ≤ ((1 + fp.u) ^ j - 1) * A)
    (hy : |y - c| ≤ ((1 + fp.u) ^ j - 1) * B) :
    |fp.fl_add x y - (a + c)| ≤
      ((1 + fp.u) ^ (j + 1) - 1) * (A + B) := by
  let q : ℝ := (1 + fp.u) ^ j
  have hq : 0 ≤ q := pow_nonneg (by linarith [fp.u_nonneg]) _
  have hxx : |x| ≤ q * A := by
    calc
      |x| = |(x - a) + a| := by ring
      _ ≤ |x - a| + |a| := abs_add_le _ _
      _ ≤ (q - 1) * A + A := add_le_add hx ha
      _ = q * A := by ring
  have hyy : |y| ≤ q * B := by
    calc
      |y| = |(y - c) + c| := by ring
      _ ≤ |y - c| + |c| := abs_add_le _ _
      _ ≤ (q - 1) * B + B := add_le_add hy hc
      _ = q * B := by ring
  have hsum : |x + y| ≤ q * (A + B) := by
    calc
      |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ q * A + q * B := add_le_add hxx hyy
      _ = q * (A + B) := by ring
  have he : |(x + y) - (a + c)| ≤ (q - 1) * (A + B) := by
    calc
      |(x + y) - (a + c)| = |(x - a) + (y - c)| := by ring
      _ ≤ |x - a| + |y - c| := abs_add_le _ _
      _ ≤ (q - 1) * A + (q - 1) * B := add_le_add hx hy
      _ = (q - 1) * (A + B) := by ring
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  have hmul : |(x + y) * δ| ≤ q * (A + B) * fp.u := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hsum (abs_nonneg δ)).trans
      (mul_le_mul_of_nonneg_left hδ (mul_nonneg hq (add_nonneg hA hB)))
  calc
    |fp.fl_add x y - (a + c)| = |((x + y) - (a + c)) + (x + y) * δ| := by
      rw [hfl]
      congr 1
      ring
    _ ≤ |(x + y) - (a + c)| + |(x + y) * δ| := abs_add_le _ _
    _ ≤ (q - 1) * (A + B) + q * (A + B) * fp.u := add_le_add he hmul
    _ = ((1 + fp.u) ^ (j + 1) - 1) * (A + B) := by
      dsimp [q]
      rw [pow_succ]
      ring

private theorem p43_fold_bound (fp : P43FPModel) (k : ℕ) :
    ∀ (n : ℕ) (v e m : Fin n → ℝ) (x a A : ℝ),
      0 ≤ A → |a| ≤ A →
      |x - a| ≤ ((1 + fp.u) ^ k - 1) * A →
      (∀ i, 0 ≤ m i) → (∀ i, |e i| ≤ m i) →
      (∀ i, |v i - e i| ≤ ((1 + fp.u) ^ k - 1) * m i) →
      |Fin.foldl n (fun acc i => fp.fl_add acc (v i)) x -
          (a + ∑ i : Fin n, e i)| ≤
        ((1 + fp.u) ^ (k + n) - 1) * (A + ∑ i : Fin n, m i) := by
  intro n
  induction n with
  | zero =>
      intro v e m x a A hA ha hx hm he hv
      simpa using hx
  | succ n ih =>
      intro v e m x a A hA ha hx hm he hv
      have hrec := ih (fun i : Fin n => v i.castSucc)
        (fun i : Fin n => e i.castSucc) (fun i : Fin n => m i.castSucc)
        x a A hA ha hx (fun i => hm i.castSucc)
        (fun i => he i.castSucc) (fun i => hv i.castSucc)
      have hsumMass : 0 ≤ ∑ i : Fin n, m i.castSucc :=
        Finset.sum_nonneg (fun i hi => hm i.castSucc)
      have hsumAbs : |∑ i : Fin n, e i.castSucc| ≤
          ∑ i : Fin n, m i.castSucc := by
        calc
          |∑ i : Fin n, e i.castSucc| ≤ ∑ i : Fin n, |e i.castSucc| := by
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin n, m i.castSucc :=
            Finset.sum_le_sum (fun i hi => he i.castSucc)
      have hpartialAbs : |a + ∑ i : Fin n, e i.castSucc| ≤
          A + ∑ i : Fin n, m i.castSucc := by
        calc
          |a + ∑ i : Fin n, e i.castSucc| ≤ |a| + |∑ i : Fin n, e i.castSucc| :=
            abs_add_le _ _
          _ ≤ A + ∑ i : Fin n, m i.castSucc := add_le_add ha hsumAbs
      have hlast : |v (Fin.last n) - e (Fin.last n)| ≤
          ((1 + fp.u) ^ (k + n) - 1) * m (Fin.last n) := by
        have hc := p43_pow_mono fp.u fp.u_nonneg (Nat.le_add_right k n)
        exact (hv (Fin.last n)).trans
          (mul_le_mul_of_nonneg_right (sub_le_sub_right hc 1) (hm (Fin.last n)))
      have hround := p43_round_add_bound fp (k + n)
        (Fin.foldl n (fun acc i => fp.fl_add acc (v i.castSucc)) x)
        (v (Fin.last n))
        (a + ∑ i : Fin n, e i.castSucc) (e (Fin.last n))
        (A + ∑ i : Fin n, m i.castSucc) (m (Fin.last n))
        (add_nonneg hA hsumMass) (hm (Fin.last n)) hpartialAbs
        (he (Fin.last n)) hrec hlast
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        Nat.add_assoc, add_assoc] using hround

private theorem p43_recursive_sum_bound (fp : P43FPModel) (k b : ℕ) (hb : 0 < b)
    (v e m : Fin b → ℝ)
    (hm : ∀ i, 0 ≤ m i) (he : ∀ i, |e i| ≤ m i)
    (hv : ∀ i, |v i - e i| ≤ ((1 + fp.u) ^ k - 1) * m i) :
    |p43RecursiveSum fp b v - ∑ i : Fin b, e i| ≤
      ((1 + fp.u) ^ (k + (b - 1)) - 1) * ∑ i : Fin b, m i := by
  cases b with
  | zero => omega
  | succ n =>
      have hfold := p43_fold_bound fp k n
        (fun i : Fin n => v i.succ) (fun i : Fin n => e i.succ)
        (fun i : Fin n => m i.succ)
        (v 0) (e 0) (m 0) (hm 0) (he 0) (hv 0)
        (fun i => hm i.succ) (fun i => he i.succ) (fun i => hv i.succ)
      simpa only [p43RecursiveSum, Fin.foldl_succ, fp.fl_add_zero,
        Fin.sum_univ_succ, Nat.succ_sub_one] using hfold

private theorem p43_tree_exact_le_mass {b t : ℕ} (tree : P43DotTree b t) :
    |tree.exact| ≤ tree.absMass := by
  induction tree with
  | leaf x y => simp [P43DotTree.exact, P43DotTree.absMass]
  | node children ih =>
      change |∑ i : Fin b, (children i).exact| ≤
        ∑ i : Fin b, (children i).absMass
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i hi => ih i))

private theorem p43_tree_pow_bound (fp : P43FPModel) (b : ℕ) (hb : 0 < b) :
    ∀ {t : ℕ} (tree : P43DotTree b t),
      |tree.computed fp - tree.exact| ≤
        ((1 + fp.u) ^ (t * (b - 1) + 1) - 1) * tree.absMass := by
  intro t tree
  induction tree with
  | leaf x y =>
      obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
      change |fp.fl_mul x y - x * y| ≤
        ((1 + fp.u) ^ (0 * (b - 1) + 1) - 1) * |x * y|
      have heq : fp.fl_mul x y - x * y = (x * y) * δ := by
        rw [hfl]
        ring
      rw [heq, abs_mul]
      simpa only [zero_mul, zero_add, pow_one, add_sub_cancel_left, mul_comm] using
        (mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y)))
  | @node t children ih =>
      have hm (i : Fin b) : 0 ≤ (children i).absMass :=
        (abs_nonneg (children i).exact).trans (p43_tree_exact_le_mass (children i))
      have he (i : Fin b) : |(children i).exact| ≤ (children i).absMass :=
        p43_tree_exact_le_mass (children i)
      have hsum := p43_recursive_sum_bound fp (t * (b - 1) + 1) b hb
        (fun i => (children i).computed fp)
        (fun i => (children i).exact)
        (fun i => (children i).absMass) hm he ih
      change |p43RecursiveSum fp b (fun i => (children i).computed fp) -
        ∑ i : Fin b, (children i).exact| ≤
        ((1 + fp.u) ^ ((t + 1) * (b - 1) + 1) - 1) *
          ∑ i : Fin b, (children i).absMass
      have hk : t * (b - 1) + 1 + (b - 1) = (t + 1) * (b - 1) + 1 := by
        simp only [add_mul, one_mul]
        omega
      simpa only [hk] using hsum

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  have hpow := p43_tree_pow_bound fp b hb tree
  have hgamma := p43_pow_le_gamma fp.u fp.u_nonneg
    (t * (b - 1) + 1) hvalid
  have hmass : 0 ≤ tree.absMass :=
    (abs_nonneg tree.exact).trans (p43_tree_exact_le_mass tree)
  exact hpow.trans (mul_le_mul_of_nonneg_right hgamma hmass)

end VSCLReuse

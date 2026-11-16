import VSCLReuse.P43.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p43_add_error (fp : P43FPModel) (a s v : ℝ) :
    |fp.fl_add a v - (s + v)| ≤ |a - s| + fp.u * (|a| + |v|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a v
  rw [hfl]
  have h₁ : (a + v) * (1 + δ) - (s + v) = (a - s) + δ * (a + v) := by ring
  rw [h₁]
  calc
    |(a - s) + δ * (a + v)| ≤ |a - s| + |δ * (a + v)| := abs_add_le _ _
    _ = |a - s| + |δ| * |a + v| := by rw [abs_mul]
    _ ≤ |a - s| + fp.u * (|a| + |v|) := by
      have hmul : |δ| * |a + v| ≤ fp.u * (|a| + |v|) := by
        calc
          |δ| * |a + v| ≤ fp.u * |a + v| :=
            mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
          _ ≤ fp.u * (|a| + |v|) :=
            mul_le_mul_of_nonneg_left (abs_add_le a v) fp.u_nonneg
      linarith

private lemma p43_add_abs (fp : P43FPModel) (a v : ℝ) :
    |fp.fl_add a v| ≤ (1 + fp.u) * (|a| + |v|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a v
  rw [hfl, abs_mul]
  have h₁ : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  calc
    |a + v| * |1 + δ| ≤ (|a| + |v|) * |1 + δ| :=
      mul_le_mul_of_nonneg_right (abs_add_le a v) (abs_nonneg _)
    _ ≤ (|a| + |v|) * (1 + fp.u) :=
      mul_le_mul_of_nonneg_left h₁ (by positivity)
    _ = (1 + fp.u) * (|a| + |v|) := by ring

private lemma p43_fold_bound (fp : P43FPModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ) (a : ℝ),
      let c := Fin.foldl n (fun acc i => fp.fl_add acc (v i)) a
      let s := a + ∑ i, v i
      let m := |a| + ∑ i, |v i|
      |c - s| ≤ ((1 + fp.u)^n - 1) * m ∧
      |c| ≤ (1 + fp.u)^n * m := by
  intro n
  induction n with
  | zero =>
      intro v a
      simp
  | succ n ih =>
      intro v a
      let w : Fin n → ℝ := fun i => v i.castSucc
      let c : ℝ := Fin.foldl n (fun acc i => fp.fl_add acc (w i)) a
      let s : ℝ := a + ∑ i, w i
      let m : ℝ := |a| + ∑ i, |w i|
      have hprev := ih w a
      have he : |c - s| ≤ ((1 + fp.u)^n - 1) * m := hprev.1
      have hc : |c| ≤ (1 + fp.u)^n * m := hprev.2
      have hm : 0 ≤ m := by
        dsimp [m]
        positivity
      have hv : 0 ≤ |v (Fin.last n)| := abs_nonneg _
      have hu : 0 ≤ fp.u := fp.u_nonneg
      have hq : 1 ≤ (1 + fp.u)^n := by
        exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + fp.u)
      have hsum : |s| ≤ m := by
        calc
          |s| ≤ |a| + |∑ i, w i| := by simpa [s] using abs_add_le a (∑ i, w i)
          _ ≤ m := by
            dsimp [m]
            gcongr
            exact Finset.abs_sum_le_sum_abs w Finset.univ
      have hca : |c| ≤ |c - s| + |s| := by
        convert abs_add_le (c - s) s using 1 <;> ring
      have hstep := p43_add_error fp c s (v (Fin.last n))
      have habs := p43_add_abs fp c (v (Fin.last n))
      have hle : |fp.fl_add c (v (Fin.last n)) - (s + v (Fin.last n))| ≤
          ((1 + fp.u)^(n+1) - 1) * (m + |v (Fin.last n)|) := by
        rw [pow_succ]
        have hmul : fp.u * (|c| + |v (Fin.last n)|) ≤
            fp.u * ((1 + fp.u)^n * m + |v (Fin.last n)|) := by
          gcongr
        have hpos : 0 ≤ ((1 + fp.u)^n - 1) * (1 + fp.u) * |v (Fin.last n)| := by
          exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hv
        nlinarith
      have habs' : |fp.fl_add c (v (Fin.last n))| ≤
          (1 + fp.u)^(n+1) * (m + |v (Fin.last n)|) := by
        rw [pow_succ]
        have hmul : (1 + fp.u) * (|c| + |v (Fin.last n)|) ≤
            (1 + fp.u) * ((1 + fp.u)^n * m + |v (Fin.last n)|) := by
          gcongr
        have hpos : 0 ≤ (1 + fp.u) * ((1 + fp.u)^n - 1) * |v (Fin.last n)| := by
          exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hv
        nlinarith
      constructor
      · simpa [c, s, m, Fin.foldl_succ_last, Fin.sum_univ_castSucc, add_assoc] using hle
      · simpa [c, s, m, Fin.foldl_succ_last, Fin.sum_univ_castSucc, add_assoc] using habs'

private lemma p43_recursive_bound (fp : P43FPModel) (b : ℕ) (hb : 0 < b)
    (v : Fin b → ℝ) :
    |p43RecursiveSum fp b v - ∑ i, v i| ≤
      ((1 + fp.u)^(b - 1) - 1) * ∑ i, |v i| := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have h := (p43_fold_bound fp n (fun i : Fin n => v i.succ) (v 0)).1
  simpa [p43RecursiveSum, Fin.foldl_succ, fp.fl_add_zero,
    Fin.sum_univ_succ, add_assoc] using h

private lemma p43_exact_le_mass {b t : ℕ} (tree : P43DotTree b t) :
    |tree.exact| ≤ tree.absMass := by
  induction tree with
  | leaf x y => simp [P43DotTree.exact, P43DotTree.absMass]
  | node children ih =>
      simp only [P43DotTree.exact, P43DotTree.absMass]
      calc
        |∑ i, (children i).exact| ≤ ∑ i, |(children i).exact| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (children i).absMass := by
          apply Finset.sum_le_sum
          intro i hi
          exact ih i

private lemma p43_tree_power_bound (fp : P43FPModel) {b t : ℕ}
    (hb : 0 < b) (tree : P43DotTree b t) :
    |tree.computed fp - tree.exact| ≤
      ((1 + fp.u)^(t * (b - 1) + 1) - 1) * tree.absMass := by
  induction tree with
  | leaf x y =>
      obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
      have he : |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
        rw [hfl]
        have hident : (x * y) * (1 + δ) - x * y = δ * (x * y) := by ring
        rw [hident, abs_mul]
        exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      simpa [P43DotTree.computed, P43DotTree.exact,
        P43DotTree.absMass] using he
  | node children ih =>
      rename_i t'
      let r : ℕ := b - 1
      let k : ℕ := t' * r + 1
      let v : Fin b → ℝ := fun i => (children i).computed fp
      let e : Fin b → ℝ := fun i => (children i).exact
      let a : Fin b → ℝ := fun i => (children i).absMass
      let M : ℝ := ∑ i, a i
      have hq : 1 ≤ (1 + fp.u)^k :=
        one_le_pow₀ (by linarith [fp.u_nonneg] : (1 : ℝ) ≤ 1 + fp.u)
      have hr : 1 ≤ (1 + fp.u)^r :=
        one_le_pow₀ (by linarith [fp.u_nonneg] : (1 : ℝ) ≤ 1 + fp.u)
      have hchild (i : Fin b) : |v i - e i| ≤ ((1 + fp.u)^k - 1) * a i := by
        exact ih i
      have hvabs (i : Fin b) : |v i| ≤ (1 + fp.u)^k * a i := by
        have htri : |v i| ≤ |v i - e i| + |e i| := by
          convert abs_add_le (v i - e i) (e i) using 1 <;> ring
        have hexact : |e i| ≤ a i := p43_exact_le_mass (children i)
        nlinarith [hchild i]
      have hsumabs : (∑ i, |v i|) ≤ (1 + fp.u)^k * M := by
        calc
          (∑ i, |v i|) ≤ ∑ i, (1 + fp.u)^k * a i := by
            apply Finset.sum_le_sum
            intro i hi
            exact hvabs i
          _ = (1 + fp.u)^k * M := by simp [M, Finset.mul_sum]
      have hsumerr : |(∑ i, v i) - (∑ i, e i)| ≤
          ((1 + fp.u)^k - 1) * M := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i, (v i - e i)| ≤ ∑ i, |v i - e i| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ((1 + fp.u)^k - 1) * a i := by
            apply Finset.sum_le_sum
            intro i hi
            exact hchild i
          _ = ((1 + fp.u)^k - 1) * M := by simp [M, Finset.mul_sum]
      have hrec := p43_recursive_bound fp b hb v
      have htotal : |p43RecursiveSum fp b v - ∑ i, e i| ≤
          ((1 + fp.u)^(k+r) - 1) * M := by
        calc
          |p43RecursiveSum fp b v - ∑ i, e i| ≤
              |p43RecursiveSum fp b v - ∑ i, v i| +
                |(∑ i, v i) - (∑ i, e i)| := abs_sub_le _ _ _
          _ ≤ ((1 + fp.u)^r - 1) * (∑ i, |v i|) +
                ((1 + fp.u)^k - 1) * M := by simpa [r] using add_le_add hrec hsumerr
          _ ≤ ((1 + fp.u)^r - 1) * ((1 + fp.u)^k * M) +
                ((1 + fp.u)^k - 1) * M := by
            gcongr
            linarith
          _ = ((1 + fp.u)^(k+r) - 1) * M := by rw [pow_add]; ring
      simpa [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass,
        v, e, a, M, k, r, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using htotal

private lemma p43_power_denom_bound (u : ℝ) (hu : 0 ≤ u) :
    ∀ n : ℕ, (n : ℝ) * u < 1 →
      (1 + u)^n * (1 - (n : ℝ) * u) ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hvalid
      have hprev : (n : ℝ) * u < 1 := by
        push_cast at hvalid
        nlinarith
      have hih := ih hprev
      have hq : 0 ≤ (1 + u)^n := pow_nonneg (by linarith) _
      have hfactor :
          (1 + u) * (1 - ((n+1 : ℕ) : ℝ) * u) ≤ 1 - (n : ℝ) * u := by
        have hsq : 0 ≤ ((n : ℝ) + 1) * u^2 :=
          mul_nonneg (by positivity) (sq_nonneg u)
        push_cast
        nlinarith
      calc
        (1 + u)^(n+1) * (1 - ((n+1 : ℕ) : ℝ) * u) =
            (1 + u)^n * ((1 + u) * (1 - ((n+1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u)^n * (1 - (n : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hfactor hq
        _ ≤ 1 := hih

private lemma p43_power_le_gamma (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hvalid : P43GammaValid u n) :
    (1 + u)^n - 1 ≤ p43Gamma u n := by
  have hv : (n : ℝ) * u < 1 := hvalid
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  have hp := p43_power_denom_bound u hu n hv
  apply (le_div_iff₀ hd).2
  change ((1 + u)^n - 1) * (1 - (n : ℝ) * u) ≤ (n : ℝ) * u
  nlinarith

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  have hpower := p43_tree_power_bound fp hb tree
  have hmass : 0 ≤ tree.absMass :=
    (abs_nonneg tree.exact).trans (p43_exact_le_mass tree)
  exact hpower.trans (mul_le_mul_of_nonneg_right
    (p43_power_le_gamma fp.u fp.u_nonneg _ hvalid) hmass)

end VSCLReuse

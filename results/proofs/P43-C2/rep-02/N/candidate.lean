import VSCLReuse.P43.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p43_add_error (fp : P43FPModel) (a z : ℝ) :
    |fp.fl_add a z - (a + z)| ≤ fp.u * |a + z| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a z
  rw [hfl]
  have heq : (a + z) * (1 + δ) - (a + z) = (a + z) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + z))

private theorem p43_mul_error (fp : P43FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private theorem p43_fold_error (fp : P43FPModel) (n : ℕ)
    (v : Fin n → ℝ) (a : ℝ) :
    |Fin.foldl n (fun acc i => fp.fl_add acc (v i)) a - (a + ∑ i, v i)| ≤
      ((1 + fp.u)^n - 1) * (|a| + ∑ i, |v i|) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let w : Fin n → ℝ := fun i => v i.castSucc
      let r := Fin.foldl n (fun acc i => fp.fl_add acc (w i)) a
      let s := a + ∑ i, w i
      let z := v (Fin.last n)
      let m := |a| + ∑ i, |w i|
      have hm : 0 ≤ m := add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hi : |r - s| ≤ ((1 + fp.u)^n - 1) * m := ih w
      have hs : |s| ≤ m := by
        calc
          |s| ≤ |a| + |∑ i, w i| := abs_add_le _ _
          _ ≤ m := by
            simpa [m, add_comm] using
              add_le_add_left (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := w)) |a|
      have hfirst : |fp.fl_add r z - (s + z)| ≤
          (1 + fp.u) * |r - s| + fp.u * (|s| + |z|) := by
        have hloc := p43_add_error fp r z
        have htri : |fp.fl_add r z - (s + z)| ≤
            |fp.fl_add r z - (r + z)| + |(r + z) - (s + z)| := abs_sub_le _ _ _
        have hrz : |r + z| ≤ |r - s| + (|s| + |z|) := by
          calc
            |r + z| = |(r - s) + (s + z)| := by congr 1; ring
            _ ≤ |r - s| + |s + z| := abs_add_le _ _
            _ ≤ |r - s| + (|s| + |z|) := by
              simpa [add_comm] using add_le_add_left (abs_add_le s z) |r - s|
        have hu := fp.u_nonneg
        have hmul := mul_le_mul_of_nonneg_left hrz hu
        have hcancel : (r + z) - (s + z) = r - s := by ring
        rw [hcancel] at htri
        nlinarith only [hloc, htri, hmul]
      have hz : 0 ≤ |z| := abs_nonneg _
      have hpow : 1 ≤ (1 + fp.u)^n := one_le_pow₀ (by linarith [fp.u_nonneg])
      have hEn : 0 ≤ (1 + fp.u)^n - 1 := by linarith
      have hbound : |fp.fl_add r z - (s + z)| ≤
          ((1 + fp.u)^(n+1) - 1) * (m + |z|) := by
        have hup : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        calc
          |fp.fl_add r z - (s + z)| ≤
              (1 + fp.u) * |r - s| + fp.u * (|s| + |z|) := hfirst
          _ ≤ (1 + fp.u) * (((1 + fp.u)^n - 1) * m) + fp.u * (m + |z|) := by
            have hmul := mul_le_mul_of_nonneg_left hi hup
            have hsmul := mul_le_mul_of_nonneg_left hs fp.u_nonneg
            nlinarith only [hmul, hsmul]
          _ ≤ ((1 + fp.u)^(n+1) - 1) * (m + |z|) := by
            rw [pow_succ]
            nlinarith only [mul_nonneg (mul_nonneg hEn hup) hz]
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc, w, r, s, z, m,
        add_assoc] using hbound

private theorem p43_sum_error (fp : P43FPModel) (b : ℕ) (hb : 0 < b)
    (v : Fin b → ℝ) :
    |p43RecursiveSum fp b v - ∑ i, v i| ≤
      ((1 + fp.u)^(b - 1) - 1) * ∑ i, |v i| := by
  cases b with
  | zero => omega
  | succ n =>
      have h := p43_fold_error fp n (fun i => v i.succ) (v 0)
      simpa only [p43RecursiveSum, Fin.foldl_succ, fp.fl_add_zero,
        Fin.sum_univ_succ, Nat.add_sub_cancel_left, add_zero] using h

private theorem p43_tree_exact_abs_le_mass {b t : ℕ} (tree : P43DotTree b t) :
    |tree.exact| ≤ tree.absMass := by
  induction tree with
  | leaf x y => simp [P43DotTree.exact, P43DotTree.absMass]
  | @node t children ih =>
      simp only [P43DotTree.exact, P43DotTree.absMass]
      calc
        |∑ i, (children i).exact| ≤ ∑ i, |(children i).exact| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (children i).absMass :=
          Finset.sum_le_sum (fun i _ => ih i)

private theorem p43_tree_pow_error (fp : P43FPModel) (b : ℕ) (hb : 0 < b) :
    ∀ {t : ℕ} (tree : P43DotTree b t),
      |tree.computed fp - tree.exact| ≤
        ((1 + fp.u)^(t * (b - 1) + 1) - 1) * tree.absMass := by
  intro t tree
  induction tree with
  | leaf x y =>
      simpa [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass]
        using p43_mul_error fp x y
  | @node t children ih =>
      let q : ℕ := t * (b - 1) + 1
      let A : ℝ := (1 + fp.u)^q
      let E : ℝ := A - 1
      let B : ℝ := (1 + fp.u)^(b - 1) - 1
      let M : ℝ := ∑ i : Fin b, (children i).absMass
      have hE : ∀ i : Fin b,
          |(children i).computed fp - (children i).exact| ≤
            E * (children i).absMass := by
        intro i
        exact ih i
      have hM : 0 ≤ M := Finset.sum_nonneg fun i _ =>
        le_trans (abs_nonneg _) (p43_tree_exact_abs_le_mass (children i))
      have hA : ∀ i : Fin b,
          |(children i).computed fp| ≤ A * (children i).absMass := by
        intro i
        calc
          |(children i).computed fp| =
              |((children i).computed fp - (children i).exact) + (children i).exact| := by
                congr 1; ring
          _ ≤ |(children i).computed fp - (children i).exact| +
                |(children i).exact| := abs_add_le _ _
          _ ≤ E * (children i).absMass + (children i).absMass :=
            add_le_add (hE i) (p43_tree_exact_abs_le_mass (children i))
          _ = A * (children i).absMass := by dsimp [E]; ring
      have hsumE :
          |(∑ i : Fin b, (children i).computed fp) -
            (∑ i : Fin b, (children i).exact)| ≤ E * M := by
        calc
          |(∑ i : Fin b, (children i).computed fp) -
            (∑ i : Fin b, (children i).exact)| =
              |∑ i : Fin b, ((children i).computed fp - (children i).exact)| := by
                rw [Finset.sum_sub_distrib]
          _ ≤ ∑ i : Fin b,
              |(children i).computed fp - (children i).exact| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin b, E * (children i).absMass :=
                Finset.sum_le_sum (fun i _ => hE i)
          _ = E * M := by rw [Finset.mul_sum]
      have hsumA :
          (∑ i : Fin b, |(children i).computed fp|) ≤ A * M := by
        calc
          _ ≤ ∑ i : Fin b, A * (children i).absMass :=
            Finset.sum_le_sum (fun i _ => hA i)
          _ = A * M := by rw [Finset.mul_sum]
      have hB : 0 ≤ B := by
        dsimp [B]
        have h : 1 ≤ (1 + fp.u)^(b - 1) :=
          one_le_pow₀ (by linarith [fp.u_nonneg])
        linarith
      have hfold := p43_sum_error fp b hb
        (fun i : Fin b => (children i).computed fp)
      have hmain :
          |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
            ∑ i : Fin b, (children i).exact| ≤
              ((1 + fp.u)^((t + 1) * (b - 1) + 1) - 1) * M := by
        have htri :
            |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
              ∑ i : Fin b, (children i).exact| ≤
            |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
              ∑ i : Fin b, (children i).computed fp| +
            |(∑ i : Fin b, (children i).computed fp) -
              (∑ i : Fin b, (children i).exact)| := abs_sub_le _ _ _
        have hfoldA :
            |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
              ∑ i : Fin b, (children i).computed fp| ≤ B * (A * M) :=
          le_trans hfold (mul_le_mul_of_nonneg_left hsumA hB)
        have hexp : (t + 1) * (b - 1) + 1 = q + (b - 1) := by
          dsimp [q]
          ring
        rw [hexp, pow_add]
        dsimp [A, B, E] at *
        nlinarith only [htri, hfoldA, hsumE]
      simpa only [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass]
        using hmain

private theorem p43_pow_mul_one_sub_le_one (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (1 + u)^k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : 0 ≤ (1 + u)^k := pow_nonneg (by linarith) _
      have hcast : 0 ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hnonneg : 0 ≤ (1 + u)^k * ((k + 1 : ℕ) : ℝ) * u^2 :=
        mul_nonneg (mul_nonneg hpow hcast) (sq_nonneg _)
      have hid :
          (1 + u)^k * (1 - (k : ℝ) * u) -
            (1 + u)^(k+1) * (1 - ((k+1 : ℕ) : ℝ) * u) =
          (1 + u)^k * ((k+1 : ℕ) : ℝ) * u^2 := by
        rw [pow_succ]
        push_cast
        ring
      linarith

private theorem p43_pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u)
    (k : ℕ) (hk : P43GammaValid u k) :
    (1 + u)^k - 1 ≤ p43Gamma u k := by
  have hden : 0 < 1 - (k : ℝ) * u := by
    exact sub_pos.mpr hk
  have hpow := p43_pow_mul_one_sub_le_one u hu k
  unfold p43Gamma
  apply (le_div_iff₀ hden).2
  nlinarith only [hpow]

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  have _ : 0 < t := ht
  have hmass : 0 ≤ tree.absMass :=
    le_trans (abs_nonneg _) (p43_tree_exact_abs_le_mass tree)
  have hpow := p43_tree_pow_error fp b hb tree
  have hgamma := p43_pow_sub_one_le_gamma fp.u fp.u_nonneg
    (t * (b - 1) + 1) hvalid
  exact le_trans hpow (mul_le_mul_of_nonneg_right hgamma hmass)

end VSCLReuse

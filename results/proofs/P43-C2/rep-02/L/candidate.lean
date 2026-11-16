import VSCLReuse.P43.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p43AsFP (fp : P43FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring
  model_sqrt := by
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem p43_recursiveSum_bound (fp : P43FPModel) (b : ℕ)
    (v : Fin b → ℝ) (hvalid : P43GammaValid fp.u (b - 1)) :
    |p43RecursiveSum fp b v - ∑ i : Fin b, v i| ≤
      p43Gamma fp.u (b - 1) * ∑ i : Fin b, |v i| := by
  have h := NumStability.recursiveSum_forward_error_bound
    (p43AsFP fp) b v hvalid
  simpa [p43RecursiveSum, NumStability.fl_recursiveSum,
    p43AsFP, p43Gamma, NumStability.gamma] using h

private theorem p43_absMass_nonneg {b t : ℕ} (tree : P43DotTree b t) :
    0 ≤ tree.absMass := by
  induction tree with
  | leaf x y => simp [P43DotTree.absMass]; positivity
  | node children ih =>
      simpa [P43DotTree.absMass] using
        (Finset.sum_nonneg (fun i _ => ih i))

private theorem p43_exact_abs_le {b t : ℕ} (tree : P43DotTree b t) :
    |tree.exact| ≤ tree.absMass := by
  induction tree with
  | leaf x y => simp [P43DotTree.exact, P43DotTree.absMass, abs_mul]
  | node children ih =>
      simpa [P43DotTree.exact, P43DotTree.absMass] using
        (le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun i _ => ih i))

private theorem p43_full_bound (fp : P43FPModel) (b : ℕ) (hb : 0 < b) :
    ∀ (t : ℕ) (tree : P43DotTree b t),
      P43GammaValid fp.u (t * (b - 1) + 1) →
      |tree.computed fp - tree.exact| ≤
        p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  intro t tree
  induction tree with
  | leaf x y =>
      intro hvalid
      simp only [Nat.zero_mul, zero_add] at hvalid
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul x y
      have hu : fp.u ≤ p43Gamma fp.u 1 := by
        have hv : NumStability.gammaValid (p43AsFP fp) 1 := by
          simpa [NumStability.gammaValid, P43GammaValid, p43AsFP] using hvalid
        simpa [NumStability.gamma, p43Gamma, p43AsFP] using
          (NumStability.u_le_gamma (p43AsFP fp) (by omega : 0 < 1) hv)
      simp only [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass,
        Nat.zero_mul, zero_add]
      rw [hmul]
      have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
      rw [heq, abs_mul]
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left (le_trans hδ hu) (abs_nonneg (x * y)))
  | @node t children ih =>
      intro hvalid
      let k : ℕ := t * (b - 1) + 1
      let j : ℕ := b - 1
      have hind : k + j = (t + 1) * (b - 1) + 1 := by
        dsimp [k, j]
        rw [Nat.add_mul]
        omega
      have hchildvalid : P43GammaValid fp.u k := by
        exact NumStability.gammaValid_mono (p43AsFP fp) (by omega : k ≤ (t + 1) * (b - 1) + 1) hvalid
      have hsumvalid : P43GammaValid fp.u j := by
        exact NumStability.gammaValid_mono (p43AsFP fp) (by omega : j ≤ (t + 1) * (b - 1) + 1) hvalid
      have hmass : 0 ≤ ∑ i : Fin b, (children i).absMass := by
        exact Finset.sum_nonneg (fun i _ => p43_absMass_nonneg (children i))
      have hchild (i : Fin b) :
          |(children i).computed fp - (children i).exact| ≤
            p43Gamma fp.u k * (children i).absMass := ih i hchildvalid
      have habs (i : Fin b) :
          |(children i).computed fp| ≤
            (1 + p43Gamma fp.u k) * (children i).absMass := by
        have he := abs_add_le ((children i).computed fp - (children i).exact)
          (children i).exact
        have hexact : |(children i).exact| ≤ (children i).absMass := by
          exact p43_exact_abs_le (children i)
        have hg : 0 ≤ p43Gamma fp.u k := by
          exact NumStability.gamma_nonneg (p43AsFP fp) hchildvalid
        have hs := mul_le_mul_of_nonneg_left hexact (by positivity : 0 ≤ (1 : ℝ))
        calc
          |(children i).computed fp| =
              |((children i).computed fp - (children i).exact) + (children i).exact| := by ring
          _ ≤ |(children i).computed fp - (children i).exact| + |(children i).exact| := he
          _ ≤ p43Gamma fp.u k * (children i).absMass + (children i).absMass :=
              add_le_add (hchild i) hexact
          _ = (1 + p43Gamma fp.u k) * (children i).absMass := by ring
      have hsum := p43_recursiveSum_bound fp b
        (fun i => (children i).computed fp) hsumvalid
      have hchildsum :
          |(∑ i : Fin b, (children i).computed fp) -
            (∑ i : Fin b, (children i).exact)| ≤
              p43Gamma fp.u k * (∑ i : Fin b, (children i).absMass) := by
        rw [← Finset.sum_sub_distrib]
        calc
          |∑ i : Fin b, ((children i).computed fp - (children i).exact)| ≤
              ∑ i : Fin b, |(children i).computed fp - (children i).exact| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i : Fin b, p43Gamma fp.u k * (children i).absMass :=
                Finset.sum_le_sum (fun i _ => hchild i)
          _ = _ := by rw [← Finset.mul_sum]
      have habssum :
          (∑ i : Fin b, |(children i).computed fp|) ≤
            (1 + p43Gamma fp.u k) * (∑ i : Fin b, (children i).absMass) := by
        calc
          _ ≤ ∑ i : Fin b, (1 + p43Gamma fp.u k) * (children i).absMass :=
              Finset.sum_le_sum (fun i _ => habs i)
          _ = _ := by rw [← Finset.mul_sum]
      have hγj : 0 ≤ p43Gamma fp.u j := by
        exact NumStability.gamma_nonneg (p43AsFP fp) hsumvalid
      have hγcomp :
          p43Gamma fp.u j * (1 + p43Gamma fp.u k) + p43Gamma fp.u k ≤
            p43Gamma fp.u ((t + 1) * (b - 1) + 1) := by
        have h := NumStability.gamma_sum_le (p43AsFP fp) k j (hind ▸ hvalid)
        change p43Gamma fp.u k + p43Gamma fp.u j +
          p43Gamma fp.u k * p43Gamma fp.u j ≤ p43Gamma fp.u (k + j) at h
        rw [hind] at h
        nlinarith [h]
      change |p43RecursiveSum fp b (fun i => (children i).computed fp) -
        ∑ i : Fin b, (children i).exact| ≤
        p43Gamma fp.u ((t + 1) * (b - 1) + 1) *
          (∑ i : Fin b, (children i).absMass)
      calc
        _ ≤ |p43RecursiveSum fp b (fun i => (children i).computed fp) -
              ∑ i : Fin b, (children i).computed fp| +
            |(∑ i : Fin b, (children i).computed fp) -
              ∑ i : Fin b, (children i).exact| := by
                convert abs_add_le
                  (p43RecursiveSum fp b (fun i => (children i).computed fp) -
                    ∑ i : Fin b, (children i).computed fp)
                  ((∑ i : Fin b, (children i).computed fp) -
                    ∑ i : Fin b, (children i).exact) using 1 <;> ring
        _ ≤ p43Gamma fp.u j * (∑ i : Fin b, |(children i).computed fp|) +
            p43Gamma fp.u k * (∑ i : Fin b, (children i).absMass) :=
              add_le_add hsum hchildsum
        _ ≤ (p43Gamma fp.u j * (1 + p43Gamma fp.u k) +
            p43Gamma fp.u k) * (∑ i : Fin b, (children i).absMass) := by
              nlinarith [mul_le_mul_of_nonneg_left habssum hγj]
        _ ≤ _ := mul_le_mul_of_nonneg_right hγcomp hmass

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  exact p43_full_bound fp b hb t tree hvalid

end VSCLReuse

import VSCLReuse.P43.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p43AsFPModel (fp : P43FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p43_sum_eq (fp : P43FPModel) (n : ℕ) (v : Fin n → ℝ) :
    p43RecursiveSum fp n v = NumStability.fl_recursiveSum (p43AsFPModel fp) n v := by
  rfl

private lemma p43_gamma_eq (fp : P43FPModel) (n : ℕ) :
    p43Gamma fp.u n = NumStability.gamma (p43AsFPModel fp) n := by
  rfl

private lemma p43_gamma_valid_eq (fp : P43FPModel) (n : ℕ) :
    P43GammaValid fp.u n = NumStability.gammaValid (p43AsFPModel fp) n := by
  rfl

private lemma p43_exact_abs_le_mass {b t : ℕ} (tree : P43DotTree b t) :
    |tree.exact| ≤ tree.absMass := by
  induction tree with
  | leaf x y => rfl
  | node children ih =>
      change |∑ i : Fin b, (children i).exact| ≤
        ∑ i : Fin b, (children i).absMass
      calc
        |∑ i : Fin b, (children i).exact| ≤
            ∑ i : Fin b, |(children i).exact| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin b, (children i).absMass :=
          Finset.sum_le_sum (fun i _ => ih i)

private theorem p43_tree_error (fp : P43FPModel) (b : ℕ) :
    ∀ t (tree : P43DotTree b t),
      P43GammaValid fp.u (t * (b - 1) + 1) →
      |tree.computed fp - tree.exact| ≤
        p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  intro t tree
  induction tree with
  | leaf x y =>
      intro hvalid
      obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
      have hu : fp.u ≤ p43Gamma fp.u 1 := by
        rw [p43_gamma_eq]
        exact NumStability.u_le_gamma (p43AsFPModel fp) (by omega)
          (by simpa [p43_gamma_valid_eq] using hvalid)
      simp only [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass,
        Nat.zero_mul, zero_add] 
      calc
        |fp.fl_mul x y - x * y| = |x * y * δ| := by rw [hfl]; congr 1; ring
        _ = |x * y| * |δ| := abs_mul _ _
        _ ≤ p43Gamma fp.u 1 * |x * y| := by
          rw [mul_comm (|x * y|) (|δ|)]
          exact mul_le_mul_of_nonneg_right (le_trans hδ hu) (abs_nonneg _)
  | node children ih =>
      intro hvalid
      rename_i k
      let f := p43AsFPModel fp
      let j := k * (b - 1) + 1
      let q := b - 1
      have hidx : (k + 1) * (b - 1) + 1 = j + q := by
        dsimp [j, q]
        simp [Nat.succ_mul]
        omega
      have htotal : NumStability.gammaValid f (j + q) := by
        rw [← p43_gamma_valid_eq]
        rw [← hidx]
        exact hvalid
      have hchild : P43GammaValid fp.u j := by
        rw [p43_gamma_valid_eq]
        exact NumStability.gammaValid_mono f (by omega) htotal
      have hsum : NumStability.gammaValid f q :=
        NumStability.gammaValid_mono f (by omega) htotal
      have hcomp : p43Gamma fp.u j + p43Gamma fp.u q +
          p43Gamma fp.u j * p43Gamma fp.u q ≤ p43Gamma fp.u (j + q) := by
        simpa [p43_gamma_eq] using NumStability.gamma_sum_le f j q htotal
      let v : Fin b → ℝ := fun i => (children i).computed fp
      obtain ⟨θ, hθ, hfold⟩ :=
        NumStability.recursiveSum_backward_error f b v hsum
      have hθ' (i : Fin b) : |θ i| ≤ p43Gamma fp.u q := by
        simpa [p43_gamma_eq] using hθ i
      have hfold' : p43RecursiveSum fp b v = ∑ i : Fin b, v i * (1 + θ i) := by
        rw [p43_sum_eq]
        exact hfold
      have hterm (i : Fin b) :
          |v i * (1 + θ i) - (children i).exact| ≤
            p43Gamma fp.u (j + q) * (children i).absMass := by
        have he := ih i hchild
        have hm : 0 ≤ (children i).absMass :=
          le_trans (abs_nonneg _) (p43_exact_abs_le_mass (children i))
        have hc : |v i| ≤ (1 + p43Gamma fp.u j) * (children i).absMass := by
          calc
            |v i| = |(v i - (children i).exact) + (children i).exact| := by
              congr 1
              ring
            _ ≤ |v i - (children i).exact| + |(children i).exact| :=
              abs_add_le _ _
            _ ≤ p43Gamma fp.u j * (children i).absMass +
                  (children i).absMass := by
              exact add_le_add (by simpa [v, j] using he)
                (p43_exact_abs_le_mass (children i))
            _ = (1 + p43Gamma fp.u j) * (children i).absMass := by ring
        have hp : |v i| * |θ i| ≤
            ((1 + p43Gamma fp.u j) * (children i).absMass) *
              p43Gamma fp.u q := by
          exact mul_le_mul hc (hθ' i) (abs_nonneg _)
            (le_trans (abs_nonneg _) hc)
        calc
          |v i * (1 + θ i) - (children i).exact| =
              |(v i - (children i).exact) + v i * θ i| := by
                congr 1
                ring
          _ ≤ |v i - (children i).exact| + |v i * θ i| := abs_add_le _ _
          _ = |v i - (children i).exact| + |v i| * |θ i| := by rw [abs_mul]
          _ ≤ p43Gamma fp.u j * (children i).absMass +
              ((1 + p43Gamma fp.u j) * (children i).absMass) *
                p43Gamma fp.u q := by
              exact add_le_add (by simpa [v, j] using he) hp
          _ = (p43Gamma fp.u j + p43Gamma fp.u q +
                p43Gamma fp.u j * p43Gamma fp.u q) *
                (children i).absMass := by ring
          _ ≤ p43Gamma fp.u (j + q) * (children i).absMass :=
            mul_le_mul_of_nonneg_right hcomp hm
      simp only [P43DotTree.computed, P43DotTree.exact, P43DotTree.absMass]
      rw [hidx]
      change |p43RecursiveSum fp b v - ∑ i : Fin b, (children i).exact| ≤
        p43Gamma fp.u (j + q) * ∑ i : Fin b, (children i).absMass
      rw [hfold', ← Finset.sum_sub_distrib]
      calc
        |∑ i : Fin b, (v i * (1 + θ i) - (children i).exact)| ≤
            ∑ i : Fin b, |v i * (1 + θ i) - (children i).exact| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin b, p43Gamma fp.u (j + q) * (children i).absMass :=
          Finset.sum_le_sum (fun i _ => hterm i)
        _ = p43Gamma fp.u (j + q) * ∑ i : Fin b, (children i).absMass := by
          rw [Finset.mul_sum]

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  exact p43_tree_error fp b t tree hvalid

end VSCLReuse

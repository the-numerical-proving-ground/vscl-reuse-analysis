import VSCLReuse.P43.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p43Proxy (fp : P43FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private theorem p43_exact_abs_le_mass (b : ℕ) :
    ∀ t (tree : P43DotTree b t), |tree.exact| ≤ tree.absMass := by
  intro t
  induction t with
  | zero =>
      intro tree
      cases tree with
      | leaf x y => rfl
  | succ t ih =>
      intro tree
      cases tree with
      | node children =>
          change |∑ i : Fin b, (children i).exact| ≤
            ∑ i : Fin b, (children i).absMass
          calc
            |∑ i : Fin b, (children i).exact|
                ≤ ∑ i : Fin b, |(children i).exact| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin b, (children i).absMass := by
                  exact Finset.sum_le_sum (fun i _ => ih (children i))

private theorem p43_tree_bound (fp : P43FPModel) (b : ℕ) (hb : 0 < b) :
    ∀ t (tree : P43DotTree b t),
      P43GammaValid fp.u (t * (b - 1) + 1) →
      |tree.computed fp - tree.exact| ≤
        p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  intro t
  induction t with
  | zero =>
      intro tree hvalid
      cases tree with
      | leaf x y =>
          obtain ⟨δ, hδ, hmul⟩ := fp.model_mul x y
          have hval1 : NumStability.gammaValid (p43Proxy fp) 1 := by
            simpa [P43GammaValid, NumStability.gammaValid, p43Proxy] using hvalid
          have hu : fp.u ≤ p43Gamma fp.u 1 := by
            simpa [NumStability.gamma, p43Gamma, p43Proxy] using
              (NumStability.u_le_gamma (p43Proxy fp) (by omega : 0 < 1) hval1)
          simp only [P43DotTree.computed, P43DotTree.exact,
            P43DotTree.absMass, Nat.zero_mul, zero_add] at ⊢
          calc
            |fp.fl_mul x y - x * y| = |x * y| * |δ| := by
              rw [hmul]
              have heq : x * y * (1 + δ) - x * y = x * y * δ := by ring
              rw [heq, abs_mul]
            _ ≤ |x * y| * fp.u :=
              mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
            _ ≤ p43Gamma fp.u 1 * |x * y| := by
              rw [mul_comm (|x * y|) fp.u]
              exact mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  | succ t ih =>
      intro tree hvalid
      cases tree with
      | node children =>
          let k := t * (b - 1) + 1
          let l := b - 1
          let gk := p43Gamma fp.u k
          let gl := p43Gamma fp.u l
          let mass := ∑ i : Fin b, (children i).absMass
          have hindex : k + l = (t + 1) * (b - 1) + 1 := by
            dsimp [k, l]
            simp [Nat.add_mul]
            omega
          have hval : NumStability.gammaValid (p43Proxy fp) (k + l) := by
            simpa [P43GammaValid, NumStability.gammaValid, p43Proxy, hindex] using hvalid
          have hvalk : P43GammaValid fp.u k := by
            have h := NumStability.gammaValid_mono (p43Proxy fp)
              (Nat.le_add_right k l) hval
            simpa [P43GammaValid, NumStability.gammaValid, p43Proxy] using h
          have hvall : NumStability.gammaValid (p43Proxy fp) l :=
            NumStability.gammaValid_mono (p43Proxy fp) (Nat.le_add_left l k) (by
              simpa [Nat.add_comm] using hval)
          have hgk : 0 ≤ gk := by
            have h : NumStability.gammaValid (p43Proxy fp) k := by
              simpa [P43GammaValid, NumStability.gammaValid, p43Proxy] using hvalk
            simpa [gk, NumStability.gamma, p43Gamma, p43Proxy] using
              (NumStability.gamma_nonneg (p43Proxy fp) h)
          have hgl : 0 ≤ gl := by
            simpa [gl, NumStability.gamma, p43Gamma, p43Proxy] using
              (NumStability.gamma_nonneg (p43Proxy fp) hvall)
          have hchild (i : Fin b) :
              |(children i).computed fp - (children i).exact| ≤
                gk * (children i).absMass := ih (children i) hvalk
          have hmass : 0 ≤ mass := by
            dsimp [mass]
            exact Finset.sum_nonneg (fun i _ => by
              exact le_trans (abs_nonneg _) (p43_exact_abs_le_mass b t (children i)))
          have hcomp (i : Fin b) :
              |(children i).computed fp| ≤ (1 + gk) * (children i).absMass := by
            have htri : |(children i).computed fp| ≤
                |(children i).computed fp - (children i).exact| +
                  |(children i).exact| := by
              have h := abs_add_le
                ((children i).computed fp - (children i).exact)
                (children i).exact
              convert h using 1 <;> ring
            calc
              |(children i).computed fp| ≤
                  |(children i).computed fp - (children i).exact| +
                    |(children i).exact| := htri
              _ ≤ gk * (children i).absMass + (children i).absMass :=
                  add_le_add (hchild i) (p43_exact_abs_le_mass b t (children i))
              _ = (1 + gk) * (children i).absMass := by ring
          have hsumcomp : (∑ i : Fin b, |(children i).computed fp|) ≤
              (1 + gk) * mass := by
            calc
              (∑ i : Fin b, |(children i).computed fp|) ≤
                  ∑ i : Fin b, (1 + gk) * (children i).absMass :=
                    Finset.sum_le_sum (fun i _ => hcomp i)
              _ = (1 + gk) * mass := by simp [mass, Finset.mul_sum]
          have hsumerr :
              (∑ i : Fin b, |(children i).computed fp - (children i).exact|) ≤
                gk * mass := by
            calc
              (∑ i : Fin b, |(children i).computed fp - (children i).exact|) ≤
                  ∑ i : Fin b, gk * (children i).absMass :=
                    Finset.sum_le_sum (fun i _ => hchild i)
              _ = gk * mass := by simp [mass, Finset.mul_sum]
          have hsum :
              |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
                ∑ i : Fin b, (children i).computed fp| ≤
                gl * ∑ i : Fin b, |(children i).computed fp| := by
            have h := NumStability.recursiveSum_forward_error_bound
              (p43Proxy fp) b (fun i : Fin b => (children i).computed fp) hvall
            simpa [p43RecursiveSum, NumStability.fl_recursiveSum,
              p43Proxy, gl, p43Gamma, NumStability.gamma] using h
          have hgam : gk + gl + gk * gl ≤
              p43Gamma fp.u ((t + 1) * (b - 1) + 1) := by
            obtain ⟨θ, hθ, heq⟩ := NumStability.gamma_mul (p43Proxy fp)
              k l (NumStability.gamma (p43Proxy fp) k)
              (NumStability.gamma (p43Proxy fp) l)
              (by rw [abs_of_nonneg (by
                  simpa [gk, p43Gamma, NumStability.gamma, p43Proxy] using hgk)])
              (by rw [abs_of_nonneg (by
                  simpa [gl, p43Gamma, NumStability.gamma, p43Proxy] using hgl)]) hval
            have hθeq : θ = gk + gl + gk * gl := by
              simp only [NumStability.gamma, p43Proxy] at heq
              dsimp [gk, gl, p43Gamma]
              nlinarith [heq]
            rw [hθeq] at hθ
            have hmain := le_trans (le_abs_self (gk + gl + gk * gl)) hθ
            simpa [NumStability.gamma, p43Gamma, p43Proxy, hindex] using hmain
          change |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
            ∑ i : Fin b, (children i).exact| ≤
            p43Gamma fp.u ((t + 1) * (b - 1) + 1) * mass
          have htri :
              |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
                ∑ i : Fin b, (children i).exact| ≤
                |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
                  ∑ i : Fin b, (children i).computed fp| +
                |(∑ i : Fin b, (children i).computed fp) -
                  ∑ i : Fin b, (children i).exact| := by
            convert abs_add_le
              (p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
                ∑ i : Fin b, (children i).computed fp)
              ((∑ i : Fin b, (children i).computed fp) -
                ∑ i : Fin b, (children i).exact) using 1 <;> ring
          calc
            _ ≤ |p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp) -
                  ∑ i : Fin b, (children i).computed fp| +
                |(∑ i : Fin b, (children i).computed fp) -
                  ∑ i : Fin b, (children i).exact| := htri
            _ ≤ gl * (∑ i : Fin b, |(children i).computed fp|) +
                  ∑ i : Fin b, |(children i).computed fp - (children i).exact| := by
                apply add_le_add hsum
                rw [← Finset.sum_sub_distrib]
                exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ gl * ((1 + gk) * mass) + gk * mass := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hsumcomp hgl) hsumerr
            _ = (gk + gl + gk * gl) * mass := by ring
            _ ≤ p43Gamma fp.u ((t + 1) * (b - 1) + 1) * mass :=
                mul_le_mul_of_nonneg_right hgam hmass

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  exact p43_tree_bound fp b hb t tree hvalid

end VSCLReuse

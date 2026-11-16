import VSCLReuse.P38.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p38AsFPModel (fp : P38FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := by
    intro x hx
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

private theorem p38_gamma_bridge (fp : P38FPModel) (n : ℕ) :
    NumStability.gamma (p38AsFPModel fp) n = p38Gamma fp.u n := by
  rfl

private theorem p38_dot_bridge (fp : P38FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    NumStability.fl_dotProduct (p38AsFPModel fp) n x y =
      p38RoundedDotProduct fp n x y := by
  rfl

private theorem p38_steps_bridge (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p38AsFPModel fp) n L b k hk x =
        p38ForwardSubSteps fp n L b k hk x := by
  intro k
  induction k with
  | zero =>
    intro hk x
    rfl
  | succ k ih =>
    intro hk x
    unfold NumStability.fl_forwardSub_steps p38ForwardSubSteps
    exact ih (Nat.le_of_succ_le hk) _

private theorem p38_forward_bridge (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_forwardSub (p38AsFPModel fp) n L b =
      p38ForwardSub fp n L b := by
  exact p38_steps_bridge fp n L b n (le_refl n) (fun _ => 0)

/-- The Method B off-diagonal block estimate in the proof of (6.1). -/
theorem p38_c3_methodB_offdiagonal_residual
    (fp : P38FPModel) (n r p : ℕ)
    (L22 : P38Matrix n n) (L21 : P38Matrix n r)
    (X11 : P38Matrix r p)
    (hdiag : ∀ i, L22 i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L22 i j = 0)
    (hn : P38GammaValid fp.u n)
    (hr : P38GammaValid fp.u r) :
    ∀ i j,
      |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
      p38Gamma fp.u r *
        (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
  -- PROOF_START P38-C3-H001
  let M := p38AsFPModel fp
  have hnM : NumStability.gammaValid M n := hn
  have hrM : NumStability.gammaValid M r := hr
  intro i j
  let b : Fin n → ℝ := fun k => -(p38RoundedMatMul fp L21 X11 k j)
  obtain ⟨ΔL, hΔL, hsolve⟩ :=
    NumStability.forwardSub_backward_error M n L22 b hdiag hlower hnM
  have hsolve' :
      (∑ k : Fin n, (L22 i k + ΔL i k) *
        p38MethodBOffDiagonal fp L22 L21 X11 k j) =
        -(p38RoundedMatMul fp L21 X11 i j) := by
    simpa only [M, b, p38_forward_bridge, p38MethodBOffDiagonal] using hsolve i
  have hdot :=
    NumStability.dotProduct_error_bound M r (L21 i) (fun k => X11 k j) hrM
  have hdot' :
      |p38RoundedMatMul fp L21 X11 i j -
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    simpa only [M, p38RoundedMatMul, p38_dot_bridge, p38_gamma_bridge] using hdot
  have hdelta :
      |∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) := by
    calc
      _ ≤ ∑ k : Fin n, |ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |ΔL i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j| := by
        simp only [abs_mul]
      _ ≤ ∑ k : Fin n,
          (p38Gamma fp.u n * |L22 i k|) *
            |p38MethodBOffDiagonal fp L22 L21 X11 k j| := by
        apply Finset.sum_le_sum
        intro k hk
        have hbound : |ΔL i k| ≤ p38Gamma fp.u n * |L22 i k| := by
          simpa only [M, p38_gamma_bridge] using hΔL i k
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = p38Gamma fp.u n *
          (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) := by
        rw [Finset.mul_sum]
        congr 1
        funext k
        ring
  have hresid :
      (∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j) =
      -(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) -
        (p38RoundedMatMul fp L21 X11 i j -
          (∑ k : Fin r, L21 i k * X11 k j)) := by
    have hsolve'' := hsolve'
    simp only [add_mul, Finset.sum_add_distrib] at hsolve''
    linear_combination hsolve'' 
  rw [hresid]
  calc
    _ ≤ |-(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j)| +
      |p38RoundedMatMul fp L21 X11 i j -
        (∑ k : Fin r, L21 i k * X11 k j)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le
          (-(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j))
          (-(p38RoundedMatMul fp L21 X11 i j -
            (∑ k : Fin r, L21 i k * X11 k j))))
    _ ≤ _ := by
      rw [abs_neg]
      exact add_le_add hdelta hdot'


end VSCLReuse

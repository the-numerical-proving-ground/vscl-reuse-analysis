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

private lemma p38ForwardSubSteps_eq (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
      p38ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p38AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      unfold p38ForwardSubSteps NumStability.fl_forwardSub_steps
      exact ih (Nat.le_of_succ_le hk) _

private lemma p38ForwardSub_eq (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    p38ForwardSub fp n L b =
      NumStability.fl_forwardSub (p38AsFPModel fp) n L b := by
  exact p38ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

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
  let fpm := p38AsFPModel fp
  have hgn : NumStability.gammaValid fpm n := hn
  have hgr : NumStability.gammaValid fpm r := hr
  intro i j
  let b : Fin n → ℝ := fun k => -(p38RoundedMatMul fp L21 X11 k j)
  let x : Fin n → ℝ := p38ForwardSub fp n L22 b
  obtain ⟨ΔL, hΔL, hsolve₀⟩ :=
    NumStability.forwardSub_backward_error fpm n L22 b hdiag hlower hgn
  have hsolve :
      (∑ k : Fin n, (L22 i k + ΔL i k) * x k) =
        -p38RoundedMatMul fp L21 X11 i j := by
    simpa only [x, p38ForwardSub_eq, b] using hsolve₀ i
  have hproduct :
      |p38RoundedMatMul fp L21 X11 i j -
          ∑ k : Fin r, L21 i k * X11 k j| ≤
        p38Gamma fp.u r *
          ∑ k : Fin r, |L21 i k| * |X11 k j| := by
    exact NumStability.dotProduct_error_bound fpm r (L21 i) (fun k => X11 k j) hgr
  have herror :
      |∑ k : Fin n, ΔL i k * x k| ≤
        p38Gamma fp.u n * ∑ k : Fin n, |L22 i k| * |x k| := by
    calc
      |∑ k : Fin n, ΔL i k * x k| ≤
          ∑ k : Fin n, |ΔL i k * x k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |ΔL i k| * |x k| := by simp only [abs_mul]
      _ ≤ ∑ k : Fin n, (p38Gamma fp.u n * |L22 i k|) * |x k| := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (hΔL i k) (abs_nonneg _)
      _ = p38Gamma fp.u n * ∑ k : Fin n, |L22 i k| * |x k| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hsplit :
      (∑ k : Fin n, L22 i k * x k) + (∑ k : Fin n, ΔL i k * x k) =
        -p38RoundedMatMul fp L21 X11 i j := by
    calc
      _ = ∑ k : Fin n, (L22 i k + ΔL i k) * x k := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := hsolve
  change
    |(∑ k : Fin n, L22 i k * x k) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u n * (∑ k : Fin n, |L22 i k| * |x k|) +
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|)
  have hidentity :
      (∑ k : Fin n, L22 i k * x k) + (∑ k : Fin r, L21 i k * X11 k j) =
        -(∑ k : Fin n, ΔL i k * x k) +
          ((∑ k : Fin r, L21 i k * X11 k j) -
            p38RoundedMatMul fp L21 X11 i j) := by
    linarith [hsplit]
  calc
    |(∑ k : Fin n, L22 i k * x k) +
        (∑ k : Fin r, L21 i k * X11 k j)| =
      |-(∑ k : Fin n, ΔL i k * x k) +
        ((∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j)| := by rw [hidentity]
    _ ≤ |-(∑ k : Fin n, ΔL i k * x k)| +
        |(∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j| := abs_add_le _ _
    _ = |∑ k : Fin n, ΔL i k * x k| +
        |p38RoundedMatMul fp L21 X11 i j -
          ∑ k : Fin r, L21 i k * X11 k j| := by rw [abs_neg, abs_sub_comm]
    _ ≤ _ := add_le_add herror hproduct

end VSCLReuse

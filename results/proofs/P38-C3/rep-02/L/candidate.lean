import VSCLReuse.P38.Definitions
import NumStability.Algorithms.MatMul
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

private theorem p38_rounded_mul_eq (fp : P38FPModel) {m n p : ℕ}
    (A : P38Matrix m n) (B : P38Matrix n p) (i : Fin m) (j : Fin p) :
    p38RoundedMatMul fp A B i j =
      NumStability.fl_matMul (p38AsFPModel fp) m n p A B i j := by
  rfl

private theorem p38_forward_sub_steps_eq (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) :
    ∀ k (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      p38ForwardSubSteps fp n L b k hk x i =
        NumStability.fl_forwardSub_steps (p38AsFPModel fp) n L b k hk x i := by
  intro k
  induction k with
  | zero =>
      intros
      rfl
  | succ k ih =>
      intro hk x i
      unfold p38ForwardSubSteps NumStability.fl_forwardSub_steps
      apply ih

private theorem p38_forward_sub_eq (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ) (i : Fin n) :
    p38ForwardSub fp n L b i =
      NumStability.fl_forwardSub (p38AsFPModel fp) n L b i := by
  exact p38_forward_sub_steps_eq fp n L b n (le_refl n) (fun _ => 0) i

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
  intro i j
  have hn' : NumStability.gammaValid (p38AsFPModel fp) n := hn
  have hr' : NumStability.gammaValid (p38AsFPModel fp) r := hr
  let b : Fin n → ℝ := fun k => -p38RoundedMatMul fp L21 X11 k j
  obtain ⟨ΔL, hΔL_bound, hΔL_eq⟩ :=
    NumStability.forwardSub_backward_error
      (p38AsFPModel fp) n L22 b hdiag hlower hn'
  have hsolve :
      (∑ k : Fin n,
        (L22 i k + ΔL i k) * p38MethodBOffDiagonal fp L22 L21 X11 k j) =
        -p38RoundedMatMul fp L21 X11 i j := by
    change (∑ k : Fin n,
        (L22 i k + ΔL i k) *
          p38ForwardSub fp n L22 (fun t => -p38RoundedMatMul fp L21 X11 t j) k) =
      -p38RoundedMatMul fp L21 X11 i j
    simp_rw [p38_forward_sub_eq]
    exact hΔL_eq i
  have hsplit :
      (∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
      (∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) =
        -p38RoundedMatMul fp L21 X11 i j := by
    simpa only [add_mul, Finset.sum_add_distrib] using hsolve
  have hΔL_bound' (a c : Fin n) :
      |ΔL a c| ≤ p38Gamma fp.u n * |L22 a c| := by
    exact hΔL_bound a c
  have hsolve_err :
      |∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j| ≤
        p38Gamma fp.u n *
          (∑ k : Fin n,
            |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) := by
    calc
      |∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j|
          ≤ ∑ k : Fin n,
              |ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n,
            |ΔL i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j| := by
          apply Finset.sum_congr rfl
          intro k _
          exact abs_mul _ _
      _ ≤ ∑ k : Fin n,
            (p38Gamma fp.u n * |L22 i k|) *
              |p38MethodBOffDiagonal fp L22 L21 X11 k j| := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_right (hΔL_bound' i k) (abs_nonneg _)
      _ = p38Gamma fp.u n *
            (∑ k : Fin n,
              |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
  have hmul :
      |p38RoundedMatMul fp L21 X11 i j -
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    simpa only [← p38_rounded_mul_eq] using
      (NumStability.matMul_error_bound
        (p38AsFPModel fp) n r p L21 X11 hr' i j)
  have hmul' :
      |(∑ k : Fin r, L21 i k * X11 k j) -
        p38RoundedMatMul fp L21 X11 i j| ≤
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    simpa only [abs_sub_comm] using hmul
  have hidentity :
      (∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
      (∑ k : Fin r, L21 i k * X11 k j) =
      -(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        ((∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j) := by
    linarith [hsplit]
  rw [hidentity]
  calc
    |-(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        ((∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j)|
        ≤ |-(∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j)| +
          |(∑ k : Fin r, L21 i k * X11 k j) -
            p38RoundedMatMul fp L21 X11 i j| := abs_add_le _ _
    _ = |∑ k : Fin n, ΔL i k * p38MethodBOffDiagonal fp L22 L21 X11 k j| +
          |(∑ k : Fin r, L21 i k * X11 k j) -
            p38RoundedMatMul fp L21 X11 i j| := by rw [abs_neg]
    _ ≤ p38Gamma fp.u n *
          (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
        p38Gamma fp.u r *
          (∑ k : Fin r, |L21 i k| * |X11 k j|) :=
      add_le_add hsolve_err hmul'

end VSCLReuse

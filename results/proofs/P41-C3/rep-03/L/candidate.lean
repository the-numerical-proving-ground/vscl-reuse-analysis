import VSCLReuse.P41.Definitions
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p41AsFPModel (fp : P41FPModel) : NumStability.FPModel where
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
    intro x _
    refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
    ring

private theorem p41_gamma_bridge (fp : P41FPModel) (n : ℕ) :
    NumStability.gamma (p41AsFPModel fp) n = p41Gamma fp.u n := rfl

private theorem p41_forward_steps_bridge (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p41AsFPModel fp) n L b k hk x =
        p41ForwardSubSteps fp n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [NumStability.fl_forwardSub_steps, p41ForwardSubSteps]
      exact ih (Nat.le_of_succ_le hk) _

private theorem p41_forward_bridge (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_forwardSub (p41AsFPModel fp) n L b =
      p41ForwardSub fp n L b :=
  p41_forward_steps_bridge fp n L b n (le_refl n) _

private theorem p41_back_steps_bridge (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_backSub_steps (p41AsFPModel fp) n U b k hk x =
        p41BackSubSteps fp n U b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [NumStability.fl_backSub_steps, p41BackSubSteps]
      exact ih (Nat.le_of_succ_le hk) _

private theorem p41_back_bridge (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_backSub (p41AsFPModel fp) n U b =
      p41BackSub fp n U b :=
  p41_back_steps_bridge fp n U b n (le_refl n) _

private theorem p41_solve_bridge (fp : P41FPModel) (n : ℕ)
    (L U : P41Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_backSub (p41AsFPModel fp) n U
      (NumStability.fl_forwardSub (p41AsFPModel fp) n L b) =
        p41LUSolve fp n L U b := by
  rw [p41_forward_bridge, p41_back_bridge]
  rfl

private theorem p41_dot_bridge (fp : P41FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    NumStability.fl_dotProduct (p41AsFPModel fp) n x y =
      p41RoundedDotProduct fp n x y := rfl

/-- The G-stage block residual at a node whose child systems are GE leaves. -/
theorem p41_c3_G_stage_leaf_residual
    (fp : P41FPModel) (n : ℕ)
    (Ase Anw Ane Ls Us Ln Un : P41Matrix n n)
    (uvec : Fin n → ℝ)
    (hLs : P41LUCertificate fp n Ase Ls Us)
    (hLn : P41LUCertificate fp n Anw Ln Un)
    (hUsdiag : ∀ i : Fin n, Us i i ≠ 0)
    (hUndiag : ∀ i : Fin n, Un i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    let gs := p41LUSolve fp n Ls Us uvec
    let w := p41RoundedMatVec fp n Ane gs
    let gn := p41LUSolve fp n Ln Un w
    ∃ Ds Dn : P41Matrix n n, ∃ dw : Fin n → ℝ,
      (∀ i j, |Ds i j| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ls i k| * |Us k j|) ∧
      (∀ i j, |Dn i j| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ln i k| * |Un k j|) ∧
      (∀ i, |dw i| ≤ p41Gamma fp.u n *
        ∑ j : Fin n, |Ane i j| * |gs j|) ∧
      (∀ i,
        (∑ j : Fin n, Ase i j * gs j) - uvec i =
          -(∑ j : Fin n, Ds i j * gs j) ∧
        (∑ j : Fin n, Anw i j * gn j) -
          (∑ j : Fin n, Ane i j * gs j) =
            dw i - (∑ j : Fin n, Dn i j * gn j)) := by
  -- PROOF_START P41-C3-H001
  let f := p41AsFPModel fp
  have hv : NumStability.gammaValid f n := hvalid
  have hLs' : NumStability.LUBackwardError n Ase Ls Us
      (NumStability.gamma f n) := by
    refine ⟨hLs.L_diag, hLs.L_upper_zero, hLs.U_lower_zero, ?_⟩
    simpa only [p41_gamma_bridge] using hLs.backward_bound
  have hLn' : NumStability.LUBackwardError n Anw Ln Un
      (NumStability.gamma f n) := by
    refine ⟨hLn.L_diag, hLn.L_upper_zero, hLn.U_lower_zero, ?_⟩
    simpa only [p41_gamma_bridge] using hLn.backward_bound
  have hLsdiag : ∀ i : Fin n, Ls i i ≠ 0 := by
    intro i
    rw [hLs.L_diag i]
    norm_num
  have hLndiag : ∀ i : Fin n, Ln i i ≠ 0 := by
    intro i
    rw [hLn.L_diag i]
    norm_num
  dsimp
  obtain ⟨Ds, hDs, hDsEq⟩ :=
    NumStability.lu_solve_backward_error f n Ase Ls Us uvec
      hLsdiag hUsdiag hLs' hv
  obtain ⟨Dn, hDn, hDnEq⟩ :=
    NumStability.lu_solve_backward_error f n Anw Ln Un
      (p41RoundedMatVec fp n Ane (p41LUSolve fp n Ls Us uvec))
      hLndiag hUndiag hLn' hv
  let gs := p41LUSolve fp n Ls Us uvec
  let w := p41RoundedMatVec fp n Ane gs
  let gn := p41LUSolve fp n Ln Un w
  let dw : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Ane i j * gs j
  have hDsEq' : ∀ i, ∑ j : Fin n, (Ase i j + Ds i j) * gs j = uvec i := by
    intro i
    simpa only [f, p41_solve_bridge] using hDsEq i
  have hDnEq' : ∀ i, ∑ j : Fin n, (Anw i j + Dn i j) * gn j = w i := by
    intro i
    simpa only [f, p41_solve_bridge] using hDnEq i
  refine ⟨Ds, Dn, dw, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [p41_gamma_bridge] using hDs i j
  · intro i j
    simpa only [p41_gamma_bridge] using hDn i j
  · intro i
    have hdot := NumStability.dotProduct_error_bound f n (Ane i) gs hv
    simpa only [p41_gamma_bridge, p41_dot_bridge] using hdot
  · intro i
    constructor
    · rw [← hDsEq' i]
      simp_rw [add_mul, Finset.sum_add_distrib]
      ring
    · change (∑ j : Fin n, Anw i j * gn j) - (∑ j : Fin n, Ane i j * gs j) =
          (w i - ∑ j : Fin n, Ane i j * gs j) - (∑ j : Fin n, Dn i j * gn j)
      have heq := hDnEq' i
      simp_rw [add_mul, Finset.sum_add_distrib] at heq
      linarith

end VSCLReuse

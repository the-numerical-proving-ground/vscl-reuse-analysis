import VSCLReuse.P41.Definitions
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.MatVec

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p41ToFPModel (fp : P41FPModel) : NumStability.FPModel where
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
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private theorem p41ForwardSubSteps_eq (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
      p41ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p41ToFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      unfold p41ForwardSubSteps NumStability.fl_forwardSub_steps
      exact ih (Nat.le_of_succ_le hk) _

private theorem p41ForwardSub_eq (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    p41ForwardSub fp n L b = NumStability.fl_forwardSub (p41ToFPModel fp) n L b := by
  exact p41ForwardSubSteps_eq fp n L b n (le_refl n) _

private theorem p41BackSubSteps_eq (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
      p41BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p41ToFPModel fp) n U b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      unfold p41BackSubSteps NumStability.fl_backSub_steps
      exact ih (Nat.le_of_succ_le hk) _

private theorem p41BackSub_eq (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    p41BackSub fp n U b = NumStability.fl_backSub (p41ToFPModel fp) n U b := by
  exact p41BackSubSteps_eq fp n U b n (le_refl n) _

private theorem p41LUSolve_eq (fp : P41FPModel) (n : ℕ)
    (L U : P41Matrix n n) (b : Fin n → ℝ) :
    p41LUSolve fp n L U b =
      NumStability.fl_backSub (p41ToFPModel fp) n U
        (NumStability.fl_forwardSub (p41ToFPModel fp) n L b) := by
  unfold p41LUSolve
  rw [p41ForwardSub_eq, p41BackSub_eq]

private theorem p41RoundedMatVec_eq (fp : P41FPModel) (n : ℕ)
    (A : P41Matrix n n) (x : Fin n → ℝ) :
    p41RoundedMatVec fp n A x =
      NumStability.fl_matVec (p41ToFPModel fp) n n A x := by
  rfl

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
  intro gs w gn
  let F := p41ToFPModel fp
  have hgamma : NumStability.gamma F n = p41Gamma fp.u n := rfl
  have hvalid' : NumStability.gammaValid F n := hvalid
  have hLs' : NumStability.LUBackwardError n Ase Ls Us
      (NumStability.gamma F n) := {
    L_diag := hLs.L_diag
    L_upper_zero := hLs.L_upper_zero
    U_lower_zero := hLs.U_lower_zero
    backward_bound := by
      intro i j
      simpa only [hgamma] using hLs.backward_bound i j }
  have hLn' : NumStability.LUBackwardError n Anw Ln Un
      (NumStability.gamma F n) := {
    L_diag := hLn.L_diag
    L_upper_zero := hLn.L_upper_zero
    U_lower_zero := hLn.U_lower_zero
    backward_bound := by
      intro i j
      simpa only [hgamma] using hLn.backward_bound i j }
  have hLsdiag : ∀ i : Fin n, Ls i i ≠ 0 := by
    intro i
    rw [hLs.L_diag i]
    norm_num
  have hLndiag : ∀ i : Fin n, Ln i i ≠ 0 := by
    intro i
    rw [hLn.L_diag i]
    norm_num
  obtain ⟨Ds, hDs_bound, hDs_eq⟩ :=
    NumStability.lu_solve_backward_error F n Ase Ls Us uvec
      hLsdiag hUsdiag hLs' hvalid'
  obtain ⟨Dn, hDn_bound, hDn_eq⟩ :=
    NumStability.lu_solve_backward_error F n Anw Ln Un w
      hLndiag hUndiag hLn' hvalid'
  let dw : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Ane i j * gs j
  have hgs : gs = NumStability.fl_backSub F n Us
      (NumStability.fl_forwardSub F n Ls uvec) := by
    exact p41LUSolve_eq fp n Ls Us uvec
  have hgn : gn = NumStability.fl_backSub F n Un
      (NumStability.fl_forwardSub F n Ln w) := by
    exact p41LUSolve_eq fp n Ln Un w
  have hw : w = NumStability.fl_matVec F n n Ane gs := by
    exact p41RoundedMatVec_eq fp n Ane gs
  have hDs_eq' : ∀ i,
      (∑ j : Fin n, (Ase i j + Ds i j) * gs j) = uvec i := by
    simpa only [hgs] using hDs_eq
  have hDn_eq' : ∀ i,
      (∑ j : Fin n, (Anw i j + Dn i j) * gn j) = w i := by
    simpa only [hgn] using hDn_eq
  have hdw_bound : ∀ i,
      |dw i| ≤ p41Gamma fp.u n *
        ∑ j : Fin n, |Ane i j| * |gs j| := by
    intro i
    have h := NumStability.matVec_error_bound F n n Ane gs hvalid' i
    simpa only [← hgamma, dw, hw] using h
  refine ⟨Ds, Dn, dw, ?_, ?_, hdw_bound, ?_⟩
  · intro i j
    simpa only [← hgamma] using hDs_bound i j
  · intro i j
    simpa only [← hgamma] using hDn_bound i j
  · intro i
    constructor
    · have h := hDs_eq' i
      simp_rw [add_mul, Finset.sum_add_distrib] at h
      linarith
    · have h := hDn_eq' i
      simp_rw [add_mul, Finset.sum_add_distrib] at h
      dsimp only [dw]
      linarith

end VSCLReuse

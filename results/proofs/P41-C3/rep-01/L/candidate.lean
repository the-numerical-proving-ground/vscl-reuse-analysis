import VSCLReuse.P41.Definitions
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.MatVec

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
    intro x hx
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private lemma p41AsFPModel_gamma (fp : P41FPModel) (n : ℕ) :
    NumStability.gamma (p41AsFPModel fp) n = p41Gamma fp.u n := rfl

private lemma p41AsFPModel_valid (fp : P41FPModel) (n : ℕ)
    (h : P41GammaValid fp.u n) :
    NumStability.gammaValid (p41AsFPModel fp) n := h

private lemma p41AsFPModel_forward_steps (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) (k : ℕ) :
    ∀ (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_forwardSub_steps (p41AsFPModel fp) n L b k hk x =
        p41ForwardSubSteps fp n L b k hk x := by
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [NumStability.fl_forwardSub_steps, p41ForwardSubSteps]
      exact ih _ _

private lemma p41AsFPModel_forward (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_forwardSub (p41AsFPModel fp) n L b =
      p41ForwardSub fp n L b := by
  unfold NumStability.fl_forwardSub p41ForwardSub
  exact p41AsFPModel_forward_steps fp n L b n _ _

private lemma p41AsFPModel_back_steps (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) (k : ℕ) :
    ∀ (hk : k ≤ n) (x : Fin n → ℝ),
      NumStability.fl_backSub_steps (p41AsFPModel fp) n U b k hk x =
        p41BackSubSteps fp n U b k hk x := by
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      simp only [NumStability.fl_backSub_steps, p41BackSubSteps]
      exact ih _ _

private lemma p41AsFPModel_back (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    NumStability.fl_backSub (p41AsFPModel fp) n U b =
      p41BackSub fp n U b := by
  unfold NumStability.fl_backSub p41BackSub
  exact p41AsFPModel_back_steps fp n U b n _ _

private lemma p41AsFPModel_matvec (fp : P41FPModel) (n : ℕ)
    (A : P41Matrix n n) (x : Fin n → ℝ) :
    NumStability.fl_matVec (p41AsFPModel fp) n n A x =
      p41RoundedMatVec fp n A x := rfl

private lemma p41AsFPModel_certificate (fp : P41FPModel) (n : ℕ)
    (A L U : P41Matrix n n) (h : P41LUCertificate fp n A L U) :
    NumStability.LUBackwardError n A L U
      (NumStability.gamma (p41AsFPModel fp) n) := by
  refine ⟨h.L_diag, h.L_upper_zero, h.U_lower_zero, ?_⟩
  simpa only [p41AsFPModel_gamma] using h.backward_bound

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
  have hgamma : NumStability.gammaValid (p41AsFPModel fp) n :=
    p41AsFPModel_valid fp n hvalid
  have hLs' := p41AsFPModel_certificate fp n Ase Ls Us hLs
  have hLn' := p41AsFPModel_certificate fp n Anw Ln Un hLn
  obtain ⟨Ds, hDsBound, hDsEq⟩ :=
    NumStability.lu_solve_backward_error (p41AsFPModel fp) n
      Ase Ls Us uvec (by intro i; rw [hLs.L_diag]; exact one_ne_zero)
      hUsdiag hLs' hgamma
  obtain ⟨Dn, hDnBound, hDnEq⟩ :=
    NumStability.lu_solve_backward_error (p41AsFPModel fp) n
      Anw Ln Un w (by intro i; rw [hLn.L_diag]; exact one_ne_zero)
      hUndiag hLn' hgamma
  let dw : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Ane i j * gs j
  have hDwBound : ∀ i, |dw i| ≤ p41Gamma fp.u n *
      ∑ j : Fin n, |Ane i j| * |gs j| := by
    intro i
    simpa only [dw, p41AsFPModel_gamma, p41AsFPModel_matvec] using
      (NumStability.matVec_error_bound (p41AsFPModel fp) n n Ane gs hgamma i)
  refine ⟨Ds, Dn, dw, ?_, ?_, hDwBound, ?_⟩
  · intro i j
    simpa only [p41AsFPModel_gamma] using hDsBound i j
  · intro i j
    simpa only [p41AsFPModel_gamma] using hDnBound i j
  · intro i
    constructor
    · have hs := hDsEq i
      simp only [p41AsFPModel_forward, p41AsFPModel_back] at hs
      change (∑ j : Fin n, (Ase i j + Ds i j) * gs j) = uvec i at hs
      simp_rw [add_mul] at hs
      rw [Finset.sum_add_distrib] at hs
      linarith
    · have hn := hDnEq i
      simp only [p41AsFPModel_forward, p41AsFPModel_back] at hn
      change (∑ j : Fin n, (Anw i j + Dn i j) * gn j) = w i at hn
      simp_rw [add_mul] at hn
      rw [Finset.sum_add_distrib] at hn
      change (∑ j : Fin n, Anw i j * gn j) -
        (∑ j : Fin n, Ane i j * gs j) =
          (w i - ∑ j : Fin n, Ane i j * gs j) -
            (∑ j : Fin n, Dn i j * gn j)
      linarith

end VSCLReuse

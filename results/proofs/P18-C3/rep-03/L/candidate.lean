import VSCLReuse.P18.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

open scoped BigOperators


private lemma p18MatMul_eq_mul {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18MatMul A B = A * B := by
  ext i j
  rfl

private lemma p18EntryNorm_nonneg {m n : ℕ} (A : P18Matrix m n) :
    0 ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

private lemma p18EntryNorm_add_le {m n : ℕ} (A B : P18Matrix m n) :
    p18EntryNorm (A + B) ≤ p18EntryNorm A + p18EntryNorm B := by
  simp only [p18EntryNorm, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact abs_add_le _ _

private lemma p18EntryNorm_mul_le {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18EntryNorm (A * B) ≤ p18EntryNorm A * p18EntryNorm B := by
  have hrow (k : Fin n) :
      (∑ j : Fin p, |B k j|) ≤ p18EntryNorm B := by
    unfold p18EntryNorm
    exact Finset.single_le_sum (s := Finset.univ) (a := k)
      (f := fun i : Fin n => ∑ j : Fin p, |B i j|)
      (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      (Finset.mem_univ k)
  calc
    p18EntryNorm (A * B) = ∑ i : Fin m, ∑ j : Fin p,
        |∑ k : Fin n, A i k * B k j| := by
      simp [p18EntryNorm, Matrix.mul_apply]
    _ ≤ ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n,
        |A i k| * |B k j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun k : Fin n => A i k * B k j) Finset.univ)
    _ = ∑ i : Fin m, ∑ k : Fin n,
        |A i k| * (∑ j : Fin p, |B k j|) := by
      congr 1
      funext i
      rw [Finset.sum_comm]
      congr 1
      funext k
      rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin m, ∑ k : Fin n,
        |A i k| * p18EntryNorm B := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _)
    _ = p18EntryNorm A * p18EntryNorm B := by
      simp only [p18EntryNorm, ← Finset.sum_mul]

private lemma p18EntryNorm_pointwise {m n : ℕ}
    (A B : P18Matrix m n) (c : ℝ)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p18EntryNorm A ≤ c * p18EntryNorm B := by
  simp only [p18EntryNorm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact h i j

private lemma p18MatVec_mul {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p)
    (x : Fin p → ℝ) (i : Fin m) :
    (∑ j : Fin p, (A * B) i j * x j) =
      ∑ k : Fin n, A i k * (∑ j : Fin p, B k j * x j) := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p18CombinedBackwardError_eq {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      ΔL * (D + ΔD) * (p18Transpose L + ΔU) +
      L * ΔD * (p18Transpose L + ΔU) + L * D * ΔU := by
  simp only [p18CombinedBackwardError, p18PerturbedLDLT, p18LDLT,
    p18MatMul_eq_mul]
  noncomm_ring

private lemma p18EntryNorm_combined_le {n : ℕ}
    (fp : P18FPModel) (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (hvalid : P18GammaValid fp.u n) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18SolveBackwardFactor fp n eta L D := by
  let T := p18Transpose L
  let g := p18Gamma fp.u n
  have hg : 0 ≤ g := by
    dsimp [g, p18Gamma, P18GammaValid] at *
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    · linarith
  have hnL : 0 ≤ p18EntryNorm L := p18EntryNorm_nonneg L
  have hnD : 0 ≤ p18EntryNorm D := p18EntryNorm_nonneg D
  have hnT : 0 ≤ p18EntryNorm T := p18EntryNorm_nonneg T
  have hnDp : 0 ≤ p18EntryNorm (D + ΔD) := p18EntryNorm_nonneg _
  have hnUp : 0 ≤ p18EntryNorm (T + ΔU) := p18EntryNorm_nonneg _
  have hLn : p18EntryNorm ΔL ≤ g * p18EntryNorm L :=
    p18EntryNorm_pointwise ΔL L g hL
  have hUn : p18EntryNorm ΔU ≤ g * p18EntryNorm T :=
    p18EntryNorm_pointwise ΔU T g hU
  have hDp : p18EntryNorm (D + ΔD) ≤
      (1 + eta) * p18EntryNorm D := by
    calc
      p18EntryNorm (D + ΔD) ≤ p18EntryNorm D + p18EntryNorm ΔD :=
        p18EntryNorm_add_le D ΔD
      _ ≤ p18EntryNorm D + eta * p18EntryNorm D := by linarith
      _ = (1 + eta) * p18EntryNorm D := by ring
  have hUp : p18EntryNorm (T + ΔU) ≤
      (1 + g) * p18EntryNorm T := by
    calc
      p18EntryNorm (T + ΔU) ≤ p18EntryNorm T + p18EntryNorm ΔU :=
        p18EntryNorm_add_le T ΔU
      _ ≤ p18EntryNorm T + g * p18EntryNorm T := by linarith
      _ = (1 + g) * p18EntryNorm T := by ring
  have hbase :
      p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
        p18EntryNorm L * p18EntryNorm D * p18EntryNorm T *
          (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
    rw [p18CombinedBackwardError_eq]
    calc
      p18EntryNorm
          (ΔL * (D + ΔD) * (T + ΔU) +
           L * ΔD * (T + ΔU) + L * D * ΔU) ≤
        p18EntryNorm (ΔL * (D + ΔD) * (T + ΔU)) +
        p18EntryNorm (L * ΔD * (T + ΔU)) +
        p18EntryNorm (L * D * ΔU) := by
          have h₁ := p18EntryNorm_add_le
            (ΔL * (D + ΔD) * (T + ΔU) + L * ΔD * (T + ΔU))
            (L * D * ΔU)
          have h₂ := p18EntryNorm_add_le
            (ΔL * (D + ΔD) * (T + ΔU)) (L * ΔD * (T + ΔU))
          linarith
      _ ≤ (p18EntryNorm ΔL * p18EntryNorm (D + ΔD) *
              p18EntryNorm (T + ΔU)) +
            (p18EntryNorm L * p18EntryNorm ΔD *
              p18EntryNorm (T + ΔU)) +
            p18EntryNorm L * p18EntryNorm D * p18EntryNorm ΔU := by
          have h₁ := p18EntryNorm_mul_le (ΔL * (D + ΔD)) (T + ΔU)
          have h₂ := p18EntryNorm_mul_le ΔL (D + ΔD)
          have h₃ := p18EntryNorm_mul_le (L * ΔD) (T + ΔU)
          have h₄ := p18EntryNorm_mul_le L ΔD
          have h₅ := p18EntryNorm_mul_le (L * D) ΔU
          have h₆ := p18EntryNorm_mul_le L D
          have hnon₁ := p18EntryNorm_nonneg (T + ΔU)
          have hnon₂ := p18EntryNorm_nonneg ΔU
          nlinarith
      _ ≤ (g * p18EntryNorm L) * ((1 + eta) * p18EntryNorm D) *
              ((1 + g) * p18EntryNorm T) +
            p18EntryNorm L * (eta * p18EntryNorm D) *
              ((1 + g) * p18EntryNorm T) +
            p18EntryNorm L * p18EntryNorm D * (g * p18EntryNorm T) := by
          gcongr
      _ = p18EntryNorm L * p18EntryNorm D * p18EntryNorm T *
            (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by ring
  by_cases hn : n = 0
  · subst n
    simp [p18SolveBackwardFactor, p18EntryNorm] at *
  · have hn1 : 1 ≤ (n : ℝ) ^ 6 := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact one_le_pow₀ (by exact_mod_cast this)
    have hfactor_nonneg :
        0 ≤ p18EntryNorm L * p18EntryNorm D * p18EntryNorm T *
          (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
      positivity
    unfold p18SolveBackwardFactor
    dsimp [T, g] at *
    nlinarith

private noncomputable def p18AsFPModel (fp : P18FPModel) : NumStability.FPModel where
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

private lemma p18ForwardSub_eq_library (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) :
    p18ForwardSub fp n L b =
      NumStability.fl_forwardSub (p18AsFPModel fp) n L b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p18ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p18AsFPModel fp) n L b k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
      intro hk x
      unfold p18ForwardSubSteps NumStability.fl_forwardSub_steps
      exact ih _ _
  exact hsteps n (le_refl n) _

private lemma p18BackSub_eq_library (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) :
    p18BackSub fp n U b =
      NumStability.fl_backSub (p18AsFPModel fp) n U b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p18BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p18AsFPModel fp) n U b k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
      intro hk x
      unfold p18BackSubSteps NumStability.fl_backSub_steps
      exact ih _ _
  exact hsteps n (le_refl n) _

/-- P18-C3: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p18_c3_ldlt_solve_backward_stability
    (fp : P18FPModel) (n : ℕ) (A L D E0 : P18Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p18LDLT L D = A + E0)
    (hE0 : p18EntryNorm E0 ≤ factorEta * p18EntryNorm A)
    (hDsolve : P18BlockSolveStable n D
      (p18ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P18Matrix n n),
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      p18EntryNorm ΔD ≤ eta * p18EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p18Gamma fp.u n * |p18Transpose L i j|) ∧
      F = p18TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p18BackSub fp n (p18Transpose L) z j = b i) ∧
      p18EntryNorm F ≤
        p18TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P18-C3-H001
  let fpl := p18AsFPModel fp
  have hvalid' : NumStability.gammaValid fpl n := hvalid
  obtain ⟨ΔL, hΔL, hLsolve⟩ :=
    NumStability.forwardSub_backward_error fpl n L b hdiag hlower hvalid'
  change P18Matrix n n at ΔL
  have hΔL' : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j| := by
    simpa only [fpl, p18AsFPModel, NumStability.gamma, p18Gamma] using hΔL
  rw [← p18ForwardSub_eq_library fp n L b] at hLsolve
  obtain ⟨ΔD, hΔD, hDsolve'⟩ := hDsolve
  let T := p18Transpose L
  have hTdiag : ∀ i, T i i ≠ 0 := by
    intro i
    exact hdiag i
  have hTupper : ∀ i j : Fin n, j.val < i.val → T i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔU, hUsolve⟩ :=
    NumStability.backSub_backward_error fpl n T z hTdiag hTupper hvalid'
  change P18Matrix n n at ΔU
  have hΔU' : ∀ i j, |ΔU i j| ≤ p18Gamma fp.u n * |T i j| := by
    simpa only [fpl, p18AsFPModel, NumStability.gamma, p18Gamma] using hΔU
  rw [← p18BackSub_eq_library fp n T z] at hUsolve
  let x := p18BackSub fp n T z
  have hprod : ∀ i,
      (∑ j : Fin n, ((L + ΔL) * (D + ΔD) * (T + ΔU)) i j * x j) = b i := by
    intro i
    rw [p18MatVec_mul]
    calc
      (∑ k : Fin n, ((L + ΔL) * (D + ΔD)) i k *
          (∑ j : Fin n, (T + ΔU) k j * x j)) =
        ∑ k : Fin n, ((L + ΔL) * (D + ΔD)) i k * z k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hUsolve k]
          rfl
      _ = ∑ k : Fin n, (L + ΔL) i k *
          (∑ j : Fin n, (D + ΔD) k j * z j) :=
            p18MatVec_mul (L + ΔL) (D + ΔD) z i
      _ = ∑ k : Fin n, (L + ΔL) i k * p18ForwardSub fp n L b k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [← hDsolve' k]
          rfl
      _ = b i := by
          simpa only [Matrix.add_apply] using hLsolve i
  have hAplus : A + p18TotalBackwardError E0 L D ΔL ΔD ΔU =
      (L + ΔL) * (D + ΔD) * (T + ΔU) := by
    calc
      A + p18TotalBackwardError E0 L D ΔL ΔD ΔU =
          (A + E0) +
            (p18PerturbedLDLT L D ΔL ΔD ΔU - p18LDLT L D) := by
              simp only [p18TotalBackwardError, p18CombinedBackwardError]
              abel
      _ = p18LDLT L D +
            (p18PerturbedLDLT L D ΔL ΔD ΔU - p18LDLT L D) := by
              rw [hfactor]
      _ = p18PerturbedLDLT L D ΔL ΔD ΔU := by abel
      _ = (L + ΔL) * (D + ΔD) * (T + ΔU) := by
            simp only [p18PerturbedLDLT, p18MatMul_eq_mul]
            rfl
  refine ⟨ΔL, ΔD, ΔU, p18TotalBackwardError E0 L D ΔL ΔD ΔU,
    hΔL', hΔD, ?_, rfl, ?_, ?_⟩
  · exact hΔU'
  · intro i
    have hi := hprod i
    rw [← hAplus] at hi
    exact hi
  · unfold p18TotalBackwardBound p18TotalBackwardError
    calc
      p18EntryNorm (E0 + p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p18EntryNorm E0 +
            p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) :=
            p18EntryNorm_add_le _ _
      _ ≤ factorEta * p18EntryNorm A + p18SolveBackwardFactor fp n eta L D := by
            apply add_le_add hE0
            exact p18EntryNorm_combined_le fp eta L D ΔL ΔD ΔU
              hvalid heta hΔL' hΔD hΔU'

end VSCLReuse

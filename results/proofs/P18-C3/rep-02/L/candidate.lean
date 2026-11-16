import VSCLReuse.P18.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

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

private lemma p18ForwardSub_eq (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) :
    p18ForwardSub fp n L b =
      NumStability.fl_forwardSub (p18AsFPModel fp) n L b := by
  have hsteps : ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
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

private lemma p18BackSub_eq (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) :
    p18BackSub fp n U b =
      NumStability.fl_backSub (p18AsFPModel fp) n U b := by
  have hsteps : ∀ k (hk : k ≤ n) (x : Fin n → ℝ),
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

private lemma p18Gamma_eq (fp : P18FPModel) (n : ℕ) :
    p18Gamma fp.u n = NumStability.gamma (p18AsFPModel fp) n := by
  rfl

private lemma p18Gamma_nonneg (fp : P18FPModel) (n : ℕ)
    (hvalid : P18GammaValid fp.u n) : 0 ≤ p18Gamma fp.u n := by
  rw [p18Gamma_eq]
  exact NumStability.gamma_nonneg (p18AsFPModel fp) hvalid

private lemma p18EntryNorm_nonneg {m n : ℕ} (A : P18Matrix m n) :
    0 ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

private lemma p18EntryNorm_add_le {m n : ℕ}
    (A B : P18Matrix m n) :
    p18EntryNorm (A + B) ≤ p18EntryNorm A + p18EntryNorm B := by
  calc
    p18EntryNorm (A + B)
        ≤ ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
          unfold p18EntryNorm
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simpa only [Matrix.add_apply] using abs_add_le (A i j) (B i j)
    _ = p18EntryNorm A + p18EntryNorm B := by
          simp only [Finset.sum_add_distrib, p18EntryNorm]

private lemma p18EntryNorm_sub_le {m n : ℕ}
    (A B : P18Matrix m n) :
    p18EntryNorm (A - B) ≤ p18EntryNorm A + p18EntryNorm B := by
  calc
    p18EntryNorm (A - B)
        ≤ ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
          unfold p18EntryNorm
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simpa only [Matrix.sub_apply, sub_eq_add_neg, abs_neg] using
            abs_add_le (A i j) (-B i j)
    _ = p18EntryNorm A + p18EntryNorm B := by
          simp only [Finset.sum_add_distrib, p18EntryNorm]

private lemma p18EntryNorm_mul_le {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18EntryNorm (p18MatMul A B) ≤ p18EntryNorm A * p18EntryNorm B := by
  have hcol (k : Fin n) : (∑ i : Fin m, |A i k|) ≤ p18EntryNorm A := by
    unfold p18EntryNorm
    rw [Finset.sum_comm]
    exact Finset.single_le_sum
      (f := fun j : Fin n => ∑ i : Fin m, |A i j|)
      (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg _)) (Finset.mem_univ k)
  have hrow (k : Fin n) : (∑ j : Fin p, |B k j|) ≤ p18EntryNorm B := by
    unfold p18EntryNorm
    exact Finset.single_le_sum
      (f := fun i : Fin n => ∑ j : Fin p, |B i j|)
      (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ k)
  calc
    p18EntryNorm (p18MatMul A B)
        ≤ ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j| := by
          unfold p18EntryNorm p18MatMul
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          calc
            |∑ k : Fin n, A i k * B k j|
                ≤ ∑ k : Fin n, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
            _ = ∑ k : Fin n, |A i k| * |B k j| := by simp only [abs_mul]
    _ = ∑ k : Fin n, (∑ i : Fin m, |A i k|) * (∑ j : Fin p, |B k j|) := by
          calc
            (∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j|)
                = ∑ i : Fin m, ∑ k : Fin n, ∑ j : Fin p, |A i k| * |B k j| := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [Finset.sum_comm]
            _ = ∑ k : Fin n, ∑ i : Fin m, ∑ j : Fin p, |A i k| * |B k j| := by
                  rw [Finset.sum_comm]
            _ = _ := by
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
    _ ≤ ∑ k : Fin n, (∑ i : Fin m, |A i k|) * p18EntryNorm B := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hrow k)
            (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    _ = p18EntryNorm A * p18EntryNorm B := by
          rw [← Finset.sum_mul]
          congr 1
          unfold p18EntryNorm
          rw [Finset.sum_comm]

private lemma p18EntryNorm_le_of_entrywise {m n : ℕ}
    (A B : P18Matrix m n) (c : ℝ) (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p18EntryNorm A ≤ c * p18EntryNorm B := by
  unfold p18EntryNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => h i j)

private lemma p18MatMul_eq {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) : p18MatMul A B = A * B := by
  ext i j
  rfl

private lemma p18EntryNorm_mul3_le {m n p q : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) (C : P18Matrix p q) :
    p18EntryNorm (p18MatMul (p18MatMul A B) C) ≤
      p18EntryNorm A * p18EntryNorm B * p18EntryNorm C := by
  calc
    p18EntryNorm (p18MatMul (p18MatMul A B) C)
        ≤ p18EntryNorm (p18MatMul A B) * p18EntryNorm C :=
          p18EntryNorm_mul_le _ _
    _ ≤ (p18EntryNorm A * p18EntryNorm B) * p18EntryNorm C :=
          mul_le_mul_of_nonneg_right (p18EntryNorm_mul_le A B)
            (p18EntryNorm_nonneg C)

private lemma p18CombinedBackwardError_decomp {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L D) ΔU := by
  simp only [p18CombinedBackwardError, p18PerturbedLDLT, p18LDLT,
    p18MatMul_eq]
  noncomm_ring

private lemma p18CombinedBackwardError_norm_le {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) (g eta : ℝ)
    (hg : 0 ≤ g) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ g * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤ g * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18EntryNorm L * p18EntryNorm D *
        p18EntryNorm (p18Transpose L) *
        (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
  let T := p18Transpose L
  have hLn : p18EntryNorm ΔL ≤ g * p18EntryNorm L :=
    p18EntryNorm_le_of_entrywise ΔL L g hL
  have hUn : p18EntryNorm ΔU ≤ g * p18EntryNorm T :=
    p18EntryNorm_le_of_entrywise ΔU T g hU
  have hL0 : 0 ≤ p18EntryNorm L := p18EntryNorm_nonneg L
  have hD0 : 0 ≤ p18EntryNorm D := p18EntryNorm_nonneg D
  have hT0 : 0 ≤ p18EntryNorm T := p18EntryNorm_nonneg T
  have hDplus0 : 0 ≤ p18EntryNorm (D + ΔD) := p18EntryNorm_nonneg _
  have hTplus0 : 0 ≤ p18EntryNorm (T + ΔU) := p18EntryNorm_nonneg _
  have hLp : p18EntryNorm (L + ΔL) ≤ (1 + g) * p18EntryNorm L := by
    calc
      p18EntryNorm (L + ΔL) ≤ p18EntryNorm L + p18EntryNorm ΔL :=
        p18EntryNorm_add_le _ _
      _ ≤ p18EntryNorm L + g * p18EntryNorm L := by gcongr
      _ = (1 + g) * p18EntryNorm L := by ring
  have hDp : p18EntryNorm (D + ΔD) ≤ (1 + eta) * p18EntryNorm D := by
    calc
      p18EntryNorm (D + ΔD) ≤ p18EntryNorm D + p18EntryNorm ΔD :=
        p18EntryNorm_add_le _ _
      _ ≤ p18EntryNorm D + eta * p18EntryNorm D := by gcongr
      _ = (1 + eta) * p18EntryNorm D := by ring
  have hUp : p18EntryNorm (T + ΔU) ≤ (1 + g) * p18EntryNorm T := by
    calc
      p18EntryNorm (T + ΔU) ≤ p18EntryNorm T + p18EntryNorm ΔU :=
        p18EntryNorm_add_le _ _
      _ ≤ p18EntryNorm T + g * p18EntryNorm T := by gcongr
      _ = (1 + g) * p18EntryNorm T := by ring
  have h1 : p18EntryNorm
      (p18MatMul (p18MatMul ΔL (D + ΔD)) (T + ΔU)) ≤
      (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) *
        (g * (1 + eta) * (1 + g)) := by
    calc
      _ ≤ p18EntryNorm ΔL * p18EntryNorm (D + ΔD) *
          p18EntryNorm (T + ΔU) := p18EntryNorm_mul3_le _ _ _
      _ ≤ (g * p18EntryNorm L) * ((1 + eta) * p18EntryNorm D) *
          ((1 + g) * p18EntryNorm T) := by gcongr
      _ = _ := by ring
  have h2 : p18EntryNorm
      (p18MatMul (p18MatMul L ΔD) (T + ΔU)) ≤
      (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) *
        (eta * (1 + g)) := by
    calc
      _ ≤ p18EntryNorm L * p18EntryNorm ΔD *
          p18EntryNorm (T + ΔU) := p18EntryNorm_mul3_le _ _ _
      _ ≤ p18EntryNorm L * (eta * p18EntryNorm D) *
          ((1 + g) * p18EntryNorm T) := by gcongr
      _ = _ := by ring
  have h3 : p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) ≤
      (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) * g := by
    calc
      _ ≤ p18EntryNorm L * p18EntryNorm D * p18EntryNorm ΔU :=
          p18EntryNorm_mul3_le _ _ _
      _ ≤ p18EntryNorm L * p18EntryNorm D * (g * p18EntryNorm T) := by
          gcongr
      _ = _ := by ring
  rw [p18CombinedBackwardError_decomp]
  calc
    p18EntryNorm
      (p18MatMul (p18MatMul ΔL (D + ΔD)) (T + ΔU) +
        p18MatMul (p18MatMul L ΔD) (T + ΔU) +
        p18MatMul (p18MatMul L D) ΔU)
        ≤ p18EntryNorm (p18MatMul (p18MatMul ΔL (D + ΔD)) (T + ΔU)) +
          p18EntryNorm (p18MatMul (p18MatMul L ΔD) (T + ΔU)) +
          p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) := by
            grw [p18EntryNorm_add_le, p18EntryNorm_add_le]
    _ ≤ (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) *
          (g * (1 + eta) * (1 + g)) +
        (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) *
          (eta * (1 + g)) +
        (p18EntryNorm L * p18EntryNorm D * p18EntryNorm T) * g := by
          gcongr
    _ = _ := by ring

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
  let fp' := p18AsFPModel fp
  have hvalid' : NumStability.gammaValid fp' n := hvalid
  obtain ⟨ΔL, hLbound, hLsolve⟩ :=
    NumStability.forwardSub_backward_error fp' n L b hdiag hlower hvalid'
  change P18Matrix n n at ΔL
  have hLbound' : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j| := by
    simpa only [p18Gamma_eq] using hLbound
  rw [← p18ForwardSub_eq] at hLsolve
  obtain ⟨ΔD, hDbound, hDsolve'⟩ := hDsolve
  have hdiagT : ∀ i, p18Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hupperT : ∀ i j : Fin n, j.val < i.val → p18Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hUbound, hUsolve⟩ :=
    NumStability.backSub_backward_error fp' n (p18Transpose L) z
      hdiagT hupperT hvalid'
  change P18Matrix n n at ΔU
  have hUbound' : ∀ i j,
      |ΔU i j| ≤ p18Gamma fp.u n * |p18Transpose L i j| := by
    simpa only [p18Gamma_eq] using hUbound
  rw [← p18BackSub_eq] at hUsolve
  let y := p18ForwardSub fp n L b
  let x := p18BackSub fp n (p18Transpose L) z
  have hfront : (L + ΔL).mulVec y = b := by
    funext i
    change (∑ j : Fin n, (L i j + ΔL i j) * y j) = b i
    exact hLsolve i
  have hblock : (D + ΔD).mulVec z = y := by
    funext i
    change (∑ j : Fin n, (D i j + ΔD i j) * z j) = y i
    exact hDsolve' i
  have hback : (p18Transpose L + ΔU).mulVec x = z := by
    funext i
    change (∑ j : Fin n, (p18Transpose L i j + ΔU i j) * x j) = z i
    exact hUsolve i
  have hcombined :
      ((L + ΔL) * (D + ΔD) * (p18Transpose L + ΔU)).mulVec x = b := by
    calc
      ((L + ΔL) * (D + ΔD) * (p18Transpose L + ΔU)).mulVec x
          = ((L + ΔL) * (D + ΔD)).mulVec
              ((p18Transpose L + ΔU).mulVec x) :=
                (Matrix.mulVec_mulVec x _ _).symm
      _ = ((L + ΔL) * (D + ΔD)).mulVec z := by rw [hback]
      _ = (L + ΔL).mulVec ((D + ΔD).mulVec z) :=
            (Matrix.mulVec_mulVec z _ _).symm
      _ = (L + ΔL).mulVec y := by rw [hblock]
      _ = b := hfront
  let F := p18TotalBackwardError E0 L D ΔL ΔD ΔU
  have hmatrix : A + F = p18PerturbedLDLT L D ΔL ΔD ΔU := by
    change A + (E0 +
      (p18PerturbedLDLT L D ΔL ΔD ΔU - p18LDLT L D)) = _
    rw [hfactor]
    abel
  have hcombo' : (A + F).mulVec x = b := by
    rw [hmatrix]
    simpa only [p18PerturbedLDLT, p18MatMul_eq] using hcombined
  have heq : ∀ i, ∑ j : Fin n, (A i j + F i j) * x j = b i := by
    intro i
    have hi := congrArg (fun v : Fin n → ℝ => v i) hcombo'
    exact hi
  let P := p18EntryNorm L * p18EntryNorm D *
    p18EntryNorm (p18Transpose L)
  let Q := p18Gamma fp.u n * (1 + eta) * (1 + p18Gamma fp.u n) +
    eta * (1 + p18Gamma fp.u n) + p18Gamma fp.u n
  have hg : 0 ≤ p18Gamma fp.u n := p18Gamma_nonneg fp n hvalid
  have hP : 0 ≤ P := by
    dsimp [P]
    have hL0 := p18EntryNorm_nonneg L
    have hD0 := p18EntryNorm_nonneg D
    have hT0 := p18EntryNorm_nonneg (p18Transpose L)
    positivity
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hscale : P * Q ≤ (n : ℝ) ^ 6 * P * Q := by
    by_cases hn : n = 0
    · subst n
      simp [P, p18EntryNorm]
    · have hnNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnNat
      have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hn1
      have hPQ : 0 ≤ P * Q := mul_nonneg hP hQ
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hn6 hPQ
  have hcombinedNorm :
      p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤ P * Q := by
    exact p18CombinedBackwardError_norm_le L D ΔL ΔD ΔU
      (p18Gamma fp.u n) eta hg heta hLbound' hDbound hUbound'
  have hFnorm : p18EntryNorm F ≤
      p18TotalBackwardBound fp n eta factorEta A L D := by
    calc
      p18EntryNorm F
          ≤ p18EntryNorm E0 +
              p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) :=
                p18EntryNorm_add_le _ _
      _ ≤ factorEta * p18EntryNorm A + P * Q :=
            add_le_add hE0 hcombinedNorm
      _ ≤ factorEta * p18EntryNorm A + (n : ℝ) ^ 6 * P * Q :=
            (by simpa [add_comm] using
              (add_le_add_right hscale (factorEta * p18EntryNorm A)))
      _ = p18TotalBackwardBound fp n eta factorEta A L D := by
            dsimp [p18TotalBackwardBound, p18SolveBackwardFactor, P, Q]
            ring
  exact ⟨ΔL, ΔD, ΔU, F, hLbound', hDbound, hUbound', rfl, heq, hFnorm⟩

end VSCLReuse

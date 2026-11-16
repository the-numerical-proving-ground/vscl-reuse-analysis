import VSCLReuse.P18.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

open scoped Matrix

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
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private lemma p18_forward_steps_as_library (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    p18ForwardSubSteps fp n L b k hk x =
      NumStability.fl_forwardSub_steps (p18AsFPModel fp) n L b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [p18ForwardSubSteps, NumStability.fl_forwardSub_steps]
      exact ih _ _

private lemma p18_forward_as_library (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) :
    p18ForwardSub fp n L b =
      NumStability.fl_forwardSub (p18AsFPModel fp) n L b := by
  exact p18_forward_steps_as_library fp n L b n (le_refl n) _

private lemma p18_back_steps_as_library (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    p18BackSubSteps fp n U b k hk x =
      NumStability.fl_backSub_steps (p18AsFPModel fp) n U b k hk x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      simp only [p18BackSubSteps, NumStability.fl_backSub_steps]
      exact ih _ _

private lemma p18_back_as_library (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) :
    p18BackSub fp n U b =
      NumStability.fl_backSub (p18AsFPModel fp) n U b := by
  exact p18_back_steps_as_library fp n U b n (le_refl n) _

private lemma p18_norm_nonneg {m n : ℕ} (A : P18Matrix m n) :
    0 ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  positivity

private lemma p18_norm_add_le {m n : ℕ} (A B : P18Matrix m n) :
    p18EntryNorm (A + B) ≤ p18EntryNorm A + p18EntryNorm B := by
  simp only [p18EntryNorm, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact abs_add_le _ _

private lemma p18_norm_sub_le {m n : ℕ} (A B : P18Matrix m n) :
    p18EntryNorm (A - B) ≤ p18EntryNorm A + p18EntryNorm B := by
  simp only [p18EntryNorm, Matrix.sub_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact abs_sub _ _

private lemma p18_norm_zero {m n : ℕ} :
    p18EntryNorm (0 : P18Matrix m n) = 0 := by
  simp [p18EntryNorm]

private lemma p18_norm_le_of_entry {m n : ℕ} (A B : P18Matrix m n)
    (h : ∀ i j, |A i j| ≤ |B i j|) :
    p18EntryNorm A ≤ p18EntryNorm B := by
  unfold p18EntryNorm
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))

private lemma p18_norm_entry_bound {m n : ℕ} (A B : P18Matrix m n)
    (c : ℝ) (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p18EntryNorm A ≤ c * p18EntryNorm B := by
  unfold p18EntryNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => h i j)

private lemma p18_norm_mul_le {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18EntryNorm (p18MatMul A B) ≤ p18EntryNorm A * p18EntryNorm B := by
  have hrow : ∀ k : Fin n, (∑ j : Fin p, |B k j|) ≤ p18EntryNorm B := by
    intro k
    unfold p18EntryNorm
    exact Finset.single_le_sum
      (fun i _ => (Finset.sum_nonneg (fun j _ =>
        show 0 ≤ |B i j| from abs_nonneg _)))
      (Finset.mem_univ k)
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
            _ = ∑ k : Fin n, |A i k| * |B k j| := by simp_rw [abs_mul]
    _ = ∑ i : Fin m, ∑ k : Fin n, |A i k| * (∑ j : Fin p, |B k j|) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin m, ∑ k : Fin n, |A i k| * p18EntryNorm B := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _)
    _ = p18EntryNorm A * p18EntryNorm B := by
          simp only [p18EntryNorm, Finset.sum_mul]

private lemma p18_matmul_eq {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18MatMul A B = A * B := by
  rfl

private lemma p18_perturb_identity {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L D) ΔU := by
  simp only [p18CombinedBackwardError, p18PerturbedLDLT, p18LDLT,
    p18_matmul_eq]
  noncomm_ring

private lemma p18_combined_norm_bound (fp : P18FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (heta : 0 ≤ eta)
    (hvalid : P18GammaValid fp.u n)
    (hL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤ p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18EntryNorm L * p18EntryNorm D * p18EntryNorm (p18Transpose L) *
        (p18Gamma fp.u n * (1 + eta) * (1 + p18Gamma fp.u n) +
          eta * (1 + p18Gamma fp.u n) + p18Gamma fp.u n) := by
  let c := p18Gamma fp.u n
  let l := p18EntryNorm L
  let d := p18EntryNorm D
  let u := p18EntryNorm (p18Transpose L)
  have hc : 0 ≤ c := by
    dsimp [c, p18Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
      (sub_nonneg.mpr (le_of_lt hvalid))
  have hl : 0 ≤ l := p18_norm_nonneg L
  have hd : 0 ≤ d := p18_norm_nonneg D
  have hu : 0 ≤ u := p18_norm_nonneg (p18Transpose L)
  have hΔL : p18EntryNorm ΔL ≤ c * l := p18_norm_entry_bound _ _ _ hL
  have hΔU : p18EntryNorm ΔU ≤ c * u := p18_norm_entry_bound _ _ _ hU
  have hDp : p18EntryNorm (D + ΔD) ≤ (1 + eta) * d := by
    calc
      _ ≤ d + p18EntryNorm ΔD := p18_norm_add_le _ _
      _ ≤ (1 + eta) * d := by nlinarith [hD]
  have hUp : p18EntryNorm (p18Transpose L + ΔU) ≤ (1 + c) * u := by
    calc
      _ ≤ u + p18EntryNorm ΔU := p18_norm_add_le _ _
      _ ≤ (1 + c) * u := by nlinarith [hΔU]
  have hdp0 : 0 ≤ (1 + eta) * d := mul_nonneg (by linarith) hd
  have hup0 : 0 ≤ (1 + c) * u := mul_nonneg (by linarith) hu
  have hcu0 : 0 ≤ c * u := mul_nonneg hc hu
  have hndp : 0 ≤ p18EntryNorm (D + ΔD) := p18_norm_nonneg _
  have hnup : 0 ≤ p18EntryNorm (p18Transpose L + ΔU) := p18_norm_nonneg _
  have hnΔL : 0 ≤ p18EntryNorm ΔL := p18_norm_nonneg _
  have hnΔD : 0 ≤ p18EntryNorm ΔD := p18_norm_nonneg _
  have hnΔU : 0 ≤ p18EntryNorm ΔU := p18_norm_nonneg _
  have hT1 : p18EntryNorm
      (p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU)) ≤
      (c * l * ((1 + eta) * d)) * ((1 + c) * u) := by
    calc
      _ ≤ p18EntryNorm (p18MatMul ΔL (D + ΔD)) *
            p18EntryNorm (p18Transpose L + ΔU) := p18_norm_mul_le _ _
      _ ≤ (p18EntryNorm ΔL * p18EntryNorm (D + ΔD)) *
            p18EntryNorm (p18Transpose L + ΔU) := by
              exact mul_le_mul_of_nonneg_right (p18_norm_mul_le _ _) hnup
      _ ≤ (c * l * ((1 + eta) * d)) * ((1 + c) * u) := by
            gcongr
  have hT2 : p18EntryNorm
      (p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU)) ≤
      (l * (eta * d)) * ((1 + c) * u) := by
    calc
      _ ≤ p18EntryNorm (p18MatMul L ΔD) *
            p18EntryNorm (p18Transpose L + ΔU) := p18_norm_mul_le _ _
      _ ≤ (l * p18EntryNorm ΔD) *
            p18EntryNorm (p18Transpose L + ΔU) := by
              exact mul_le_mul_of_nonneg_right (p18_norm_mul_le _ _) hnup
      _ ≤ (l * (eta * d)) * ((1 + c) * u) := by
            gcongr
  have hT3 : p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) ≤
      (l * d) * (c * u) := by
    calc
      _ ≤ p18EntryNorm (p18MatMul L D) * p18EntryNorm ΔU :=
            p18_norm_mul_le _ _
      _ ≤ (l * d) * p18EntryNorm ΔU := by
            exact mul_le_mul_of_nonneg_right (p18_norm_mul_le _ _) hnΔU
      _ ≤ (l * d) * (c * u) := by
            gcongr
  calc
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU)
        = p18EntryNorm
            (p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
             p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU) +
             p18MatMul (p18MatMul L D) ΔU) := by rw [p18_perturb_identity]
    _ ≤ p18EntryNorm (p18MatMul (p18MatMul ΔL (D + ΔD))
             (p18Transpose L + ΔU)) +
          p18EntryNorm (p18MatMul (p18MatMul L ΔD)
             (p18Transpose L + ΔU)) +
          p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) := by
            have h1 := p18_norm_add_le
              (p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
                p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU))
              (p18MatMul (p18MatMul L D) ΔU)
            have h2 := p18_norm_add_le
              (p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU))
              (p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU))
            linarith
    _ ≤ (c * l * ((1 + eta) * d)) * ((1 + c) * u) +
          (l * (eta * d)) * ((1 + c) * u) +
          (l * d) * (c * u) := by
            linarith
    _ = l * d * u * (c * (1 + eta) * (1 + c) + eta * (1 + c) + c) := by
          ring

private lemma p18_chain_equation (n : ℕ)
    (A L D E0 ΔL ΔD ΔU : P18Matrix n n)
    (b y z x : Fin n → ℝ)
    (hfactor : p18LDLT L D = A + E0)
    (hforward : ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * y j = b i)
    (hD : ∀ i, ∑ j : Fin n, (D i j + ΔD i j) * z j = y i)
    (hback : ∀ i, ∑ j : Fin n,
      (p18Transpose L i j + ΔU i j) * x j = z i) :
    ∀ i, ∑ j : Fin n,
      (A i j + p18TotalBackwardError E0 L D ΔL ΔD ΔU i j) * x j = b i := by
  have hf : A + p18TotalBackwardError E0 L D ΔL ΔD ΔU =
      p18PerturbedLDLT L D ΔL ΔD ΔU := by
    simp only [p18TotalBackwardError, p18CombinedBackwardError]
    rw [hfactor]
    abel
  have hforward' : (L + ΔL) *ᵥ y = b := by
    funext i
    exact hforward i
  have hD' : (D + ΔD) *ᵥ z = y := by
    funext i
    exact hD i
  have hback' : (p18Transpose L + ΔU) *ᵥ x = z := by
    funext i
    exact hback i
  intro i
  calc
    (∑ j : Fin n,
        (A i j + p18TotalBackwardError E0 L D ΔL ΔD ΔU i j) * x j) =
        ((A + p18TotalBackwardError E0 L D ΔL ΔD ΔU) *ᵥ x) i := by rfl
    _ = (p18PerturbedLDLT L D ΔL ΔD ΔU *ᵥ x) i := by rw [hf]
    _ = b i := by
      simp only [p18PerturbedLDLT, p18_matmul_eq]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback', hD', hforward']

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
  let q := p18AsFPModel fp
  have hqvalid : NumStability.gammaValid q n := hvalid
  obtain ⟨ΔL, hΔLraw, hforwardRaw⟩ :=
    NumStability.forwardSub_backward_error q n L b hdiag hlower hqvalid
  have hΔL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j| := by
    simpa only [q, p18AsFPModel, NumStability.gamma, p18Gamma] using hΔLraw
  have hforward : ∀ i, ∑ j : Fin n,
      (L i j + ΔL i j) * p18ForwardSub fp n L b j = b i := by
    simpa only [p18_forward_as_library] using hforwardRaw
  obtain ⟨ΔD, hΔD, hDres⟩ := hDsolve
  have hUdiag : ∀ i, p18Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → p18Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔUraw, hbackRaw⟩ :=
    NumStability.backSub_backward_error q n (p18Transpose L) z
      hUdiag hUupper hqvalid
  have hΔU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j| := by
    simpa only [q, p18AsFPModel, NumStability.gamma, p18Gamma] using hΔUraw
  have hback : ∀ i, ∑ j : Fin n,
      (p18Transpose L i j + ΔU i j) *
        p18BackSub fp n (p18Transpose L) z j = z i := by
    simpa only [p18_back_as_library] using hbackRaw
  refine ⟨ΔL, ΔD, ΔU, p18TotalBackwardError E0 L D ΔL ΔD ΔU,
    hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · exact p18_chain_equation n A L D E0 ΔL ΔD ΔU b
      (p18ForwardSub fp n L b) z
      (p18BackSub fp n (p18Transpose L) z)
      hfactor hforward hDres hback
  · have hc : 0 ≤ p18Gamma fp.u n := by
      unfold p18Gamma
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
        (sub_nonneg.mpr (le_of_lt hvalid))
    have hcombined := p18_combined_norm_bound fp n eta L D ΔL ΔD ΔU
      heta hvalid hΔL hΔD hΔU
    have hbase : p18EntryNorm (p18TotalBackwardError E0 L D ΔL ΔD ΔU) ≤
        factorEta * p18EntryNorm A +
        p18EntryNorm L * p18EntryNorm D *
          p18EntryNorm (p18Transpose L) *
          (p18Gamma fp.u n * (1 + eta) * (1 + p18Gamma fp.u n) +
            eta * (1 + p18Gamma fp.u n) + p18Gamma fp.u n) := by
      calc
        _ ≤ p18EntryNorm E0 +
              p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) := by
              exact p18_norm_add_le _ _
        _ ≤ _ := by linarith
    cases n with
    | zero =>
        simp [p18EntryNorm, p18TotalBackwardBound,
          p18SolveBackwardFactor]
    | succ k =>
        have hn1 : (1 : ℝ) ≤ (Nat.succ k : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        have hn6 : (1 : ℝ) ≤ (Nat.succ k : ℝ) ^ 6 := by
          calc
            (1 : ℝ) = (1 : ℝ) ^ 6 := by norm_num
            _ ≤ (Nat.succ k : ℝ) ^ 6 := by gcongr
        have hprod : 0 ≤ p18EntryNorm L * p18EntryNorm D *
            p18EntryNorm (p18Transpose L) *
            (p18Gamma fp.u (Nat.succ k) * (1 + eta) *
                (1 + p18Gamma fp.u (Nat.succ k)) +
              eta * (1 + p18Gamma fp.u (Nat.succ k)) +
              p18Gamma fp.u (Nat.succ k)) := by
          have hl := p18_norm_nonneg L
          have hd := p18_norm_nonneg D
          have hu := p18_norm_nonneg (p18Transpose L)
          positivity
        unfold p18TotalBackwardBound p18SolveBackwardFactor
        calc
          p18EntryNorm (p18TotalBackwardError E0 L D ΔL ΔD ΔU)
              ≤ factorEta * p18EntryNorm A +
                  p18EntryNorm L * p18EntryNorm D *
                    p18EntryNorm (p18Transpose L) *
                    (p18Gamma fp.u (Nat.succ k) * (1 + eta) *
                        (1 + p18Gamma fp.u (Nat.succ k)) +
                      eta * (1 + p18Gamma fp.u (Nat.succ k)) +
                      p18Gamma fp.u (Nat.succ k)) := hbase
          _ ≤ factorEta * p18EntryNorm A +
                (Nat.succ k : ℝ) ^ 6 * p18EntryNorm L * p18EntryNorm D *
                  p18EntryNorm (p18Transpose L) *
                  (p18Gamma fp.u (Nat.succ k) * (1 + eta) *
                      (1 + p18Gamma fp.u (Nat.succ k)) +
                    eta * (1 + p18Gamma fp.u (Nat.succ k)) +
                    p18Gamma fp.u (Nat.succ k)) := by
                    nlinarith [mul_le_mul_of_nonneg_right hn6 hprod]

end VSCLReuse

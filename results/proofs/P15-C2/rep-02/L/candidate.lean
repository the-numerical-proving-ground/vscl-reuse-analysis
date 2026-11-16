import VSCLReuse.P15.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace VSCLReuse

private noncomputable def p15AsFPModel (fp : P15FPModel) : NumStability.FPModel where
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
    · ring

private theorem p15ForwardSubSteps_eq (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p15ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p15AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
      intro hk x
      exact ih (Nat.le_of_succ_le hk) _

private theorem p15ForwardSub_eq (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    p15ForwardSub fp n L b =
      NumStability.fl_forwardSub (p15AsFPModel fp) n L b := by
  exact p15ForwardSubSteps_eq fp n L b n (le_refl n) (fun _ => 0)

private theorem p15VecNormSq_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p15VecNormSq v := by
  unfold p15VecNormSq
  exact Finset.sum_nonneg (fun j hj => sq_nonneg (v j))

private theorem p15VecNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    p15VecNorm v ^ 2 = p15VecNormSq v := by
  unfold p15VecNorm
  exact Real.sq_sqrt (p15VecNormSq_nonneg v)

private theorem p15FrobNorm_sq {m n : ℕ} (A : P15Matrix m n) :
    p15FrobNorm A ^ 2 = p15FrobNormSq A := by
  unfold p15FrobNorm
  apply Real.sq_sqrt
  unfold p15FrobNormSq
  exact Finset.sum_nonneg (fun i hi => p15VecNormSq_nonneg (A i))

private theorem p15FrobNorm_le_mul_of_rows {m n : ℕ}
    (A B : P15Matrix m n) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i : Fin m, p15VecNorm (A i) ≤ C * p15VecNorm (B i)) :
    p15FrobNorm A ≤ C * p15FrobNorm B := by
  have hsum : p15FrobNormSq A ≤ C ^ 2 * p15FrobNormSq B := by
    unfold p15FrobNormSq
    simp_rw [← p15VecNorm_sq]
    calc
      ∑ i : Fin m, p15VecNorm (A i) ^ 2 ≤
          ∑ i : Fin m, (C * p15VecNorm (B i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).2
        exact hrow i
      _ = C ^ 2 * ∑ i : Fin m, p15VecNorm (B i) ^ 2 := by
        rw [Finset.mul_sum]
        simp_rw [mul_pow]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).1
  change p15FrobNorm A ^ 2 ≤ (C * p15FrobNorm B) ^ 2
  rw [p15FrobNorm_sq A, mul_pow, p15FrobNorm_sq B]
  exact hsum

private theorem p15ScalarFactor (n : ℕ) :
    (11 / 10 : ℝ) * n * Real.sqrt n * Real.sqrt (3 * n) ≤
      2 * (n : ℝ) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h3 : (11 / 10 : ℝ) * Real.sqrt 3 ≤ 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs0 := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  calc
    (11 / 10 : ℝ) * n * Real.sqrt n * Real.sqrt (3 * n)
        = (11 / 10 : ℝ) * n * Real.sqrt n *
            (Real.sqrt 3 * Real.sqrt n) := by
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    _ = ((11 / 10 : ℝ) * Real.sqrt 3) *
          (n : ℝ) * (Real.sqrt n * Real.sqrt n) := by ring
    _ = ((11 / 10 : ℝ) * Real.sqrt 3) * (n : ℝ) ^ 2 := by
          rw [Real.mul_self_sqrt hn]
          ring
    _ ≤ 2 * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

theorem p15_c2_lemma_3_2
    (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P15RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p15FrobNorm (p15RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p15FrobNorm
        (p15Residual (p15RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P15-C2-H001
  let fp' := p15AsFPModel fp
  have hdiagL : ∀ i : Fin n, p15Transpose R i i ≠ 0 := by
    intro i
    simpa only [p15Transpose] using hdiag i
  have hlower : ∀ i j : Fin n, i.val < j.val → p15Transpose R i j = 0 := by
    intro i j hij
    exact hupper j i hij
  have hgamma : NumStability.gammaValid fp' n := hvalid
  let Q := p15RoundedQ fp X R
  let E := p15Residual Q R X
  let C : ℝ := (11 / 10 : ℝ) * n * Real.sqrt n * fp.u * xNorm
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
          (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hrow : ∀ i : Fin m,
      p15VecNorm (E i) ≤ C * p15VecNorm (Q i) := by
    intro i
    obtain ⟨δ, hδ, heq⟩ :=
      NumStability.forwardSub_backward_error fp' n (p15Transpose R) (X i)
        hdiagL hlower hgamma
    have hδ' : ∀ k j, |δ k j| ≤ p15Gamma fp.u n * |R j k| := by
      intro k j
      simpa only [p15Gamma, NumStability.gamma, p15Transpose, fp'] using hδ k j
    have heq' : ∀ k, ∑ j : Fin n,
        (p15Transpose R k j + δ k j) * Q i j = X i k := by
      intro k
      have hq : Q i = NumStability.fl_forwardSub fp' n (p15Transpose R) (X i) :=
        p15ForwardSub_eq fp n (p15Transpose R) (X i)
      simpa only [hq] using heq k
    exact hperturb i δ hδ' heq'
  have hF : p15FrobNorm E ≤ C * p15FrobNorm Q :=
    p15FrobNorm_le_mul_of_rows E Q C hC hrow
  calc
    p15FrobNorm E ≤ C * p15FrobNorm Q := hF
    _ ≤ C * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hC
    _ = ((11 / 10 : ℝ) * n * Real.sqrt n * Real.sqrt (3 * n)) *
          (fp.u * xNorm) := by
      dsimp [C]
      ring
    _ ≤ (2 * (n : ℝ) ^ 2) * (fp.u * xNorm) :=
      mul_le_mul_of_nonneg_right (p15ScalarFactor n)
        (mul_nonneg fp.u_nonneg hxNorm)
    _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring

end VSCLReuse

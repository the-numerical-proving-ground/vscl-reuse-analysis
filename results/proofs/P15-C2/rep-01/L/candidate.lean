import VSCLReuse.P15.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace VSCLReuse

open scoped BigOperators

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
    · simp

private lemma p15ForwardSubSteps_eq_library (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p15ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p15AsFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk x
    simpa only [p15ForwardSubSteps, NumStability.fl_forwardSub_steps] using
      ih (Nat.le_of_succ_le hk)
        (Function.update x ⟨n - k - 1, by omega⟩
          (fp.fl_div
            (Fin.foldl (n - k - 1)
              (fun acc (t : Fin (n - k - 1)) =>
                fp.fl_sub acc (fp.fl_mul (L ⟨n - k - 1, by omega⟩ ⟨t.val, by omega⟩)
                  (x ⟨t.val, by omega⟩)))
              (b ⟨n - k - 1, by omega⟩))
            (L ⟨n - k - 1, by omega⟩ ⟨n - k - 1, by omega⟩)))

private lemma p15ForwardSub_eq_library (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    p15ForwardSub fp n L b = NumStability.fl_forwardSub (p15AsFPModel fp) n L b := by
  exact p15ForwardSubSteps_eq_library fp n L b n (le_refl n) (fun _ => 0)

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
  let Q := p15RoundedQ fp X R
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hrow : ∀ i : Fin m, p15VecNorm (p15Residual Q R X i) ≤ c * p15VecNorm (Q i) := by
    intro i
    have hLdiag : ∀ j, p15Transpose R j j ≠ 0 := by
      intro j
      exact hdiag j
    have hLT : ∀ j k : Fin n, j.val < k.val → p15Transpose R j k = 0 := by
      intro j k hjk
      exact hupper k j hjk
    obtain ⟨deltaL, hdelta, heq⟩ :=
      NumStability.forwardSub_backward_error (p15AsFPModel fp) n
        (p15Transpose R) (X i) hLdiag hLT hvalid
    have hdelta' : ∀ k j, |deltaL k j| ≤ p15Gamma fp.u n * |R j k| := by
      intro k j
      simpa only [p15Gamma, NumStability.gamma, p15Transpose, p15AsFPModel] using
        hdelta k j
    have heq' : ∀ k, ∑ j : Fin n, (p15Transpose R k j + deltaL k j) * Q i j = X i k := by
      intro k
      simpa only [Q, p15RoundedQ, p15ForwardSub_eq_library] using heq k
    exact hperturb i deltaL hdelta' heq'
  have hvecsq : ∀ v : Fin n → ℝ, p15VecNorm v ^ 2 = p15VecNormSq v := by
    intro v
    unfold p15VecNorm p15VecNormSq
    exact Real.sq_sqrt (Finset.sum_nonneg fun j hj => sq_nonneg (v j))
  have hfrobsq : ∀ A : P15Matrix m n, p15FrobNorm A ^ 2 = p15FrobNormSq A := by
    intro A
    unfold p15FrobNorm p15FrobNormSq
    exact Real.sq_sqrt (Finset.sum_nonneg fun i hi => by
      rw [← hvecsq]
      exact sq_nonneg _)
  have hc : 0 ≤ c := by
    dsimp [c]
    have hu : 0 ≤ fp.u := fp.u_nonneg
    positivity
  have hres_sq : p15FrobNormSq (p15Residual Q R X) ≤
      c ^ 2 * p15FrobNormSq Q := by
    unfold p15FrobNormSq
    calc
      ∑ i : Fin m, p15VecNormSq (p15Residual Q R X i) =
          ∑ i : Fin m, p15VecNorm (p15Residual Q R X i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (hvecsq _).symm
      _ ≤ ∑ i : Fin m, (c * p15VecNorm (Q i)) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hc (Real.sqrt_nonneg _))).2
              (hrow i)
      _ = c ^ 2 * ∑ i : Fin m, p15VecNormSq (Q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [mul_pow, hvecsq]
  have hfrob_bound : p15FrobNorm (p15Residual Q R X) ≤ c * p15FrobNorm Q := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hc (Real.sqrt_nonneg _))).1
    calc
      p15FrobNorm (p15Residual Q R X) ^ 2 =
          p15FrobNormSq (p15Residual Q R X) := hfrobsq _
      _ ≤ c ^ 2 * p15FrobNormSq Q := hres_sq
      _ = (c * p15FrobNorm Q) ^ 2 := by
        conv_rhs => rw [mul_pow, hfrobsq]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsqrtN : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn
  have hsqrt_bound : Real.sqrt (3 * (n : ℝ)) ≤
      (20 : ℝ) / 11 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).1
    rw [Real.sq_sqrt (by positivity)]
    nlinarith
  change p15FrobNorm (p15Residual Q R X) ≤
    2 * (n : ℝ) ^ 2 * fp.u * xNorm
  calc
    p15FrobNorm (p15Residual Q R X) ≤ c * p15FrobNorm Q := hfrob_bound
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hc
    _ ≤ c * ((20 : ℝ) / 11 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt_bound hc
    _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      dsimp [c]
      calc
        (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm *
            ((20 : ℝ) / 11 * Real.sqrt n) =
          2 * (n : ℝ) * (Real.sqrt n ^ 2) * fp.u * xNorm := by ring
        _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by rw [hsqrtN]; ring

end VSCLReuse

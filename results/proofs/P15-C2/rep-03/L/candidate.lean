import VSCLReuse.P15.Definitions
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution

namespace VSCLReuse

private noncomputable def p15ToFPModel (fp : P15FPModel) : NumStability.FPModel where
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

private lemma p15Steps_eq (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p15ForwardSubSteps fp n L b k hk x =
        NumStability.fl_forwardSub_steps (p15ToFPModel fp) n L b k hk x := by
  intro k
  induction k with
  | zero => intro hk x; rfl
  | succ k ih =>
    intro hk x
    simp only [p15ForwardSubSteps, NumStability.fl_forwardSub_steps]
    apply ih

private lemma p15ForwardSub_eq (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) :
    p15ForwardSub fp n L b =
      NumStability.fl_forwardSub (p15ToFPModel fp) n L b := by
  exact p15Steps_eq fp n L b n (le_refl n) (fun _ => 0)

private lemma p15VecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p15VecNormSq x := by
  unfold p15VecNormSq
  positivity

private lemma p15VecNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    p15VecNorm x ^ 2 = p15VecNormSq x := by
  exact Real.sq_sqrt (p15VecNormSq_nonneg x)

private lemma p15FrobNormSq_nonneg {m n : ℕ} (A : P15Matrix m n) :
    0 ≤ p15FrobNormSq A := by
  unfold p15FrobNormSq
  exact Finset.sum_nonneg (fun i _ => p15VecNormSq_nonneg (A i))

private lemma p15FrobNorm_le_of_rows {m n : ℕ}
    (A Q : P15Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, p15VecNorm (A i) ≤ c * p15VecNorm (Q i)) :
    p15FrobNorm A ≤ c * p15FrobNorm Q := by
  have hs : p15FrobNormSq A ≤ c ^ 2 * p15FrobNormSq Q := by
    calc
      p15FrobNormSq A = ∑ i : Fin m, p15VecNorm (A i) ^ 2 := by
        simp [p15FrobNormSq, p15VecNorm_sq]
      _ ≤ ∑ i : Fin m, (c * p15VecNorm (Q i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hAi : 0 ≤ p15VecNorm (A i) := Real.sqrt_nonneg _
        have hQi : 0 ≤ p15VecNorm (Q i) := Real.sqrt_nonneg _
        nlinarith [hrow i]
      _ = c ^ 2 * p15FrobNormSq Q := by
        simp only [mul_pow, ← Finset.mul_sum]
        congr 1
        simp [p15FrobNormSq, p15VecNorm_sq]
  calc
    p15FrobNorm A = Real.sqrt (p15FrobNormSq A) := rfl
    _ ≤ Real.sqrt (c ^ 2 * p15FrobNormSq Q) := Real.sqrt_le_sqrt hs
    _ = c * p15FrobNorm Q := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
      rfl

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
  let A := p15Residual Q R X
  let c : ℝ := (11 / 10) * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    have hu : 0 ≤ fp.u := fp.u_nonneg
    positivity
  have hrow : ∀ i : Fin m, p15VecNorm (A i) ≤ c * p15VecNorm (Q i) := by
    intro i
    have hLT : ∀ k j : Fin n, k.val < j.val → p15Transpose R k j = 0 := by
      intro k j hkj
      exact hupper j k hkj
    have hD : ∀ k : Fin n, p15Transpose R k k ≠ 0 := by
      intro k
      exact hdiag k
    have hV : NumStability.gammaValid (p15ToFPModel fp) n := hvalid
    obtain ⟨deltaL, hδ, heq⟩ :=
      NumStability.forwardSub_backward_error
        (p15ToFPModel fp) n (p15Transpose R) (X i) hD hLT hV
    apply hperturb i deltaL
    · intro k j
      simpa [p15Gamma, NumStability.gamma, p15ToFPModel, p15Transpose] using hδ k j
    · intro k
      simpa [Q, p15RoundedQ, p15ForwardSub_eq] using heq k
  have hFrob : p15FrobNorm A ≤ c * p15FrobNorm Q :=
    p15FrobNorm_le_of_rows A Q c hc hrow
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hsqrt3 : Real.sqrt (3 : ℝ) ≤ 20 / 11 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg (3 : ℝ)]
  have hsqrtn : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt hn
  have hroot : Real.sqrt (3 * (n : ℝ)) = Real.sqrt 3 * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    p15FrobNorm A ≤ c * p15FrobNorm Q := hFrob
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hc
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      rw [hroot]
      dsimp [c]
      nlinarith [mul_nonneg (mul_nonneg hn hu) hxNorm,
        mul_le_mul_of_nonneg_right hsqrt3
          (mul_nonneg (mul_nonneg hn hu) hxNorm)]

end VSCLReuse

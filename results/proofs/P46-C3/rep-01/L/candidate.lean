import VSCLReuse.P46.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p46AsNumFP (fp : P46TriFPModel) : NumStability.FPModel where
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

private lemma p46_dot_bridge (fp : P46TriFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p46RoundedDotProduct fp.toP46FPModel n x y =
      NumStability.fl_dotProduct (p46AsNumFP fp) n x y := by
  rfl

private lemma p46_back_bridge (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) :
    p46BackSub fp n U b = NumStability.fl_backSub (p46AsNumFP fp) n U b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p46BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p46AsNumFP fp) n U b k hk x := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro hk x
      simp only [p46BackSubSteps, NumStability.fl_backSub_steps]
      apply ih
  exact hsteps n (le_refl n) (fun _ => 0)

/-- Section 3.2: high-precision kernels rounded once to low precision. -/
theorem p46_c3_simulated_product_and_triangular_solve
    (fp : P46TriFPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hu : 0 < fp.u)
    (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    (∀ i j,
      |p46SimulatedMatMul fp.toP46FPModel A B i j - p46MatMul A B i j| ≤
        2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j) ∧
    (∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j|) := by
  -- PROOF_START P46-C3-H001
  have hgamma : p46Gamma fp.u n * (1 + fp.u_low) ≤ fp.u_low := by
    have hden : 0 < 1 - (n : ℝ) * fp.u := by
      dsimp [P46GammaValid] at hvalid
      linarith
    have hmult : 0 < fp.u * (1 + 2 * fp.u_low) := by
      have := fp.u_low_nonneg
      positivity
    have hbound : ((n : ℝ) * fp.u) * (1 + 2 * fp.u_low) ≤ fp.u_low := by
      have h := (le_div_iff₀ hmult).mp hsize
      nlinarith
    unfold p46Gamma
    calc
      (n : ℝ) * fp.u / (1 - (n : ℝ) * fp.u) * (1 + fp.u_low) =
          ((n : ℝ) * fp.u * (1 + fp.u_low)) / (1 - (n : ℝ) * fp.u) := by ring
      _ ≤ fp.u_low := (div_le_iff₀ hden).2 (by nlinarith [hbound])
  have hcoeff : fp.u_low * (1 + p46Gamma fp.u n) + p46Gamma fp.u n ≤
      2 * fp.u_low := by
    nlinarith [hgamma]
  constructor
  · intro i j
    let H : ℝ := ∑ k : Fin n, |A i k| * |B k j|
    let C : ℝ := ∑ k : Fin n, A i k * B k j
    let Chat : ℝ := p46RoundedDotProduct fp.toP46FPModel n (A i) (fun k => B k j)
    have hH : 0 ≤ H := Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hhigh : |Chat - C| ≤ p46Gamma fp.u n * H := by
      simpa only [Chat, C, H, p46_dot_bridge, p46AsNumFP, NumStability.gamma] using
        (NumStability.dotProduct_error_bound (p46AsNumFP fp) n (A i)
          (fun k => B k j) (show NumStability.gammaValid (p46AsNumFP fp) n from hvalid))
    have hC : |C| ≤ H := by
      calc
        |C| ≤ ∑ k : Fin n, |A i k * B k j| := by
          exact Finset.abs_sum_le_sum_abs _ _
        _ = H := by simp [H, abs_mul]
    have hChat : |Chat| ≤ (1 + p46Gamma fp.u n) * H := by
      calc
        |Chat| = |(Chat - C) + C| := by ring
        _ ≤ |Chat - C| + |C| := abs_add_le _ _
        _ ≤ p46Gamma fp.u n * H + H := add_le_add hhigh hC
        _ = (1 + p46Gamma fp.u n) * H := by ring
    have hlow : |fp.fl_low Chat - Chat| ≤ fp.u_low * |Chat| := fp.model_low Chat
    change |fp.fl_low Chat - C| ≤ 2 * fp.u_low * H
    calc
      |fp.fl_low Chat - C| = |(fp.fl_low Chat - Chat) + (Chat - C)| := by ring
      _ ≤ |fp.fl_low Chat - Chat| + |Chat - C| := abs_add_le _ _
      _ ≤ fp.u_low * |Chat| + p46Gamma fp.u n * H := add_le_add hlow hhigh
      _ ≤ fp.u_low * ((1 + p46Gamma fp.u n) * H) + p46Gamma fp.u n * H :=
        by
          gcongr
          exact fp.u_low_nonneg
      _ = (fp.u_low * (1 + p46Gamma fp.u n) + p46Gamma fp.u n) * H := by ring
      _ ≤ 2 * fp.u_low * H := mul_le_mul_of_nonneg_right hcoeff hH
  · obtain ⟨ΔU, hΔU, hsystem⟩ :=
      NumStability.backSub_backward_error (p46AsNumFP fp) n U b hUdiag hUupper
        (show NumStability.gammaValid (p46AsNumFP fp) n from hvalid)
    intro i
    have hΔ : ∀ j : Fin n, |ΔU i j| ≤ p46Gamma fp.u n * |U i j| := by
      intro j
      simpa only [NumStability.gamma, p46AsNumFP, p46Gamma] using hΔU i j
    have hsys : ∑ j : Fin n, (U i j + ΔU i j) * p46BackSub fp n U b j = b i := by
      simpa only [← p46_back_bridge] using hsystem i
    have hsum :
        |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
          ∑ j : Fin n,
            |U i j * p46SimulatedBackSub fp n U b j -
                (U i j + ΔU i j) * p46BackSub fp n U b j| := by
      rw [← hsys, ← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    calc
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
          ∑ j : Fin n,
            |U i j * p46SimulatedBackSub fp n U b j -
                (U i j + ΔU i j) * p46BackSub fp n U b j| := hsum
      _ ≤ ∑ j : Fin n, (p46Gamma fp.u n + fp.u_low) *
          (|U i j| * |p46BackSub fp n U b j|) := by
        apply Finset.sum_le_sum
        intro j hj
        let x := p46BackSub fp n U b j
        have hlow : |p46SimulatedBackSub fp n U b j - x| ≤ fp.u_low * |x| :=
          fp.model_low x
        have hmul1 : |U i j| * |p46SimulatedBackSub fp n U b j - x| ≤
            |U i j| * (fp.u_low * |x|) :=
          mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
        have hmul2 : |ΔU i j| * |x| ≤
            (p46Gamma fp.u n * |U i j|) * |x| :=
          mul_le_mul_of_nonneg_right (hΔ j) (abs_nonneg _)
        change |U i j * p46SimulatedBackSub fp n U b j - (U i j + ΔU i j) * x| ≤
          (p46Gamma fp.u n + fp.u_low) * (|U i j| * |x|)
        calc
          |U i j * p46SimulatedBackSub fp n U b j - (U i j + ΔU i j) * x| =
              |U i j * (p46SimulatedBackSub fp n U b j - x) - ΔU i j * x| := by ring
          _ ≤ |U i j * (p46SimulatedBackSub fp n U b j - x)| + |ΔU i j * x| :=
            by
              rw [sub_eq_add_neg]
              simpa only [abs_neg] using
                (abs_add_le (U i j * (p46SimulatedBackSub fp n U b j - x)) (-(ΔU i j * x)))
          _ = |U i j| * |p46SimulatedBackSub fp n U b j - x| + |ΔU i j| * |x| := by
            rw [abs_mul, abs_mul]
          _ ≤ |U i j| * (fp.u_low * |x|) +
              (p46Gamma fp.u n * |U i j|) * |x| := add_le_add hmul1 hmul2
          _ = (p46Gamma fp.u n + fp.u_low) * (|U i j| * |x|) := by ring
      _ = (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j| := by
        rw [Finset.mul_sum]

end VSCLReuse

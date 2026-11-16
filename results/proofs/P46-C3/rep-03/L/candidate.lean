import VSCLReuse.P46.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p46LibraryModel (fp : P46TriFPModel) : NumStability.FPModel where
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

private lemma p46LibraryDot_eq (fp : P46TriFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p46RoundedDotProduct fp.toP46FPModel n x y =
      NumStability.fl_dotProduct (p46LibraryModel fp) n x y := by
  rfl

private lemma p46LibraryBackSub_eq (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) :
    p46BackSub fp n U b =
      NumStability.fl_backSub (p46LibraryModel fp) n U b := by
  have hsteps : ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p46BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p46LibraryModel fp) n U b k hk x := by
    intro k
    induction k with
    | zero => intro hk x; rfl
    | succ k ih =>
      intro hk x
      simp only [p46BackSubSteps, NumStability.fl_backSub_steps]
      exact ih (Nat.le_of_succ_le hk) _
  exact hsteps n (le_refl n) _

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
  have hden : 0 < fp.u * (1 + 2 * fp.u_low) := by
    apply mul_pos hu
    linarith [fp.u_low_nonneg]
  have hsize' : (n : ℝ) * fp.u * (1 + 2 * fp.u_low) ≤ fp.u_low := by
    simpa only [mul_assoc] using (le_div_iff₀ hden).mp hsize
  have hγden : 0 < 1 - (n : ℝ) * fp.u := by
    exact sub_pos.mpr hvalid
  have hγcoeff : p46Gamma fp.u n * (1 + fp.u_low) ≤ fp.u_low := by
    unfold p46Gamma
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hγden).2
    nlinarith [hsize']
  constructor
  · intro i j
    let C : ℝ := p46MatMul A B i j
    let Chat : ℝ := p46RoundedMatMul fp.toP46FPModel A B i j
    let M : ℝ := p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j
    have hM : 0 ≤ M := by
      dsimp [M, p46MatMul, p46AbsMatrix]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hC : |C| ≤ M := by
      dsimp [C, M, p46MatMul, p46AbsMatrix]
      calc
        |∑ k : Fin n, A i k * B k j| ≤ ∑ k : Fin n, |A i k * B k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |A i k| * |B k j| := by simp only [abs_mul]
    have hhi : |Chat - C| ≤ p46Gamma fp.u n * M := by
      simpa only [Chat, C, M, p46RoundedMatMul, p46MatMul,
        p46AbsMatrix, p46LibraryDot_eq, p46Gamma, NumStability.gamma,
        p46LibraryModel] using
        (NumStability.dotProduct_error_bound (p46LibraryModel fp) n
          (A i) (fun k => B k j) hvalid)
    have hround : |fp.fl_low Chat - Chat| ≤ fp.u_low * |Chat| := fp.model_low Chat
    have hChat : |Chat| ≤ (1 + p46Gamma fp.u n) * M := by
      have ht : |Chat| ≤ |Chat - C| + |C| := by
        simpa only [sub_add_cancel] using (abs_add_le (Chat - C) C)
      nlinarith [hhi, hC]
    have htotal : |fp.fl_low Chat - C| ≤
        (p46Gamma fp.u n * (1 + fp.u_low) + fp.u_low) * M := by
      have hscale := mul_le_mul_of_nonneg_left hChat fp.u_low_nonneg
      calc
        |fp.fl_low Chat - C| = |(fp.fl_low Chat - Chat) + (Chat - C)| := by ring
        _ ≤ |fp.fl_low Chat - Chat| + |Chat - C| := abs_add_le _ _
        _ ≤ fp.u_low * |Chat| + p46Gamma fp.u n * M := add_le_add hround hhi
        _ ≤ fp.u_low * ((1 + p46Gamma fp.u n) * M) +
            p46Gamma fp.u n * M := add_le_add hscale le_rfl
        _ = (p46Gamma fp.u n * (1 + fp.u_low) + fp.u_low) * M := by ring
    have hfinal :
        (p46Gamma fp.u n * (1 + fp.u_low) + fp.u_low) * M ≤
          2 * fp.u_low * M := by
      nlinarith [mul_le_mul_of_nonneg_right hγcoeff hM]
    simpa only [p46SimulatedMatMul, C, M, Chat] using le_trans htotal hfinal
  · intro i
    let xhat : Fin n → ℝ := p46BackSub fp n U b
    let xtilde : Fin n → ℝ := p46SimulatedBackSub fp n U b
    obtain ⟨ΔU, hΔ, hEq⟩ :=
      NumStability.backSub_backward_error (p46LibraryModel fp) n U b
        hUdiag hUupper hvalid
    have hEq' : ∑ j : Fin n, (U i j + ΔU i j) * xhat j = b i := by
      simpa only [xhat, ← p46LibraryBackSub_eq fp n U b] using hEq i
    have hΔ' : ∀ j : Fin n,
        |ΔU i j| ≤ p46Gamma fp.u n * |U i j| := by
      intro j
      simpa only [p46Gamma, NumStability.gamma, p46LibraryModel] using hΔ i j
    have hround : ∀ j : Fin n, |xtilde j - xhat j| ≤ fp.u_low * |xhat j| := by
      intro j
      exact fp.model_low (xhat j)
    have hident : (∑ j : Fin n, U i j * xtilde j) - b i =
        (∑ j : Fin n, U i j * (xtilde j - xhat j)) -
          (∑ j : Fin n, ΔU i j * xhat j) := by
      rw [← hEq']
      simp_rw [add_mul, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      ring
    have hroundsum :
        |∑ j : Fin n, U i j * (xtilde j - xhat j)| ≤
          fp.u_low * ∑ j : Fin n, |U i j| * |xhat j| := by
      calc
        |∑ j : Fin n, U i j * (xtilde j - xhat j)| ≤
            ∑ j : Fin n, |U i j * (xtilde j - xhat j)| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n, fp.u_low * (|U i j| * |xhat j|) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          calc
            |U i j| * |xtilde j - xhat j| ≤
                |U i j| * (fp.u_low * |xhat j|) :=
                  mul_le_mul_of_nonneg_left (hround j) (abs_nonneg _)
            _ = fp.u_low * (|U i j| * |xhat j|) := by ring
        _ = fp.u_low * ∑ j : Fin n, |U i j| * |xhat j| := by
          rw [Finset.mul_sum]
    have hΔsum :
        |∑ j : Fin n, ΔU i j * xhat j| ≤
          p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |xhat j| := by
      calc
        |∑ j : Fin n, ΔU i j * xhat j| ≤
            ∑ j : Fin n, |ΔU i j * xhat j| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin n, p46Gamma fp.u n * (|U i j| * |xhat j|) := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul]
          calc
            |ΔU i j| * |xhat j| ≤
                (p46Gamma fp.u n * |U i j|) * |xhat j| :=
                  mul_le_mul_of_nonneg_right (hΔ' j) (abs_nonneg _)
            _ = p46Gamma fp.u n * (|U i j| * |xhat j|) := by ring
        _ = p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |xhat j| := by
          rw [Finset.mul_sum]
    calc
      |(∑ j : Fin n, U i j * xtilde j) - b i| =
          |(∑ j : Fin n, U i j * (xtilde j - xhat j)) -
            (∑ j : Fin n, ΔU i j * xhat j)| := by rw [hident]
      _ ≤ |∑ j : Fin n, U i j * (xtilde j - xhat j)| +
          |∑ j : Fin n, ΔU i j * xhat j| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (∑ j : Fin n, U i j * (xtilde j - xhat j))
                (-(∑ j : Fin n, ΔU i j * xhat j)))
      _ ≤ fp.u_low * (∑ j : Fin n, |U i j| * |xhat j|) +
          p46Gamma fp.u n * (∑ j : Fin n, |U i j| * |xhat j|) :=
            add_le_add hroundsum hΔsum
      _ = (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |xhat j| := by ring

end VSCLReuse

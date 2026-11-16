import VSCLReuse.P46.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p46NumFP (fp : P46TriFPModel) : NumStability.FPModel where
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
    exact ⟨0, by simp [fp.u_nonneg], by simp⟩

private theorem p46_num_dot_eq (fp : P46TriFPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p46RoundedDotProduct fp.toP46FPModel n x y =
      NumStability.fl_dotProduct (p46NumFP fp) n x y := by
  rfl

private theorem p46_num_steps_eq (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      p46BackSubSteps fp n U b k hk x =
        NumStability.fl_backSub_steps (p46NumFP fp) n U b k hk x := by
  intro k
  induction k with
  | zero =>
      intro hk x
      rfl
  | succ k ih =>
      intro hk x
      simp only [p46BackSubSteps, NumStability.fl_backSub_steps]
      exact ih (Nat.le_of_succ_le hk) _

private theorem p46_num_backSub_eq (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) :
    p46BackSub fp n U b =
      NumStability.fl_backSub (p46NumFP fp) n U b := by
  exact p46_num_steps_eq fp n U b n (le_refl n) (fun _ => 0)

private theorem p46_num_gamma_eq (fp : P46TriFPModel) (n : ℕ) :
    p46Gamma fp.u n = NumStability.gamma (p46NumFP fp) n := by
  rfl

private theorem p46_num_valid (fp : P46TriFPModel) (n : ℕ)
    (hvalid : P46GammaValid fp.u n) :
    NumStability.gammaValid (p46NumFP fp) n := by
  exact hvalid

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
  have hden : 0 < 1 - (n : ℝ) * fp.u := by
    dsimp [P46GammaValid] at hvalid
    linarith
  have hlowden : 0 < 1 + 2 * fp.u_low := by
    linarith [fp.u_low_nonneg]
  have hsize' : (n : ℝ) * fp.u * (1 + 2 * fp.u_low) ≤ fp.u_low := by
    have h := (le_div_iff₀ (mul_pos hu hlowden)).mp hsize
    nlinarith [h]
  have hgamma : p46Gamma fp.u n * (1 + fp.u_low) ≤ fp.u_low := by
    unfold p46Gamma
    calc
      ((n : ℝ) * fp.u) / (1 - (n : ℝ) * fp.u) * (1 + fp.u_low) =
          ((n : ℝ) * fp.u * (1 + fp.u_low)) / (1 - (n : ℝ) * fp.u) := by ring
      _ ≤ fp.u_low := (div_le_iff₀ hden).2 (by nlinarith [hsize'])
  constructor
  · intro i j
    let C : ℝ := p46MatMul A B i j
    let E : ℝ := p46RoundedMatMul fp.toP46FPModel A B i j
    let S : ℝ := p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j
    have hS : 0 ≤ S := by
      dsimp [S, p46MatMul, p46AbsMatrix]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hC : |C| ≤ S := by
      dsimp [C, S, p46MatMul, p46AbsMatrix]
      calc
        |∑ k : Fin n, A i k * B k j| ≤ ∑ k : Fin n, |A i k * B k j| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, |A i k| * |B k j| := by simp only [abs_mul]
    have hE : |E - C| ≤ p46Gamma fp.u n * S := by
      simpa only [E, C, S, p46RoundedMatMul, p46MatMul, p46AbsMatrix,
        p46_num_dot_eq, p46_num_gamma_eq] using
        (NumStability.dotProduct_error_bound (p46NumFP fp) n (A i)
          (fun k => B k j) (p46_num_valid fp n hvalid))
    have hEabs : |E| ≤ (1 + p46Gamma fp.u n) * S := by
      calc
        |E| = |(E - C) + C| := by congr 1; ring
        _ ≤ |E - C| + |C| := abs_add_le _ _
        _ ≤ p46Gamma fp.u n * S + S := add_le_add hE hC
        _ = (1 + p46Gamma fp.u n) * S := by ring
    have hlow : |fp.fl_low E - E| ≤ fp.u_low * |E| := fp.model_low E
    have hcoef : fp.u_low + p46Gamma fp.u n * (1 + fp.u_low) ≤
        2 * fp.u_low := by linarith [hgamma]
    change |fp.fl_low E - C| ≤ 2 * fp.u_low * S
    calc
      |fp.fl_low E - C| = |(fp.fl_low E - E) + (E - C)| := by congr 1; ring
      _ ≤ |fp.fl_low E - E| + |E - C| := abs_add_le _ _
      _ ≤ fp.u_low * |E| + p46Gamma fp.u n * S := add_le_add hlow hE
      _ ≤ fp.u_low * ((1 + p46Gamma fp.u n) * S) +
          p46Gamma fp.u n * S :=
        add_le_add (mul_le_mul_of_nonneg_left hEabs fp.u_low_nonneg) le_rfl
      _ = (fp.u_low + p46Gamma fp.u n * (1 + fp.u_low)) * S := by ring
      _ ≤ 2 * fp.u_low * S := mul_le_mul_of_nonneg_right hcoef hS
  · intro i
    let x : Fin n → ℝ := p46BackSub fp n U b
    let y : Fin n → ℝ := p46SimulatedBackSub fp n U b
    let S : ℝ := ∑ j : Fin n, |U i j| * |x j|
    let γ : ℝ := p46Gamma fp.u n
    obtain ⟨ΔU, hΔU, hEq⟩ :=
      NumStability.backSub_backward_error (p46NumFP fp) n U b
        hUdiag hUupper (p46_num_valid fp n hvalid)
    have hΔU' (j : Fin n) : |ΔU i j| ≤ γ * |U i j| := by
      simpa only [γ, p46_num_gamma_eq] using hΔU i j
    have hEq' : (∑ j : Fin n, (U i j + ΔU i j) * x j) = b i := by
      simpa only [x, p46_num_backSub_eq] using hEq i
    have hhigh : |(∑ j : Fin n, U i j * x j) - b i| ≤ γ * S := by
      calc
        |(∑ j : Fin n, U i j * x j) - b i| =
            |∑ j : Fin n, -(ΔU i j * x j)| := by
          rw [← hEq', ← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ∑ j : Fin n, |-(ΔU i j * x j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |ΔU i j| * |x j| := by
          simp only [abs_neg, abs_mul]
        _ ≤ ∑ j : Fin n, (γ * |U i j|) * |x j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hΔU' j) (abs_nonneg _)
        _ = γ * S := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    have hlow (j : Fin n) : |y j - x j| ≤ fp.u_low * |x j| := by
      exact fp.model_low (x j)
    have hround :
        |(∑ j : Fin n, U i j * y j) - (∑ j : Fin n, U i j * x j)| ≤
          fp.u_low * S := by
      calc
        |(∑ j : Fin n, U i j * y j) - (∑ j : Fin n, U i j * x j)| =
            |∑ j : Fin n, U i j * (y j - x j)| := by
          rw [← Finset.sum_sub_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ ∑ j : Fin n, |U i j * (y j - x j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |U i j| * |y j - x j| := by
          simp only [abs_mul]
        _ ≤ ∑ j : Fin n, |U i j| * (fp.u_low * |x j|) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hlow j) (abs_nonneg _)
        _ = fp.u_low * S := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    change |(∑ j : Fin n, U i j * y j) - b i| ≤ (γ + fp.u_low) * S
    calc
      |(∑ j : Fin n, U i j * y j) - b i| =
          |((∑ j : Fin n, U i j * y j) - (∑ j : Fin n, U i j * x j)) +
            ((∑ j : Fin n, U i j * x j) - b i)| := by congr 1; ring
      _ ≤ |(∑ j : Fin n, U i j * y j) - (∑ j : Fin n, U i j * x j)| +
          |(∑ j : Fin n, U i j * x j) - b i| := abs_add_le _ _
      _ ≤ fp.u_low * S + γ * S := add_le_add hround hhigh
      _ = (γ + fp.u_low) * S := by ring

end VSCLReuse

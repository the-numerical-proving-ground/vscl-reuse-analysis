import VSCLReuse.P30.Definitions
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations

namespace VSCLReuse

private theorem p30_norm_sq {d : ℕ} (x : P30Vector d) :
    p30VecNorm x ^ 2 = ∑ i : Fin d, x i ^ 2 := by
  unfold p30VecNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (x i)))

private theorem p30_norm_nonneg {d : ℕ} (x : P30Vector d) :
    0 ≤ p30VecNorm x := Real.sqrt_nonneg _

private theorem p30_ls_objective_eq {d e : ℕ}
    (H : Fin d → Fin e → ℝ) (b : P30Vector d) (x : P30Vector e) :
    NumStability.lsObjective H b x =
      p30VecNorm (fun i => b i - (∑ j : Fin e, H i j * x j)) ^ 2 := by
  rw [p30_norm_sq]
  unfold NumStability.lsObjective NumStability.vecNorm2Sq
    NumStability.lsResidual NumStability.rectMatMulVec
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Complete named Lemma 5.1 under the paper's full Givens QR and GMRES run model. -/
theorem p30_lemma51_from_full_gmres_minimization
    {n m : ℕ} (a : P30Lemma51Angles m) (β : ℝ)
    (H : P30TallMatrix m)
    (V : Fin n → Fin (m + 1) → ℝ) (r0 : P30Vector n)
    (R Rinv : P30Matrix m) (sigma : ℝ) (hsigma : 0 < sigma)
    (hQR : H = p30_tall_left_mul
      (fun i j => p30_lemma51_qt a j i) (p30_tall_embed_matrix R))
    (hRinv : p30MatMul R Rinv = p30Id m)
    (hSigma : ∀ v : P30Vector m,
      sigma * p30VecNorm v ≤ p30VecNorm (p30_tall_matvec H v))
    (hSigmaAttained : ∃ v : P30Vector m,
      p30VecNorm v = 1 ∧ p30VecNorm (p30_tall_matvec H v) = sigma)
    (hRupper : ∀ i j : Fin m, j.val < i.val → R i j = 0)
    (hVisometry : ∀ z : P30Vector (m + 1),
      p30VecNorm (p30_lemma51_basisMatVec V z) = p30VecNorm z)
    (hr0 : r0 = p30_lemma51_basisMatVec V
      (fun j : Fin (m + 1) => if j = 0 then β else 0))
    (yprev : Fin m → P30Vector m)
    (hYprevSupport : ∀ k j : Fin m,
      k.val ≤ j.val → yprev k j = 0)
    (hPrevMin : ∀ k : Fin m, ∀ z : P30Vector m,
      (∀ j : Fin m, k.val ≤ j.val → z j = 0) →
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H (yprev k) i) ≤
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H z i))
    (y : P30Vector m)
    (hFullMin : ∀ z : P30Vector m,
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H y i) ≤
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H z i)) :
    ∀ k : Fin m, |y k| ≤ sigma⁻¹ *
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
  -- PROOF_START P30-C2-H001
  let b : P30Vector (m + 1) := fun i => if i = 0 then β else 0
  have hmin : NumStability.IsLeastSquaresMinimizer H b y := by
    intro z
    rw [p30_ls_objective_eq H b y, p30_ls_objective_eq H b z]
    have hle := hFullMin z
    have hy0 := p30_norm_nonneg
      (fun i : Fin (m + 1) => b i - p30_tall_matvec H y i)
    have hz0 := p30_norm_nonneg
      (fun i : Fin (m + 1) => b i - p30_tall_matvec H z i)
    change p30VecNorm (fun i : Fin (m + 1) =>
      b i - p30_tall_matvec H y i) ≤
      p30VecNorm (fun i : Fin (m + 1) =>
        b i - p30_tall_matvec H z i) at hle
    change (p30VecNorm (fun i : Fin (m + 1) =>
      b i - p30_tall_matvec H y i)) ^ 2 ≤
      (p30VecNorm (fun i : Fin (m + 1) =>
        b i - p30_tall_matvec H z i)) ^ 2
    nlinarith
  have horth :=
    (NumStability.IsLeastSquaresMinimizer.rectLSNormalEquations hmin).residual_orthogonal
  intro k
  let w : P30Vector m := fun j => yprev k j - y j
  have hwyprev : (fun j : Fin m => y j + w j) = yprev k := by
    ext j
    dsimp [w]
    ring
  have hcross :
      (∑ j : Fin m, w j *
        (∑ i : Fin (m + 1), H i j * NumStability.lsResidual H b y i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [horth j]
    ring
  have hvecsq :
      NumStability.vecNorm2Sq (NumStability.rectMatMulVec H w) =
        p30VecNorm (p30_tall_matvec H w) ^ 2 := by
    rw [p30_norm_sq]
    rfl
  have hexp := NumStability.lsObjective_add_direction_eq H b y w
  rw [hwyprev, p30_ls_objective_eq H b (yprev k),
    p30_ls_objective_eq H b y, hcross, hvecsq] at hexp
  simp only [mul_zero, add_zero] at hexp
  have hH :
      p30VecNorm (p30_tall_matvec H w) ≤
        p30VecNorm (fun i : Fin (m + 1) =>
          b i - p30_tall_matvec H (yprev k) i) := by
    have hfull0 := p30_norm_nonneg
      (fun i : Fin (m + 1) => b i - p30_tall_matvec H y i)
    have hHw0 := p30_norm_nonneg (p30_tall_matvec H w)
    have hprev0 := p30_norm_nonneg
      (fun i : Fin (m + 1) => b i - p30_tall_matvec H (yprev k) i)
    change (p30VecNorm (fun i : Fin (m + 1) =>
      b i - p30_tall_matvec H (yprev k) i)) ^ 2 =
      (p30VecNorm (fun i : Fin (m + 1) =>
        b i - p30_tall_matvec H y i)) ^ 2 +
      p30VecNorm (p30_tall_matvec H w) ^ 2 at hexp
    nlinarith
  have hcomponent : |y k| ≤ p30VecNorm w := by
    have hzero : yprev k k = 0 := hYprevSupport k k (le_refl _)
    have hcoord : |y k| = |w k| := by simp [w, hzero, abs_neg]
    have hsq : w k ^ 2 ≤ ∑ j : Fin m, w j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ k)
    have hnonneg := p30_norm_nonneg w
    have hnormsq := p30_norm_sq w
    rw [hcoord]
    nlinarith [sq_abs (w k)]
  have hres :
      (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
      p30_lemma51_basisMatVec V
        (fun i : Fin (m + 1) => b i - p30_tall_matvec H (yprev k) i) := by
    ext i
    change r0 i - (∑ j : Fin (m + 1),
      V i j * p30_tall_matvec H (yprev k) j) =
      ∑ j : Fin (m + 1),
        V i j * (b j - p30_tall_matvec H (yprev k) j)
    rw [hr0]
    change (∑ j : Fin (m + 1), V i j * b j) -
      (∑ j : Fin (m + 1), V i j * p30_tall_matvec H (yprev k) j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hres, hVisometry]
  have hprod := le_trans (hSigma w) hH
  calc
    |y k| ≤ p30VecNorm w := hcomponent
    _ = sigma⁻¹ * (sigma * p30VecNorm w) := by
      field_simp [ne_of_gt hsigma]
    _ ≤ sigma⁻¹ * p30VecNorm
        (fun i : Fin (m + 1) => b i - p30_tall_matvec H (yprev k) i) :=
      mul_le_mul_of_nonneg_left hprod (le_of_lt (inv_pos.mpr hsigma))

end VSCLReuse

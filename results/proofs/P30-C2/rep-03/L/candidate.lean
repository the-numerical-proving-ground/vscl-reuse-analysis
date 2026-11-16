import VSCLReuse.P30.Definitions
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations

namespace VSCLReuse

private theorem p30_least_squares_difference_bound
    {r c : ℕ} (A : Fin r → Fin c → ℝ) (b : Fin r → ℝ)
    (x x₀ : Fin c → ℝ)
    (hmin : NumStability.IsLeastSquaresMinimizer A b x) :
    NumStability.vecNorm2
        (NumStability.rectMatMulVec A (fun j => x₀ j - x j)) ≤
      NumStability.vecNorm2 (NumStability.lsResidual A b x₀) := by
  let d : Fin c → ℝ := fun j => x₀ j - x j
  have hx₀ : x₀ = fun j => x j + d j := by
    ext j
    dsimp [d]
    ring
  have horth := hmin.rectLSNormalEquations.residual_orthogonal
  have hcross :
      (∑ j : Fin c, d j *
        (∑ i : Fin r, A i j * NumStability.lsResidual A b x i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [horth j]
    ring
  have hpyth := NumStability.lsObjective_add_direction_eq A b x d
  rw [← hx₀, hcross] at hpyth
  simp only [mul_zero, add_zero] at hpyth
  have hsq : NumStability.vecNorm2Sq (NumStability.rectMatMulVec A d) ≤
      NumStability.vecNorm2Sq (NumStability.lsResidual A b x₀) := by
    unfold NumStability.lsObjective at hpyth
    linarith [NumStability.vecNorm2Sq_nonneg (NumStability.lsResidual A b x)]
  change Real.sqrt (NumStability.vecNorm2Sq (NumStability.rectMatMulVec A d)) ≤
    Real.sqrt (NumStability.vecNorm2Sq (NumStability.lsResidual A b x₀))
  exact Real.sqrt_le_sqrt hsq

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
  let b : P30Vector (m + 1) :=
    fun i => if i = 0 then β else 0
  have hsign (z : P30Vector m) :
      NumStability.vecNorm2 (NumStability.lsResidual H b z) =
        p30VecNorm (fun i => b i - p30_tall_matvec H z i) := by
    unfold NumStability.vecNorm2 NumStability.vecNorm2Sq p30VecNorm
      NumStability.lsResidual NumStability.rectMatMulVec p30_tall_matvec
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmin : NumStability.IsLeastSquaresMinimizer H b y := by
    intro z
    change NumStability.vecNorm2Sq (NumStability.lsResidual H b y) ≤
      NumStability.vecNorm2Sq (NumStability.lsResidual H b z)
    rw [← NumStability.vecNorm2_sq, ← NumStability.vecNorm2_sq,
      hsign y, hsign z]
    have h := hFullMin z
    change p30VecNorm (fun i => b i - p30_tall_matvec H y i) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H z i) at h
    have hy_nonneg : 0 ≤ p30VecNorm
        (fun i => b i - p30_tall_matvec H y i) := Real.sqrt_nonneg _
    have hz_nonneg : 0 ≤ p30VecNorm
        (fun i => b i - p30_tall_matvec H z i) := Real.sqrt_nonneg _
    nlinarith
  intro k
  let d : P30Vector m := fun j => yprev k j - y j
  have hdiff := p30_least_squares_difference_bound H b y (yprev k) hmin
  have hA : p30VecNorm (p30_tall_matvec H d) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) := by
    change p30VecNorm (p30_tall_matvec H d) ≤
      NumStability.vecNorm2 (NumStability.lsResidual H b (yprev k)) at hdiff
    rw [hsign (yprev k)] at hdiff
    exact hdiff
  have hcoord := NumStability.abs_coord_le_vecNorm2 d k
  change |d k| ≤ p30VecNorm d at hcoord
  have hprevk : yprev k k = 0 := hYprevSupport k k (le_refl _)
  have hk : |y k| ≤ p30VecNorm d := by
    simpa [d, hprevk, abs_neg] using hcoord
  have hσd := hSigma d
  have hamb : (fun i : Fin n => r0 i -
      p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
      p30_lemma51_basisMatVec V
        (fun j => b j - p30_tall_matvec H (yprev k) j) := by
    ext i
    rw [hr0]
    change (∑ j : Fin (m + 1), V i j * b j) -
        (∑ j : Fin (m + 1), V i j * p30_tall_matvec H (yprev k) j) =
      ∑ j : Fin (m + 1), V i j *
        (b j - p30_tall_matvec H (yprev k) j)
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hres : p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) =
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
    rw [hamb, hVisometry]
  have hmain : sigma * |y k| ≤
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
    calc
      sigma * |y k| ≤ sigma * p30VecNorm d :=
        mul_le_mul_of_nonneg_left hk hsigma.le
      _ ≤ p30VecNorm (p30_tall_matvec H d) := hσd
      _ ≤ p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) := hA
      _ = _ := hres
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hsigma).2
  nlinarith [hmain]

end VSCLReuse

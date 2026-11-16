import VSCLReuse.P30.Definitions

namespace VSCLReuse

private theorem p30_norm_nonneg {n : ℕ} (v : P30Vector n) :
    0 ≤ p30VecNorm v := Real.sqrt_nonneg _

private theorem p30_norm_sq {n : ℕ} (v : P30Vector n) :
    p30VecNorm v ^ 2 = ∑ i : Fin n, v i ^ 2 := by
  unfold p30VecNorm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))

private theorem p30_minimizer_line_bound {n : ℕ}
    (r d : P30Vector n)
    (hmin : ∀ t : ℝ, p30VecNorm r ≤
      p30VecNorm (fun i => r i - t * d i)) :
    p30VecNorm d ≤ p30VecNorm (fun i => r i + d i) := by
  let B : ℝ := ∑ i : Fin n, r i ^ 2
  let C : ℝ := ∑ i : Fin n, d i ^ 2
  let D : ℝ := ∑ i : Fin n, r i * d i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => sq_nonneg (r i))
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hsub (t : ℝ) :
      (∑ i : Fin n, (r i - t * d i) ^ 2) =
        B - 2 * t * D + t ^ 2 * C := by
    calc
      _ = ∑ i : Fin n, (r i ^ 2 - 2 * t * (r i * d i) +
          t ^ 2 * d i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = B - 2 * t * D + t ^ 2 * C := by
            simp [B, C, D, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * C - 2 * t * D := by
    have h := hmin t
    have hsq1 := p30_norm_sq r
    have hsq2 := p30_norm_sq (fun i => r i - t * d i)
    have hnn1 := p30_norm_nonneg r
    have hnn2 := p30_norm_nonneg (fun i => r i - t * d i)
    rw [hsub t] at hsq2
    nlinarith
  let t : ℝ := D / (C + 1)
  have hCp : 0 < C + 1 := by linarith
  have htD : t * (C + 1) = D := by
    dsimp [t]
    field_simp
  have hq : 0 ≤ -(t ^ 2 * C) - 2 * t ^ 2 := by
    convert hquad t using 1 <;> rw [← htD] <;> ring
  have ht0 : t = 0 := by
    have htc : 0 ≤ t ^ 2 * C := mul_nonneg (sq_nonneg t) hC
    nlinarith [sq_nonneg t]
  have hD : D = 0 := by rw [ht0] at htD; simpa using htD.symm
  have hadd :
      (∑ i : Fin n, (r i + d i) ^ 2) = B + 2 * D + C := by
    calc
      _ = ∑ i : Fin n, (r i ^ 2 + 2 * (r i * d i) + d i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = B + 2 * D + C := by
            simp [B, C, D, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsq1 := p30_norm_sq d
  have hsq2 := p30_norm_sq (fun i => r i + d i)
  have hnn1 := p30_norm_nonneg d
  have hnn2 := p30_norm_nonneg (fun i => r i + d i)
  rw [hadd, hD] at hsq2
  nlinarith

private theorem p30_abs_le_norm {n : ℕ} (v : P30Vector n) (k : Fin n) :
    |v k| ≤ p30VecNorm v := by
  have hsingle : v k ^ 2 ≤ ∑ i : Fin n, v i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ k)
  have hsq := p30_norm_sq v
  have hnn := p30_norm_nonneg v
  nlinarith [abs_nonneg (v k), sq_abs (v k)]

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
  intro k
  let v : P30Vector m := fun j => y j - yprev k j
  let r : P30Vector (m + 1) := fun i =>
    (if i = 0 then β else 0) - p30_tall_matvec H y i
  let d : P30Vector (m + 1) := p30_tall_matvec H v
  have hsub (i : Fin (m + 1)) :
      d i = p30_tall_matvec H y i - p30_tall_matvec H (yprev k) i := by
    simp [d, v, p30_tall_matvec, mul_sub, Finset.sum_sub_distrib]
  have hline (t : ℝ) (i : Fin (m + 1)) :
      p30_tall_matvec H (fun j => y j + t * v j) i =
        p30_tall_matvec H y i + t * d i := by
    change (∑ j, H i j * (y j + t * v j)) =
      (∑ j, H i j * y j) + t * (∑ j, H i j * v j)
    rw [Finset.mul_sum]
    calc
      _ = ∑ j, (H i j * y j + t * (H i j * v j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_add_distrib]
  have hminline : ∀ t : ℝ, p30VecNorm r ≤
      p30VecNorm (fun i => r i - t * d i) := by
    intro t
    calc
      p30VecNorm r ≤ p30VecNorm (fun i : Fin (m + 1) =>
          (if i = 0 then β else 0) -
            p30_tall_matvec H (fun j => y j + t * v j) i) := hFullMin _
      _ = p30VecNorm (fun i => r i - t * d i) := by
        congr 1
        funext i
        rw [hline]
        dsimp [r]
        ring
  have hdist : p30VecNorm d ≤
      p30VecNorm (fun i => r i + d i) :=
    p30_minimizer_line_bound r d hminline
  have hrprev : p30VecNorm (fun i => r i + d i) =
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H (yprev k) i) := by
    congr 1
    funext i
    rw [hsub]
    dsimp [r]
    ring
  have hcoord : |y k| ≤ p30VecNorm v := by
    have hz := hYprevSupport k k (le_refl k.val)
    simpa [v, hz] using p30_abs_le_norm v k
  have hmul : sigma * |y k| ≤ p30VecNorm d :=
    (mul_le_mul_of_nonneg_left hcoord (le_of_lt hsigma)).trans (hSigma v)
  have hambient : p30VecNorm (fun i : Fin n => r0 i -
      p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
      p30VecNorm (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H (yprev k) i) := by
    have heq : (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
        p30_lemma51_basisMatVec V (fun i : Fin (m + 1) =>
          (if i = 0 then β else 0) - p30_tall_matvec H (yprev k) i) := by
      funext i
      rw [hr0]
      simp [p30_lemma51_basisMatVec, mul_sub, Finset.sum_sub_distrib]
    rw [heq, hVisometry]
  apply (le_inv_mul_iff₀ hsigma).2
  calc
    sigma * |y k| ≤ p30VecNorm d := hmul
    _ ≤ p30VecNorm (fun i => r i + d i) := hdist
    _ = _ := hrprev
    _ = _ := hambient.symm

end VSCLReuse

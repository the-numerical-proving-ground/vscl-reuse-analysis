import VSCLReuse.P30.Definitions

namespace VSCLReuse

private lemma p30_norm_nonneg {d : ℕ} (x : P30Vector d) : 0 ≤ p30VecNorm x := by
  unfold p30VecNorm
  positivity

private lemma p30_norm_sq {d : ℕ} (x : P30Vector d) :
    p30VecNorm x ^ 2 = ∑ i : Fin d, x i ^ 2 := by
  unfold p30VecNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (by intro i hi; positivity))]

private lemma p30_sqsum_add {d : ℕ} (r u : P30Vector d) (t : ℝ) :
    (∑ i : Fin d, (r i + t * u i) ^ 2) =
      (∑ i : Fin d, r i ^ 2) + 2 * t * (∑ i : Fin d, r i * u i) +
        t ^ 2 * (∑ i : Fin d, u i ^ 2) := by
  calc
    _ = ∑ i : Fin d, (r i ^ 2 + 2 * t * (r i * u i) + t ^ 2 * u i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma p30_min_orth {d : ℕ} (r u : P30Vector d)
    (hmin : ∀ t : ℝ, p30VecNorm r ≤ p30VecNorm (fun i => r i + t * u i)) :
    (∑ i : Fin d, r i * u i) = 0 := by
  let A : ℝ := ∑ i : Fin d, u i ^ 2
  let B : ℝ := ∑ i : Fin d, r i * u i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (by intro i hi; positivity)
  have hsq (t : ℝ) : 0 ≤ 2 * t * B + t ^ 2 * A := by
    have hn := hmin t
    have hn0 := p30_norm_nonneg r
    have hn1 := p30_norm_nonneg (fun i => r i + t * u i)
    have hs := p30_sqsum_add r u t
    rw [← p30_norm_sq (fun i => r i + t * u i), ← p30_norm_sq r] at hs
    dsimp [A, B]
    nlinarith
  have hden : A + 1 ≠ 0 := by linarith
  have hq := hsq (-B / (A + 1))
  have hmul := mul_nonneg hq (sq_nonneg (A + 1))
  have heq : (2 * (-B / (A + 1)) * B + (-B / (A + 1)) ^ 2 * A) *
      (A + 1) ^ 2 = -(B ^ 2) * (A + 2) := by
    field_simp
    ring
  rw [heq] at hmul
  by_contra hB
  have hp : 0 < B ^ 2 := sq_pos_of_ne_zero hB
  have hAp : 0 < A + 2 := by linarith
  have := mul_pos hp hAp
  dsimp [B] at hB ⊢
  nlinarith

private lemma p30_coord_le_norm {d : ℕ} (x : P30Vector d) (k : Fin d) :
    |x k| ≤ p30VecNorm x := by
  have hle : x k ^ 2 ≤ ∑ i : Fin d, x i ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin d => x i ^ 2)
      (fun i hi => sq_nonneg (x i)) (Finset.mem_univ k)
  have hn := p30_norm_nonneg x
  have hs := p30_norm_sq x
  nlinarith [sq_nonneg (x k), sq_abs (x k)]

private lemma p30_min_dist_le {d : ℕ} (r u : P30Vector d)
    (hmin : ∀ t : ℝ, p30VecNorm r ≤ p30VecNorm (fun i => r i + t * u i)) :
    p30VecNorm u ≤ p30VecNorm (fun i => r i + u i) := by
  have hor := p30_min_orth r u hmin
  have hs := p30_sqsum_add r u 1
  rw [← p30_norm_sq (fun i => r i + 1 * u i), ← p30_norm_sq r,
    ← p30_norm_sq u] at hs
  simp only [one_mul, one_pow] at hs
  have hn0 := p30_norm_nonneg u
  have hn1 := p30_norm_nonneg (fun i => r i + u i)
  nlinarith [sq_nonneg (p30VecNorm r)]

private lemma p30_tall_mix {m : ℕ} (H : P30TallMatrix m)
    (x y : P30Vector m) (t : ℝ) :
    p30_tall_matvec H (fun j => x j - t * (x j - y j)) =
      fun i => p30_tall_matvec H x i -
        t * (p30_tall_matvec H x i - p30_tall_matvec H y i) := by
  funext i
  simp only [p30_tall_matvec]
  calc
    (∑ j : Fin m, H i j * (x j - t * (x j - y j))) =
      ∑ j : Fin m, (H i j * x j - t * (H i j * x j - H i j * y j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

private lemma p30_tall_sub {m : ℕ} (H : P30TallMatrix m)
    (x y : P30Vector m) :
    p30_tall_matvec H (fun j => x j - y j) =
      fun i => p30_tall_matvec H x i - p30_tall_matvec H y i := by
  funext i
  simp only [p30_tall_matvec]
  simp only [mul_sub, Finset.sum_sub_distrib]

private lemma p30_basis_sub {n m : ℕ}
    (V : Fin n → Fin (m + 1) → ℝ) (x y : P30Vector (m + 1)) :
    p30_lemma51_basisMatVec V (fun i => x i - y i) =
      fun j => p30_lemma51_basisMatVec V x j - p30_lemma51_basisMatVec V y j := by
  funext j
  simp only [p30_lemma51_basisMatVec]
  simp only [mul_sub, Finset.sum_sub_distrib]

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
  let x : P30Vector m := fun j => y j - yprev k j
  let r : P30Vector (m + 1) := fun i =>
    (if i = 0 then β else 0) - p30_tall_matvec H y i
  let u : P30Vector (m + 1) := fun i =>
    p30_tall_matvec H y i - p30_tall_matvec H (yprev k) i
  have hmin : ∀ t : ℝ, p30VecNorm r ≤
      p30VecNorm (fun i => r i + t * u i) := by
    intro t
    let z : P30Vector m := fun j => y j - t * (y j - yprev k j)
    have hz := p30_tall_mix H y (yprev k) t
    have heq : (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H z i) =
        (fun i => r i + t * u i) := by
      funext i
      have hi := congrFun hz i
      change p30_tall_matvec H z i =
        p30_tall_matvec H y i -
          t * (p30_tall_matvec H y i - p30_tall_matvec H (yprev k) i) at hi
      dsimp [r, u]
      rw [hi]
      ring
    rw [← heq]
    exact hFullMin z
  have hdist := p30_min_dist_le r u hmin
  have hHu : p30_tall_matvec H x = u := by
    exact p30_tall_sub H y (yprev k)
  have hsx : sigma * p30VecNorm x ≤ p30VecNorm u := by
    simpa only [hHu] using hSigma x
  have hx : p30VecNorm x ≤ sigma⁻¹ * p30VecNorm u := by
    have hid : sigma⁻¹ * (sigma * p30VecNorm x) = p30VecNorm x := by
      field_simp
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hsx (le_of_lt (inv_pos.mpr hsigma))
  have hcoord : |y k| ≤ p30VecNorm x := by
    have hk := hYprevSupport k k (le_refl k.val)
    have hc := p30_coord_le_norm x k
    simpa only [x, hk, sub_zero] using hc
  have hru : (fun i => r i + u i) =
      (fun i : Fin (m + 1) =>
        (if i = 0 then β else 0) - p30_tall_matvec H (yprev k) i) := by
    funext i
    dsimp [r, u]
    ring
  have hres : p30VecNorm (fun i => r i + u i) =
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
    rw [hru, hr0]
    have hb := p30_basis_sub V
      (fun j : Fin (m + 1) => if j = 0 then β else 0)
      (p30_tall_matvec H (yprev k))
    rw [← hb]
    exact (hVisometry _).symm
  calc
    |y k| ≤ p30VecNorm x := hcoord
    _ ≤ sigma⁻¹ * p30VecNorm u := hx
    _ ≤ sigma⁻¹ * p30VecNorm (fun i => r i + u i) :=
      mul_le_mul_of_nonneg_left hdist (le_of_lt (inv_pos.mpr hsigma))
    _ = _ := by rw [hres]

end VSCLReuse

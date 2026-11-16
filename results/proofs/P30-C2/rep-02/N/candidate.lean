import VSCLReuse.P30.Definitions

namespace VSCLReuse

private lemma p30_norm_sq {d : ℕ} (x : P30Vector d) :
    p30VecNorm x ^ 2 = ∑ i : Fin d, x i ^ 2 := by
  unfold p30VecNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (x i))

private lemma p30_norm_nonneg {d : ℕ} (x : P30Vector d) :
    0 ≤ p30VecNorm x := by
  unfold p30VecNorm
  exact Real.sqrt_nonneg _

private lemma p30_coord_le_norm {d : ℕ} (x : P30Vector d) (k : Fin d) :
    |x k| ≤ p30VecNorm x := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin d => x i ^ 2)
    (fun i hi => sq_nonneg (x i)) (Finset.mem_univ k)
  have hnorm := p30_norm_sq x
  have hn := p30_norm_nonneg x
  have habs := abs_nonneg (x k)
  nlinarith [sq_abs (x k)]

private lemma p30_tall_linear {m : ℕ} (H : P30TallMatrix m)
    (x z : P30Vector m) (t : ℝ) (i : Fin (m + 1)) :
    p30_tall_matvec H (fun j => x j + t * z j) i =
      p30_tall_matvec H x i + t * p30_tall_matvec H z i := by
  simp [p30_tall_matvec, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm]

private lemma p30_tall_sub {m : ℕ} (H : P30TallMatrix m)
    (x z : P30Vector m) (i : Fin (m + 1)) :
    p30_tall_matvec H (fun j => x j - z j) i =
      p30_tall_matvec H x i - p30_tall_matvec H z i := by
  simp only [p30_tall_matvec, mul_sub, Finset.sum_sub_distrib]

private lemma p30_least_squares_orthogonal {m : ℕ} (H : P30TallMatrix m)
    (b : P30Vector (m + 1)) (y : P30Vector m)
    (hmin : ∀ z : P30Vector m,
      p30VecNorm (fun i => b i - p30_tall_matvec H y i) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H z i))
    (z : P30Vector m) :
    (∑ i : Fin (m + 1),
      (b i - p30_tall_matvec H y i) * p30_tall_matvec H z i) = 0 := by
  let S : ℝ := ∑ i : Fin (m + 1),
    (b i - p30_tall_matvec H y i) * p30_tall_matvec H z i
  let D : ℝ := ∑ i : Fin (m + 1), (p30_tall_matvec H z i) ^ 2
  have hD : 0 ≤ D := Finset.sum_nonneg fun i hi => sq_nonneg _
  have hexpand (t : ℝ) :
      (∑ i : Fin (m + 1),
        (b i - p30_tall_matvec H y i - t * p30_tall_matvec H z i) ^ 2) =
      (∑ i : Fin (m + 1), (b i - p30_tall_matvec H y i) ^ 2) +
        t ^ 2 * D - 2 * t * S := by
    calc
      _ = ∑ i : Fin (m + 1),
          ((b i - p30_tall_matvec H y i) ^ 2 +
          t ^ 2 * (p30_tall_matvec H z i) ^ 2 -
          2 * t * ((b i - p30_tall_matvec H y i) * p30_tall_matvec H z i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = _ := by
        simp [D, S, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * D - 2 * t * S := by
    have ht := hmin (fun j => y j + t * z j)
    have ht' := (sq_le_sq₀ (p30_norm_nonneg _) (p30_norm_nonneg _)).2 ht
    rw [p30_norm_sq, p30_norm_sq] at ht'
    simp_rw [p30_tall_linear] at ht'
    rw [show (∑ i : Fin (m + 1),
        (b i - (p30_tall_matvec H y i + t * p30_tall_matvec H z i)) ^ 2) =
        (∑ i : Fin (m + 1),
        (b i - p30_tall_matvec H y i - t * p30_tall_matvec H z i) ^ 2) from
        Finset.sum_congr rfl (fun i hi => by ring)] at ht'
    rw [hexpand] at ht'
    linarith
  have hden : D + 1 ≠ 0 := by linarith
  have hq := hquad (S / (D + 1))
  have hq' : 0 ≤ S ^ 2 * D - 2 * S ^ 2 * (D + 1) := by
    have hmul := mul_nonneg hq (sq_nonneg (D + 1))
    convert hmul using 1; field_simp
  have hSD : 0 ≤ S ^ 2 * D := mul_nonneg (sq_nonneg _) hD
  have hS : S = 0 := by nlinarith [sq_nonneg S]
  exact hS

private lemma p30_least_squares_distance {m : ℕ} (H : P30TallMatrix m)
    (b : P30Vector (m + 1)) (y : P30Vector m)
    (hmin : ∀ z : P30Vector m,
      p30VecNorm (fun i => b i - p30_tall_matvec H y i) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H z i))
    (z : P30Vector m) :
    p30VecNorm (p30_tall_matvec H (fun j => y j - z j)) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H z i) := by
  let d : P30Vector m := fun j => y j - z j
  have horth := p30_least_squares_orthogonal H b y hmin d
  have hres (i : Fin (m + 1)) :
      b i - p30_tall_matvec H z i =
        (b i - p30_tall_matvec H y i) + p30_tall_matvec H d i := by
    rw [show p30_tall_matvec H d i =
        p30_tall_matvec H y i - p30_tall_matvec H z i from
        p30_tall_sub H y z i]
    ring
  have hsum :
      (∑ i : Fin (m + 1), (b i - p30_tall_matvec H z i) ^ 2) =
      (∑ i : Fin (m + 1), (b i - p30_tall_matvec H y i) ^ 2) +
        ∑ i : Fin (m + 1), (p30_tall_matvec H d i) ^ 2 := by
    calc
      _ = ∑ i : Fin (m + 1),
          ((b i - p30_tall_matvec H y i) ^ 2 +
          (p30_tall_matvec H d i) ^ 2 +
          2 * (b i - p30_tall_matvec H y i) * p30_tall_matvec H d i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hres i]
            ring
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        have hc : (∑ i : Fin (m + 1),
            2 * (b i - p30_tall_matvec H y i) * p30_tall_matvec H d i) = 0 := by
          calc
            _ = 2 * (∑ i : Fin (m + 1),
                (b i - p30_tall_matvec H y i) * p30_tall_matvec H d i) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = 0 := by rw [horth]; ring
        rw [hc, add_zero]
  have hsq : p30VecNorm (p30_tall_matvec H d) ^ 2 ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H z i) ^ 2 := by
    rw [p30_norm_sq, p30_norm_sq, hsum]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun i hi => sq_nonneg _)
  exact (sq_le_sq₀ (p30_norm_nonneg _) (p30_norm_nonneg _)).1 hsq

private lemma p30_basis_sub {n m : ℕ}
    (V : Fin n → Fin (m + 1) → ℝ)
    (x z : P30Vector (m + 1)) (i : Fin n) :
    p30_lemma51_basisMatVec V (fun j => x j - z j) i =
      p30_lemma51_basisMatVec V x i - p30_lemma51_basisMatVec V z i := by
  simp [p30_lemma51_basisMatVec, mul_sub, Finset.sum_sub_distrib]

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
  let b : P30Vector (m + 1) := fun i => if i = 0 then β else 0
  let d : P30Vector m := fun j => y j - yprev k j
  have hkzero : yprev k k = 0 := hYprevSupport k k (le_refl _)
  have hcoord : |y k| ≤ p30VecNorm d := by
    have hc := p30_coord_le_norm d k
    simpa [d, hkzero] using hc
  have hdist : p30VecNorm (p30_tall_matvec H d) ≤
      p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) := by
    exact p30_least_squares_distance H b y hFullMin (yprev k)
  have hres :
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
      p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) := by
    have heq :
        (fun i : Fin n => r0 i -
          p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
        p30_lemma51_basisMatVec V
          (fun i => b i - p30_tall_matvec H (yprev k) i) := by
      funext i
      rw [hr0]
      exact (p30_basis_sub V b (p30_tall_matvec H (yprev k)) i).symm
    rw [heq, hVisometry]
  have hscale : p30VecNorm d ≤ sigma⁻¹ *
      p30VecNorm (fun i => b i - p30_tall_matvec H (yprev k) i) := by
    calc
      p30VecNorm d = sigma⁻¹ * (sigma * p30VecNorm d) := by
        field_simp
      _ ≤ sigma⁻¹ * p30VecNorm (p30_tall_matvec H d) := by
        exact mul_le_mul_of_nonneg_left (hSigma d) (le_of_lt (inv_pos.mpr hsigma))
      _ ≤ sigma⁻¹ * p30VecNorm
          (fun i => b i - p30_tall_matvec H (yprev k) i) := by
        exact mul_le_mul_of_nonneg_left hdist (le_of_lt (inv_pos.mpr hsigma))
  calc
    |y k| ≤ p30VecNorm d := hcoord
    _ ≤ sigma⁻¹ * p30VecNorm
      (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
        rw [hres]
        exact hscale

end VSCLReuse

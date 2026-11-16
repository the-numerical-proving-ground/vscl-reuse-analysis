import VSCLReuse.P30.Definitions

namespace VSCLReuse

private lemma p30_norm_sq {d : ℕ} (x : P30Vector d) :
    p30VecNorm x ^ 2 = ∑ i : Fin d, x i ^ 2 := by
  have h : 0 ≤ ∑ i : Fin d, x i ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg (x i))
  exact Real.sq_sqrt h

private lemma p30_norm_nonneg {d : ℕ} (x : P30Vector d) :
    0 ≤ p30VecNorm x := Real.sqrt_nonneg _

private lemma p30_tall_matvec_sub_smul {m : ℕ}
    (H : P30TallMatrix m) (x v : P30Vector m) (t : ℝ)
    (i : Fin (m + 1)) :
    p30_tall_matvec H (fun j => x j - t * v j) i =
      p30_tall_matvec H x i - t * p30_tall_matvec H v i := by
  simp only [p30_tall_matvec]
  calc
    (∑ j : Fin m, H i j * (x j - t * v j)) =
        ∑ j : Fin m, (H i j * x j - t * (H i j * v j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = (∑ j : Fin m, H i j * x j) -
        t * (∑ j : Fin m, H i j * v j) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]

private lemma p30_tall_matvec_sub {m : ℕ}
    (H : P30TallMatrix m) (x v : P30Vector m) (i : Fin (m + 1)) :
    p30_tall_matvec H (fun j => x j - v j) i =
      p30_tall_matvec H x i - p30_tall_matvec H v i := by
  simpa using p30_tall_matvec_sub_smul H x v 1 i

private lemma p30_basis_matvec_sub {n m : ℕ}
    (V : Fin n → Fin (m + 1) → ℝ)
    (x z : P30Vector (m + 1)) (i : Fin n) :
    p30_lemma51_basisMatVec V (fun j => x j - z j) i =
      p30_lemma51_basisMatVec V x i -
        p30_lemma51_basisMatVec V z i := by
  simp only [p30_lemma51_basisMatVec]
  calc
    (∑ j : Fin (m + 1), V i j * (x j - z j)) =
      ∑ j : Fin (m + 1), (V i j * x j - V i j * z j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = (∑ j : Fin (m + 1), V i j * x j) -
        (∑ j : Fin (m + 1), V i j * z j) := by
          rw [Finset.sum_sub_distrib]

private lemma p30_min_orthogonal {d : ℕ} (u v : P30Vector d)
    (h : ∀ t : ℝ, p30VecNorm u ≤
      p30VecNorm (fun i => u i + t * v i)) :
    (∑ i : Fin d, u i * v i) = 0 := by
  let B : ℝ := ∑ i : Fin d, v i ^ 2
  let C : ℝ := ∑ i : Fin d, u i * v i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => sq_nonneg (v i))
  have hq (t : ℝ) : 0 ≤ 2 * t * C + t ^ 2 * B := by
    have he : (∑ i : Fin d, (u i + t * v i) ^ 2) =
        (∑ i : Fin d, u i ^ 2) + 2 * t * C + t ^ 2 * B := by
      calc
        _ = ∑ i : Fin d,
            (u i ^ 2 + 2 * t * (u i * v i) + t ^ 2 * v i ^ 2) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          ring
    have hnorm := h t
    have hsquare := pow_le_pow_left₀ (p30_norm_nonneg u) hnorm 2
    rw [p30_norm_sq, p30_norm_sq] at hsquare
    rw [he] at hsquare
    dsimp [C, B] at hsquare ⊢
    linarith
  have hBp : 0 < B + 1 := by linarith
  have hq' := hq (-C / (B + 1))
  have hmul := mul_nonneg hq' (sq_nonneg (B + 1))
  have heq : (2 * (-C / (B + 1)) * C +
      (-C / (B + 1)) ^ 2 * B) * (B + 1) ^ 2 =
      -((B + 2) * C ^ 2) := by
    field_simp
    ring
  rw [heq] at hmul
  by_contra hC
  have hCp : 0 < C ^ 2 := sq_pos_of_ne_zero hC
  have hBp' : 0 < B + 2 := by linarith
  have hp := mul_pos hBp' hCp
  dsimp [C] at hC ⊢
  linarith

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
  let u : P30Vector (m + 1) := fun i => b i - p30_tall_matvec H y i
  let d : P30Vector m := fun j => y j - yprev k j
  let v : P30Vector (m + 1) := p30_tall_matvec H d
  let w : P30Vector (m + 1) :=
    fun i => b i - p30_tall_matvec H (yprev k) i
  have hmin : ∀ t : ℝ, p30VecNorm u ≤
      p30VecNorm (fun i => u i + t * v i) := by
    intro t
    let z : P30Vector m := fun j => y j - t * d j
    have hh := hFullMin z
    have heq : (fun i => u i + t * v i) =
        (fun i => b i - p30_tall_matvec H z i) := by
      funext i
      dsimp [u, v, z]
      rw [p30_tall_matvec_sub_smul]
      ring
    change p30VecNorm u ≤ p30VecNorm (fun i => b i - p30_tall_matvec H z i) at hh
    rw [← heq] at hh
    exact hh
  have hortho : (∑ i : Fin (m + 1), u i * v i) = 0 :=
    p30_min_orthogonal u v hmin
  have hw : ∀ i, w i = u i + v i := by
    intro i
    dsimp [w, u, v, d]
    rw [p30_tall_matvec_sub H y (yprev k) i]
    ring
  have hnorm_sq : p30VecNorm w ^ 2 =
      p30VecNorm u ^ 2 + p30VecNorm v ^ 2 := by
    rw [p30_norm_sq, p30_norm_sq, p30_norm_sq]
    calc
      (∑ i : Fin (m + 1), w i ^ 2) =
          ∑ i : Fin (m + 1), (u i + v i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hw]
      _ = (∑ i : Fin (m + 1), u i ^ 2) +
          (∑ i : Fin (m + 1), v i ^ 2) := by
            calc
              _ = ∑ i : Fin (m + 1),
                  (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
              _ = _ := by
                    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
                    rw [hortho]
                    ring
  have hv_le_w : p30VecNorm v ≤ p30VecNorm w := by
    have hu0 := p30_norm_nonneg u
    have hv0 := p30_norm_nonneg v
    have hw0 := p30_norm_nonneg w
    nlinarith [sq_nonneg (p30VecNorm u)]
  have hcoord : |y k| ≤ p30VecNorm d := by
    have hk : yprev k k = 0 := hYprevSupport k k (le_refl _)
    have hsq : d k ^ 2 ≤ ∑ j : Fin m, d j ^ 2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (d j)) (Finset.mem_univ k)
    have hnorm := p30_norm_sq d
    have hn := p30_norm_nonneg d
    dsimp [d] at hsq
    rw [hk, sub_zero] at hsq
    nlinarith [sq_nonneg (|y k|), sq_abs (y k)]
  have hbound : sigma * |y k| ≤ p30VecNorm w := by
    calc
      sigma * |y k| ≤ sigma * p30VecNorm d :=
        mul_le_mul_of_nonneg_left hcoord (le_of_lt hsigma)
      _ ≤ p30VecNorm v := hSigma d
      _ ≤ p30VecNorm w := hv_le_w
  have hres : p30VecNorm w =
      p30VecNorm (fun i : Fin n => r0 i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) := by
    rw [hr0]
    have hpoint : (fun i : Fin n =>
        p30_lemma51_basisMatVec V b i -
          p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i) =
        p30_lemma51_basisMatVec V w := by
      funext i
      rw [← p30_basis_matvec_sub V b (p30_tall_matvec H (yprev k)) i]
    change p30VecNorm w = p30VecNorm (fun i : Fin n =>
      p30_lemma51_basisMatVec V b i -
        p30_lemma51_basisMatVec V (p30_tall_matvec H (yprev k)) i)
    rw [hpoint, hVisometry]
  rw [← hres]
  calc
    |y k| = sigma⁻¹ * (sigma * |y k|) := by
      field_simp
    _ ≤ sigma⁻¹ * p30VecNorm w :=
      mul_le_mul_of_nonneg_left hbound (by positivity)

end VSCLReuse

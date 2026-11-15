import VSCLReuse.P30.Definitions

namespace VSCLReuse

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
  sorry

end VSCLReuse

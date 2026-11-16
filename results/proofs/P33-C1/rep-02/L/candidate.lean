import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

private lemma p33_run_support {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k, k ≤ n → ∀ j : Fin (n + 1), k < j.val → run.state k j = 0 := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rw [run.state_zero]
    simp [p33FirstBasis, Nat.ne_of_gt hj]
  | succ k ih =>
    intro hk j hj
    have hkn : k < n := by omega
    rw [run.state_succ k hkn]
    have hne₁ : j ≠ (⟨k, hkn⟩ : Fin n).castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    have hne₂ : j ≠ (⟨k, hkn⟩ : Fin n).succ := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp only [p33AdjointCoreStep]
    split_ifs <;> simp_all
    exact ih (by omega) j (by omega)

private lemma p33_run_diagonal {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k (hk : k ≤ n),
      run.state k ⟨k, by omega⟩ =
        ∏ j ∈ Finset.range k, star (p33CoreCoeff run.v j) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [run.state_zero, p33FirstBasis]
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hzero : run.state k (⟨k, hkn⟩ : Fin n).succ = 0 :=
      p33_run_support run k (by omega) _ (by simp)
    rw [run.state_succ k hkn]
    simp only [p33AdjointCoreStep]
    have hne : (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠
        (⟨k, hkn⟩ : Fin n).castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
    have heq : (⟨k + 1, by omega⟩ : Fin (n + 1)) =
        (⟨k, hkn⟩ : Fin n).succ := by
      apply Fin.ext
      simp
    simp only [if_neg hne, if_pos heq]
    rw [hzero, mul_zero, add_zero]
    rw [Finset.prod_range_succ, ← ih (by omega)]
    simp only [p33CoreCoeff, dif_pos hkn]
    ac_rfl

/-- P33-C1: the subdiagonal product and nontriviality result of Theorem 4.5. -/
theorem p33_c1_core_subdiagonal_product
    (n : ℕ) (hn : 0 < n) (run : P33CoreRollupRun n)
    (x : P33Vector n) (alpha a0 : ℂ)
    (hx : x = alpha • run.state n)
    (hxlast : x ⟨n, by omega⟩ = -1)
    (halpha : ‖alpha‖ = p33VecNorm2 x)
    (hvw : ∀ i, ‖run.v i‖ = ‖run.w i‖)
    (Ctail Rtail Htail : P33Matrix n)
    (hCdiag : ∀ i, Ctail i i = run.w i)
    (hCtri : Ctail.BlockTriangular id)
    (hRtri : Rtail.BlockTriangular id)
    (hHtail : Htail = Ctail * Rtail)
    (hdetR : ‖Matrix.det Rtail‖ = ‖a0‖)
    (ha0 : a0 ≠ 0) :
    (∀ i, 0 < ‖Htail i i‖) ∧
      (∏ i, ‖Htail i i‖) = ‖a0‖ / p33VecNorm2 x := by
  -- PROOF_START P33-C1-H001
  have hstate : run.state n ⟨n, by omega⟩ = ∏ i, star (run.v i) := by
    have h := p33_run_diagonal run n le_rfl
    rw [← Fin.prod_univ_eq_prod_range] at h
    simpa [p33CoreCoeff] using h
  have hlast : (-1 : ℂ) = alpha * ∏ i, star (run.v i) := by
    calc
      (-1 : ℂ) = x ⟨n, by omega⟩ := hxlast.symm
      _ = alpha * ∏ i, star (run.v i) := by
        rw [hx]
        simpa only [Pi.smul_apply, smul_eq_mul] using congrArg (alpha * ·) hstate
  have hnorm : (1 : ℝ) = ‖alpha‖ * ∏ i, ‖run.w i‖ := by
    have h := congrArg norm hlast
    simpa [norm_mul, norm_prod, hvw] using h
  have hanorm : ‖alpha‖ ≠ 0 := by
    intro h
    rw [h] at hnorm
    norm_num at hnorm
  have hvecpos : 0 < p33VecNorm2 x := by
    rw [← halpha]
    exact lt_of_le_of_ne (norm_nonneg alpha) (Ne.symm hanorm)
  have hprodW : (∏ i, ‖run.w i‖) = 1 / p33VecNorm2 x := by
    rw [eq_div_iff (ne_of_gt hvecpos)]
    rw [← halpha]
    nlinarith [hnorm]
  have hHtri : Htail.BlockTriangular id := by
    rw [hHtail]
    exact hCtri.mul hRtri
  have hHprod : (∏ i, ‖Htail i i‖) = (∏ i, ‖run.w i‖) * ‖a0‖ := by
    calc
      (∏ i, ‖Htail i i‖) = ‖∏ i, Htail i i‖ := by simp only [norm_prod]
      _ = ‖Matrix.det Htail‖ := by rw [Matrix.det_of_upperTriangular hHtri]
      _ = ‖Matrix.det Ctail‖ * ‖Matrix.det Rtail‖ := by
        rw [hHtail, Matrix.det_mul, norm_mul]
      _ = (∏ i, ‖run.w i‖) * ‖a0‖ := by
        rw [Matrix.det_of_upperTriangular hCtri, hdetR]
        simp only [norm_prod]
        simp_rw [hCdiag]
  have hfinal : (∏ i, ‖Htail i i‖) = ‖a0‖ / p33VecNorm2 x := by
    rw [hHprod, hprodW]
    simp [div_eq_mul_inv, mul_comm]
  have hfinal_ne : (∏ i, ‖Htail i i‖) ≠ 0 := by
    rw [hfinal]
    exact div_ne_zero (by simpa using ha0) (ne_of_gt hvecpos)
  constructor
  · intro i
    have hi : ‖Htail i i‖ ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hfinal_ne) i (Finset.mem_univ i)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi)
  · exact hfinal

end VSCLReuse

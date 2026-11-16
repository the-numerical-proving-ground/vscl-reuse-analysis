import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p33_rollup_coordinate {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k (hk : k ≤ n),
      run.state k ⟨k, by omega⟩ =
        ∏ j ∈ Finset.range k, star (p33CoreCoeff run.v j) ∧
      ∀ j : Fin (n + 1), k < j.val → run.state k j = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk
      constructor
      · simp [run.state_zero, p33FirstBasis]
      · intro j hj
        simp [run.state_zero, p33FirstBasis, Nat.ne_of_gt hj]
  | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      obtain ⟨hcoord, hzero⟩ := ih (by omega)
      have hnext : run.state k ⟨k + 1, by omega⟩ = 0 :=
        hzero _ (by simp)
      constructor
      · rw [run.state_succ k hk]
        simp only [p33AdjointCoreStep]
        simp only [Finset.prod_range_succ]
        simp [hnext, hcoord, p33CoreCoeff, hk, mul_comm]
      · intro j hj
        rw [run.state_succ k hk]
        simp only [p33AdjointCoreStep]
        split_ifs with h1 h2
        · have hv := congrArg Fin.val h1
          simp at hv
          omega
        · have hv := congrArg Fin.val h2
          simp at hv
          omega
        · exact hzero j (by omega)

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
  have hcoord := (p33_rollup_coordinate run n le_rfl).1
  have hlast : (-1 : ℂ) = alpha *
      (∏ j ∈ Finset.range n, star (p33CoreCoeff run.v j)) := by
    rw [hx] at hxlast
    simpa [Pi.smul_apply, smul_eq_mul, hcoord] using hxlast.symm
  have hlast_norm : 1 = ‖alpha‖ * (∏ i : Fin n, ‖run.v i‖) := by
    have hh := congrArg norm hlast
    simp only [norm_neg, norm_one, norm_mul, norm_prod, norm_star] at hh
    rw [Finset.prod_range] at hh
    simpa [p33CoreCoeff] using hh
  have hprodC : (∏ i : Fin n, ‖run.w i‖) * p33VecNorm2 x = 1 := by
    rw [← halpha]
    simp_rw [← hvw]
    simpa [mul_comm] using hlast_norm.symm
  have hnormxne : p33VecNorm2 x ≠ 0 := by
    intro heq
    rw [heq, mul_zero] at hprodC
    norm_num at hprodC
  have hHtri : Htail.BlockTriangular id := by
    rw [hHtail]
    exact hCtri.mul hRtri
  have hdetC : ‖Matrix.det Ctail‖ = ∏ i : Fin n, ‖run.w i‖ := by
    rw [Matrix.det_of_upperTriangular hCtri, norm_prod]
    simp_rw [hCdiag]
  have hdetH : ‖Matrix.det Htail‖ = ∏ i : Fin n, ‖Htail i i‖ := by
    rw [Matrix.det_of_upperTriangular hHtri, norm_prod]
  have hprodHdet : (∏ i : Fin n, ‖Htail i i‖) =
      (∏ i : Fin n, ‖run.w i‖) * ‖a0‖ := by
    calc
      (∏ i : Fin n, ‖Htail i i‖) = ‖Matrix.det Htail‖ := hdetH.symm
      _ = (∏ i : Fin n, ‖run.w i‖) * ‖a0‖ := by
        rw [hHtail, Matrix.det_mul, norm_mul, hdetC, hdetR]
  have hprodH : (∏ i : Fin n, ‖Htail i i‖) = ‖a0‖ / p33VecNorm2 x := by
    apply (eq_div_iff hnormxne).2
    rw [hprodHdet]
    calc
      (∏ i : Fin n, ‖run.w i‖) * ‖a0‖ * p33VecNorm2 x =
          ((∏ i : Fin n, ‖run.w i‖) * p33VecNorm2 x) * ‖a0‖ := by ring
      _ = ‖a0‖ := by rw [hprodC, one_mul]
  have hprodHne : (∏ i : Fin n, ‖Htail i i‖) ≠ 0 := by
    rw [hprodH]
    exact div_ne_zero (norm_ne_zero_iff.mpr ha0) hnormxne
  constructor
  · intro i
    have hi : ‖Htail i i‖ ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprodHne) i (Finset.mem_univ i)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi)
  · exact hprodH

end VSCLReuse

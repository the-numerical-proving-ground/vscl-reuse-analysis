import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p33_rollup_coordinate (n : ℕ) (run : P33CoreRollupRun n) :
    ∀ k (hk : k ≤ n),
      (∀ j : Fin (n + 1), k < j.val → run.state k j = 0) ∧
      run.state k ⟨k, Nat.lt_succ_of_le hk⟩ =
        ∏ t ∈ Finset.range k, star (p33CoreCoeff run.v t) := by
  intro k
  induction k with
  | zero =>
      intro hk
      constructor
      · intro j hj
        rw [run.state_zero]
        simp [p33FirstBasis, Nat.ne_of_gt hj]
      · rw [run.state_zero]
        simp [p33FirstBasis]
  | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      obtain ⟨hsupport, hcoord⟩ := ih (Nat.le_of_lt hkn)
      constructor
      · intro j hj
        rw [run.state_succ k hkn]
        have hji : j ≠ (⟨k, hkn⟩ : Fin n).castSucc := by
          intro h
          have : j.val = k := congrArg Fin.val h
          omega
        have hjs : j ≠ (⟨k, hkn⟩ : Fin n).succ := by
          intro h
          have : j.val = k + 1 := congrArg Fin.val h
          omega
        simp only [p33AdjointCoreStep, if_neg hji, if_neg hjs]
        exact hsupport j (by omega)
      · rw [run.state_succ k hkn]
        have hneq : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) ≠
            (⟨k, hkn⟩ : Fin n).castSucc := by
          intro h
          have : k + 1 = k := congrArg Fin.val h
          omega
        have heq : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) =
            (⟨k, hkn⟩ : Fin n).succ := by
          apply Fin.ext
          rfl
        simp only [p33AdjointCoreStep, if_neg hneq, if_pos heq]
        have hnext' : run.state k (⟨k, hkn⟩ : Fin n).succ = 0 :=
          hsupport _ (by simp)
        have hcoord' : run.state k (⟨k, hkn⟩ : Fin n).castSucc =
            ∏ t ∈ Finset.range k, star (p33CoreCoeff run.v t) := by
          simpa using hcoord
        rw [hnext', mul_zero, add_zero, hcoord', Finset.prod_range_succ]
        simp [p33CoreCoeff, hkn, mul_comm]

private theorem p33_rollup_last (n : ℕ) (run : P33CoreRollupRun n) :
    run.state n ⟨n, by omega⟩ = ∏ i, star (run.v i) := by
  have h := (p33_rollup_coordinate n run n le_rfl).2
  rw [← Fin.prod_univ_eq_prod_range] at h
  simpa [p33CoreCoeff] using h

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
  have hlast : alpha * (∏ i, star (run.v i)) = -1 := by
    rw [hx] at hxlast
    simpa [Pi.smul_apply, smul_eq_mul, p33_rollup_last] using hxlast
  have halpha_ne : alpha ≠ 0 := by
    intro h
    simp [h] at hlast
  have hxpos : 0 < p33VecNorm2 x := by
    rw [← halpha]
    exact norm_pos_iff.mpr halpha_ne
  have hWprod_one : ‖alpha‖ * (∏ i, ‖run.w i‖) = 1 := by
    have h := congrArg norm hlast
    simp only [norm_mul, norm_prod, norm_star, norm_neg, norm_one] at h
    simpa only [← hvw] using h
  have hWprod : (∏ i, ‖run.w i‖) = 1 / p33VecNorm2 x := by
    apply (eq_div_iff (ne_of_gt hxpos)).2
    rw [← halpha]
    simpa only [mul_comm] using hWprod_one
  have hdiag : ∀ i, Htail i i = Ctail i i * Rtail i i := by
    intro i
    rw [hHtail, Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rcases lt_trichotomy j i with h | h | h
      · simp [hCtri h]
      · exact (hji h).elim
      · simp [hRtri h]
    · simp
  have hRprod : (∏ i, ‖Rtail i i‖) = ‖a0‖ := by
    rw [Matrix.det_of_upperTriangular hRtri, norm_prod] at hdetR
    exact hdetR
  have hWprod_ne : (∏ i, ‖run.w i‖) ≠ 0 := by
    rw [hWprod]
    positivity
  have hRprod_ne : (∏ i, ‖Rtail i i‖) ≠ 0 := by
    rw [hRprod]
    exact norm_ne_zero_iff.mpr ha0
  have hWpos (i : Fin n) : 0 < ‖run.w i‖ := by
    have hi : ‖run.w i‖ ≠ 0 := by
      intro h
      exact hWprod_ne (Finset.prod_eq_zero (Finset.mem_univ i) h)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi)
  have hRpos (i : Fin n) : 0 < ‖Rtail i i‖ := by
    have hi : ‖Rtail i i‖ ≠ 0 := by
      intro h
      exact hRprod_ne (Finset.prod_eq_zero (Finset.mem_univ i) h)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hi)
  constructor
  · intro i
    rw [hdiag i, hCdiag i, norm_mul]
    exact mul_pos (hWpos i) (hRpos i)
  · calc
      (∏ i, ‖Htail i i‖) = ∏ i, ‖run.w i‖ * ‖Rtail i i‖ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hdiag i, hCdiag i, norm_mul]
      _ = (∏ i, ‖run.w i‖) * (∏ i, ‖Rtail i i‖) :=
        Finset.prod_mul_distrib
      _ = ‖a0‖ / p33VecNorm2 x := by
        rw [hWprod, hRprod]
        ring

end VSCLReuse

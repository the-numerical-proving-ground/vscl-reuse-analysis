import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

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
  have hrun : ∀ k (hk : k ≤ n),
      (∀ j : Fin (n + 1), k < j.val → run.state k j = 0) ∧
      (run.state k ⟨k, Nat.lt_succ_of_le hk⟩ =
        ∏ j ∈ Finset.range k, star (p33CoreCoeff run.v j)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      constructor
      · intro j hj
        rw [run.state_zero]
        have hj0 : j.val ≠ 0 := by omega
        simp [p33FirstBasis, hj0]
      · simp [run.state_zero, p33FirstBasis]
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      obtain ⟨hsupp, hfront⟩ := ih (by omega)
      let i : Fin n := ⟨k, hk⟩
      have hne : i.succ ≠ i.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp [i] at hv
      constructor
      · intro j hj
        rw [run.state_succ k hk]
        have hj1 : j ≠ i.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp [i] at hv
          omega
        have hj2 : j ≠ i.succ := by
          intro h
          have hv := congrArg Fin.val h
          simp [i] at hv
          omega
        dsimp [i] at hj1 hj2
        simp [p33AdjointCoreStep, hj1, hj2]
        exact hsupp j (by omega)
      · rw [run.state_succ k hk]
        change p33AdjointCoreStep i (run.u i) (run.v i) (run.w i)
          (run.z i) (run.state k) i.succ = _
        simp only [p33AdjointCoreStep, if_neg hne]
        have hz : run.state k i.succ = 0 := hsupp i.succ (by simp [i])
        rw [hz, mul_zero, add_zero]
        change star (run.v i) *
          run.state k ⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hk)⟩ =
          ∏ j ∈ Finset.range (k + 1), star (p33CoreCoeff run.v j)
        rw [hfront, Finset.prod_range_succ]
        simp [p33CoreCoeff, hk, i, mul_comm]
  have hfrontlast : run.state n ⟨n, by omega⟩ =
      ∏ i : Fin n, star (run.v i) := by
    rw [(hrun n le_rfl).2]
    rw [← Fin.prod_univ_eq_prod_range]
    simp [p33CoreCoeff]
  have hlast : alpha * (∏ i : Fin n, star (run.v i)) = -1 := by
    rw [hx, Pi.smul_apply, smul_eq_mul, hfrontlast] at hxlast
    exact hxlast
  have hcore_mul : ‖alpha‖ * (∏ i : Fin n, ‖run.v i‖) = 1 := by
    have h := congrArg norm hlast
    simpa [norm_mul, norm_prod] using h
  have halpha0 : ‖alpha‖ ≠ 0 := by
    intro h
    rw [h] at hcore_mul
    norm_num at hcore_mul
  have hcore : (∏ i : Fin n, ‖run.w i‖) = 1 / p33VecNorm2 x := by
    have hp : (∏ i : Fin n, ‖run.w i‖) = ∏ i : Fin n, ‖run.v i‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hvw i).symm
    rw [hp, ← halpha]
    apply (eq_div_iff halpha0).2
    simpa [mul_comm] using hcore_mul
  have hdiag (i : Fin n) : Htail i i = Ctail i i * Rtail i i := by
    classical
    rw [hHtail, Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro j hj hji
      rcases lt_trichotomy j i with hlt | heq | hgt
      · simp [hCtri hlt]
      · exact (hji heq).elim
      · simp [hRtri hgt]
    · simp
  have hRprod : (∏ i : Fin n, ‖Rtail i i‖) = ‖a0‖ := by
    calc
      (∏ i : Fin n, ‖Rtail i i‖) = ‖∏ i : Fin n, Rtail i i‖ := by
        simp only [norm_prod]
      _ = ‖Matrix.det Rtail‖ := by rw [Matrix.det_of_upperTriangular hRtri]
      _ = ‖a0‖ := hdetR
  have hHprod : (∏ i : Fin n, ‖Htail i i‖) =
      (∏ i : Fin n, ‖run.w i‖) * (∏ i : Fin n, ‖Rtail i i‖) := by
    calc
      (∏ i : Fin n, ‖Htail i i‖) =
          ∏ i : Fin n, ‖run.w i‖ * ‖Rtail i i‖ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hdiag i, hCdiag i, norm_mul]
      _ = _ := Finset.prod_mul_distrib
  have hnormx0 : p33VecNorm2 x ≠ 0 := by
    rw [← halpha]
    exact halpha0
  have hHnz : (∏ i : Fin n, ‖Htail i i‖) ≠ 0 := by
    rw [hHprod, hcore, hRprod]
    simp [ha0, hnormx0]
  constructor
  · intro i
    have hi : ‖Htail i i‖ ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hHnz) i (Finset.mem_univ i)
    rcases lt_or_eq_of_le (norm_nonneg (Htail i i)) with h | h
    · exact h
    · exact (hi h.symm).elim
  · rw [hHprod, hcore, hRprod]
    simp [div_eq_mul_inv, mul_comm]

end VSCLReuse

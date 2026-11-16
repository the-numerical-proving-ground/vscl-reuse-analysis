import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p33_run_support {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k, k ≤ n → ∀ j : Fin (n + 1), k < j.val → run.state k j = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk j hj
      rw [run.state_zero]
      simp [p33FirstBasis, Nat.ne_of_gt hj]
  | succ k ih =>
      intro hk j hj
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hne₁ : j ≠ i.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp [i] at hv
        omega
      have hne₂ : j ≠ i.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp [i] at hv
        omega
      rw [run.state_succ k hkn]
      change p33AdjointCoreStep i (run.u i) (run.v i) (run.w i) (run.z i)
        (run.state k) j = 0
      unfold p33AdjointCoreStep
      rw [if_neg hne₁, if_neg hne₂]
      exact ih (by omega) j (by omega)

private theorem p33_run_coordinate {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k, (hk : k ≤ n) → ∀ j : Fin (n + 1), j.val = k →
      run.state k j = ∏ t ∈ Finset.range k, star (p33CoreCoeff run.v t) := by
  intro k
  induction k with
  | zero =>
      intro hk j hj
      rw [run.state_zero]
      simp [p33FirstBasis, hj]
  | succ k ih =>
      intro hk j hj
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hji : j = i.succ := by
        apply Fin.ext
        simpa [i] using hj
      subst j
      have hzero : run.state k i.succ = 0 :=
        p33_run_support run k (by omega) i.succ (by simp [i])
      have hprev : run.state k i.castSucc =
          ∏ t ∈ Finset.range k, star (p33CoreCoeff run.v t) :=
        ih (by omega) i.castSucc (by simp [i])
      rw [run.state_succ k hkn]
      change p33AdjointCoreStep i (run.u i) (run.v i) (run.w i) (run.z i)
        (run.state k) i.succ = _
      have hne : i.succ ≠ i.castSucc := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
      unfold p33AdjointCoreStep
      rw [if_neg hne, if_pos rfl]
      rw [hzero, mul_zero, add_zero, hprev, Finset.prod_range_succ]
      simp [p33CoreCoeff, hkn, i, mul_comm]

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
  have hlast : x ⟨n, by omega⟩ =
      alpha * (∏ t ∈ Finset.range n, star (p33CoreCoeff run.v t)) := by
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [p33_run_coordinate run n le_rfl ⟨n, by omega⟩ rfl]
  have hnormprod : 1 = ‖alpha‖ * ∏ i : Fin n, ‖run.v i‖ := by
    have hh := congrArg norm hlast
    simp only [hxlast, norm_neg, norm_one, norm_mul, norm_prod, norm_star] at hh
    have hrange : (∏ t ∈ Finset.range n, ‖p33CoreCoeff run.v t‖) =
        ∏ i : Fin n, ‖run.v i‖ := by
      rw [← Fin.prod_univ_eq_prod_range (fun t : ℕ => ‖p33CoreCoeff run.v t‖) n]
      simp [p33CoreCoeff]
    simpa [hrange] using hh
  have hαne : ‖alpha‖ ≠ 0 := by
    intro he
    simp [he] at hnormprod
  have hwprod : (∏ i : Fin n, ‖run.w i‖) = 1 / p33VecNorm2 x := by
    have hvprod : (∏ i : Fin n, ‖run.v i‖) = 1 / ‖alpha‖ := by
      apply (eq_div_iff hαne).2
      simpa [mul_comm] using hnormprod.symm
    simpa [← halpha, ← hvw] using hvprod
  have hdiag (i : Fin n) : Htail i i = Ctail i i * Rtail i i := by
    rw [hHtail, Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro j hj hji
      rcases lt_trichotomy j i with h | h | h
      · simp [hCtri h]
      · exact (hji h).elim
      · simp [hRtri h]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hRprod : (∏ i : Fin n, ‖Rtail i i‖) = ‖a0‖ := by
    calc
      (∏ i : Fin n, ‖Rtail i i‖) = ‖∏ i : Fin n, Rtail i i‖ := by
        rw [norm_prod]
      _ = ‖Matrix.det Rtail‖ := by rw [Matrix.det_of_upperTriangular hRtri]
      _ = ‖a0‖ := hdetR
  have hHprod : (∏ i : Fin n, ‖Htail i i‖) = ‖a0‖ / p33VecNorm2 x := by
    calc
      (∏ i : Fin n, ‖Htail i i‖) =
          (∏ i : Fin n, ‖run.w i‖) * (∏ i : Fin n, ‖Rtail i i‖) := by
        simp_rw [hdiag, norm_mul, hCdiag]
        exact Finset.prod_mul_distrib
      _ = (1 / p33VecNorm2 x) * ‖a0‖ := by rw [hwprod, hRprod]
      _ = ‖a0‖ / p33VecNorm2 x := by ring
  have hHprod_ne : (∏ i : Fin n, ‖Htail i i‖) ≠ 0 := by
    rw [hHprod]
    apply div_ne_zero (norm_ne_zero_iff.mpr ha0)
    rw [← halpha]
    exact hαne
  constructor
  · intro i
    have hne : ‖Htail i i‖ ≠ 0 := by
      intro he
      exact hHprod_ne (Finset.prod_eq_zero (Finset.mem_univ i) he)
    exact lt_of_le_of_ne (norm_nonneg _) hne.symm
  · exact hHprod

end VSCLReuse

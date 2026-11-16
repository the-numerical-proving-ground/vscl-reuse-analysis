import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

private theorem p33_state_tail_zero {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k, k ≤ n → ∀ j : Fin (n + 1), k < j.val → run.state k j = 0 := by
  intro k
  induction k with
  | zero =>
      intro hk j hj
      rw [run.state_zero]
      have hj0 : j ≠ 0 := by
        intro he
        subst j
        simp at hj
      simpa [p33FirstBasis, hj0]
  | succ k ih =>
      intro hk j hj
      have hk' : k < n := by omega
      rw [run.state_succ k hk']
      have h1 : j ≠ (⟨k, hk'⟩ : Fin n).castSucc := by
        intro he
        subst j
        simp only [Fin.val_castSucc] at hj
        omega
      have h2 : j ≠ (⟨k, hk'⟩ : Fin n).succ := by
        intro he
        subst j
        simp only [Fin.val_succ] at hj
        omega
      unfold p33AdjointCoreStep
      simp only [h1, h2, ite_false]
      exact ih (by omega) j (by omega)

private theorem p33_state_froncategory_norm {n : ℕ} (run : P33CoreRollupRun n) :
    ∀ k (hk : k ≤ n),
      ‖run.state k ⟨k, by omega⟩‖ =
        ∏ i ∈ Finset.range k, ‖p33CoreCoeff run.v i‖ := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [run.state_zero]
      simp [p33FirstBasis]
  | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hzero := p33_state_tail_zero run k (by omega)
        (⟨k + 1, by omega⟩ : Fin (n + 1)) (by simp)
      rw [run.state_succ k hk']
      have hne : (⟨k + 1, by omega⟩ : Fin (n + 1)) ≠
          (⟨k, hk'⟩ : Fin n).castSucc := by
        intro he
        have := congrArg Fin.val he
        simp at this
      have heq : (⟨k + 1, by omega⟩ : Fin (n + 1)) =
          (⟨k, hk'⟩ : Fin n).succ := by
        apply Fin.ext
        rfl
      have hzero' : run.state k (⟨k, hk'⟩ : Fin n).succ = 0 := by
        rw [← heq]
        exact hzero
      have hne' : (⟨k, hk'⟩ : Fin n).succ ≠
          (⟨k, hk'⟩ : Fin n).castSucc := by
        intro he
        have := congrArg Fin.val he
        simp at this
      change ‖p33AdjointCoreStep (⟨k, hk'⟩ : Fin n)
          (run.u ⟨k, hk'⟩) (run.v ⟨k, hk'⟩)
          (run.w ⟨k, hk'⟩) (run.z ⟨k, hk'⟩)
          (run.state k) (⟨k + 1, by omega⟩ : Fin (n + 1))‖ = _
      unfold p33AdjointCoreStep
      simp only [heq, hne', ite_false, ite_true]
      rw [hzero', mul_zero, add_zero, norm_mul, norm_star]
      rw [Finset.prod_range_succ, ← ih (by omega)]
      simp [p33CoreCoeff, hk', mul_comm]

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
  have hfinprod : (∏ i : Fin n, ‖run.v i‖) =
      ∏ i ∈ Finset.range n, ‖p33CoreCoeff run.v i‖ := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [p33CoreCoeff, hin]
  have hlastnorm : ‖x (⟨n, by omega⟩ : Fin (n + 1))‖ = 1 := by
    rw [hxlast]
    simp
  have hcoreprod : ‖alpha‖ * (∏ i : Fin n, ‖run.v i‖) = 1 := by
    calc
      ‖alpha‖ * (∏ i : Fin n, ‖run.v i‖) =
          ‖alpha‖ * ‖run.state n (⟨n, by omega⟩ : Fin (n + 1))‖ := by
            rw [p33_state_froncategory_norm run n le_rfl, ← hfinprod]
      _ = ‖x (⟨n, by omega⟩ : Fin (n + 1))‖ := by
        rw [hx]
        simp [Pi.smul_apply, smul_eq_mul, norm_mul]
      _ = 1 := hlastnorm
  have halpha0 : ‖alpha‖ ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at hcoreprod
    norm_num at hcoreprod
  have hnormpos : 0 < p33VecNorm2 x := by
    rw [← halpha]
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm halpha0)
  have hwprod : (∏ i : Fin n, ‖run.w i‖) = 1 / p33VecNorm2 x := by
    rw [← halpha]
    apply (eq_div_iff halpha0).2
    have hprodvw : (∏ i : Fin n, ‖run.v i‖) =
        ∏ i : Fin n, ‖run.w i‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hvw i
    rw [hprodvw] at hcoreprod
    calc
      (∏ i : Fin n, ‖run.w i‖) * ‖alpha‖ =
          ‖alpha‖ * (∏ i : Fin n, ‖run.w i‖) := mul_comm _ _
      _ = 1 := hcoreprod
  have hdiag (i : Fin n) : Htail i i = Ctail i i * Rtail i i := by
    rw [hHtail, Matrix.mul_apply]
    apply Finset.sum_eq_single i
    · intro j hj hji
      rcases lt_trichotomy j i with hlt | heq | hgt
      · rw [hCtri hlt, zero_mul]
      · exact (hji heq).elim
      · rw [hRtri hgt, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hRprod : (∏ i : Fin n, ‖Rtail i i‖) = ‖a0‖ := by
    calc
      (∏ i : Fin n, ‖Rtail i i‖) = ‖∏ i : Fin n, Rtail i i‖ := by
        rw [norm_prod]
      _ = ‖Matrix.det Rtail‖ := by
        rw [Matrix.det_of_upperTriangular hRtri]
      _ = ‖a0‖ := hdetR
  have hHprod : (∏ i : Fin n, ‖Htail i i‖) =
      ‖a0‖ / p33VecNorm2 x := by
    calc
      (∏ i : Fin n, ‖Htail i i‖) =
          ∏ i : Fin n, (‖run.w i‖ * ‖Rtail i i‖) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hdiag i, hCdiag i, norm_mul]
      _ = (∏ i : Fin n, ‖run.w i‖) *
          (∏ i : Fin n, ‖Rtail i i‖) := Finset.prod_mul_distrib
      _ = ‖a0‖ / p33VecNorm2 x := by
        rw [hwprod, hRprod]
        ring
  constructor
  · intro i
    have hfullpos : 0 < ∏ j : Fin n, ‖Htail j j‖ := by
      rw [hHprod]
      exact div_pos (norm_pos_iff.mpr ha0) hnormpos
    have hnone : ‖Htail i i‖ ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp (ne_of_gt hfullpos)) i (Finset.mem_univ i)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnone)
  · exact hHprod

end VSCLReuse

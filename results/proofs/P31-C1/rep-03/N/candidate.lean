import VSCLReuse.P31.Definitions

namespace VSCLReuse

private theorem p31_mem_laurent {n : ℕ} (v : ℤ → Fin n → ℝ)
    (k : ℕ) (j : ℤ) (hj₁ : -(k : ℤ) ≤ j) (hj₂ : j < (k : ℤ)) :
    v j ∈ p31LaurentSpan v k := by
  apply Submodule.subset_span
  exact ⟨j, ⟨hj₁, hj₂⟩, rfl⟩

/-- P31-C1: the invariant-subspace conclusion of Proposition 3.4. -/
theorem p31_c1_rank_breakdown_invariant
    (n m : ℕ) (hm : 1 ≤ m)
    (v : ℤ → Fin n → ℝ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1))
    (hbreak : ¬ LinearIndependent ℝ (p31BreakdownDirections v m)) :
    ∀ x ∈ p31LaurentSpan v (m + 1),
      A x ∈ p31LaurentSpan v (m + 1) := by
  -- PROOF_START P31-C1-H001
  let W : Submodule ℝ (Fin n → ℝ) := p31LaurentSpan v (m + 1)
  let P : Submodule ℝ (Fin n → ℝ) := p31LaurentSpan v m
  let AW : Submodule ℝ (Fin n → ℝ) := W.map A.toLinearMap
  have hW (j : ℤ) (hl : -((m + 1 : ℕ) : ℤ) ≤ j)
      (hu : j < ((m + 1 : ℕ) : ℤ)) : v j ∈ W :=
    p31_mem_laurent v (m + 1) j hl hu
  have hstep_prev (j : ℤ) : A (v (j - 1)) = v j := by
    simpa only [sub_add_cancel] using hstep (j - 1)
  have hgenAW (j : ℤ) (hl : -(m : ℤ) ≤ j) (hu : j ≤ (m : ℤ)) :
      v j ∈ AW := by
    change v j ∈ W.map A.toLinearMap
    apply Submodule.mem_map.mpr
    refine ⟨v (j - 1), hW (j - 1) (by omega) (by omega), ?_⟩
    exact hstep_prev j
  have hP_le_AW : P ≤ AW := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    rcases hj with ⟨hjl, hju⟩
    exact hgenAW j hjl (by omega)
  have hW_invariant_of_pos (hp : v (m : ℤ) ∈ P) :
      ∀ x ∈ W, A x ∈ W := by
    have hP_to_W : P ≤ W.comap A.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rcases hj with ⟨hjl, hju⟩
      change A (v j) ∈ W
      rw [hstep j]
      exact hW (j + 1) (by omega) (by omega)
    have hnext : v ((m : ℤ) + 1) ∈ W := by
      have hh := hP_to_W hp
      change A (v (m : ℤ)) ∈ W at hh
      simpa only [hstep] using hh
    intro x hx
    have hmap : W ≤ W.comap A.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rcases hj with ⟨hjl, hju⟩
      change A (v j) ∈ W
      rw [hstep j]
      by_cases heq : j = (m : ℤ)
      · simpa [heq] using hnext
      · exact hW (j + 1) (by omega) (by omega)
    exact hmap hx
  have hb : ¬ LinearIndependent ℝ (p31BreakdownDirections v m) := hbreak
  rw [linearIndependent_fin2] at hb
  rcases not_and_or.mp hb with hz | hr
  · have hp : v (m : ℤ) ∈ P := by
      have hz' := not_ne_iff.mp hz
      change (Submodule.Quotient.mk (v (m : ℤ)) :
          (Fin n → ℝ) ⧸ P) = 0 at hz'
      exact (Submodule.Quotient.mk_eq_zero (p := P)).mp hz'
    exact hW_invariant_of_pos hp
  · push_neg at hr
    obtain ⟨a, ha⟩ := hr
    have hq : (Submodule.Quotient.mk (v (-(m : ℤ) - 1)) :
        (Fin n → ℝ) ⧸ P) =
        a • Submodule.Quotient.mk (v (m : ℤ)) := by
      simpa [p31BreakdownDirections] using ha.symm
    have hdiff : v (-(m : ℤ) - 1) - a • v (m : ℤ) ∈ P := by
      apply (Submodule.Quotient.eq P).mp
      simpa only [Submodule.Quotient.mk_smul] using hq
    have hnegAW : v (-(m : ℤ) - 1) ∈ AW := by
      have hh := AW.add_mem (hP_le_AW hdiff) (AW.smul_mem a (hgenAW (m : ℤ) (by omega) (by omega)))
      simpa only [sub_add_cancel] using hh
    have hW_le_AW : W ≤ AW := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, hj, rfl⟩
      rcases hj with ⟨hjl, hju⟩
      by_cases hleft : j = -(m : ℤ) - 1
      · simpa only [hleft] using hnegAW
      · exact hgenAW j (by omega) (by omega)
    have hfin : FiniteDimensional ℝ W := inferInstance
    have heq : W = AW := by
      apply Submodule.eq_of_le_of_finrank_eq hW_le_AW
      exact (A.finrank_map_eq W).symm
    intro x hx
    have hAx : A x ∈ AW := by
      apply Submodule.mem_map.mpr
      exact ⟨x, hx, rfl⟩
    rw [← heq] at hAx
    exact hAx

end VSCLReuse

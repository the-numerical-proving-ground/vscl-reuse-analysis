import VSCLReuse.P31.Definitions

namespace VSCLReuse

private lemma p31_mem (v : ℤ → Fin n → ℝ) (m : ℕ) (j : ℤ)
    (hj : -(m : ℤ) ≤ j ∧ j < (m : ℤ)) :
    v j ∈ p31LaurentSpan v m := by
  exact Submodule.subset_span (Set.mem_image_of_mem v hj)

private lemma p31_map_old (v : ℤ → Fin n → ℝ)
    (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1)) (m : ℕ) :
    ∀ x ∈ p31LaurentSpan v m, A x ∈ p31LaurentSpan v (m + 1) := by
  have hmap : (p31LaurentSpan v m).map (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤
      p31LaurentSpan v (m + 1) := by
    change (Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))).map
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ p31LaurentSpan v (m + 1)
    rw [Submodule.map_span_le]
    rintro y ⟨j, hj, rfl⟩
    change A (v j) ∈ p31LaurentSpan v (m + 1)
    rw [hstep]
    apply p31_mem
    obtain ⟨hlo, hhi⟩ := hj
    omega
  intro x hx
  exact hmap ⟨x, hx, rfl⟩

private lemma p31_invariant_of_next (v : ℤ → Fin n → ℝ)
    (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1)) (m : ℕ)
    (hnext : v ((m : ℤ) + 1) ∈ p31LaurentSpan v (m + 1)) :
    ∀ x ∈ p31LaurentSpan v (m + 1), A x ∈ p31LaurentSpan v (m + 1) := by
  have hmap : (p31LaurentSpan v (m + 1)).map
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ p31LaurentSpan v (m + 1) := by
    change (Submodule.span ℝ (v '' Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ))).map
      (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ p31LaurentSpan v (m + 1)
    rw [Submodule.map_span_le]
    rintro y ⟨j, hj, rfl⟩
    change A (v j) ∈ p31LaurentSpan v (m + 1)
    rw [hstep]
    by_cases h : j = (m : ℤ)
    · simpa [h] using hnext
    · apply p31_mem
      obtain ⟨hlo, hhi⟩ := hj
      omega
  intro x hx
  exact hmap ⟨x, hx, rfl⟩

private lemma p31_lower_in_old_implies_upper_in_old
    (v : ℤ → Fin n → ℝ)
    (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1)) (m : ℕ) (hm : 1 ≤ m)
    (hlower : v (-(m : ℤ) - 1) ∈ p31LaurentSpan v m) :
    v (m : ℤ) ∈ p31LaurentSpan v m := by
  let S := p31LaurentSpan v m
  have hback : ∀ j : ℤ, A.symm (v j) = v (j - 1) := by
    intro j
    have h : A (v (j - 1)) = v j := by
      convert hstep (j - 1) using 1
      congr 1
      omega
    rw [← h]
    exact A.symm_apply_apply _
  have hmap : S.map (A.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ S := by
    change (Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))).map
      (A.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ S
    rw [Submodule.map_span_le]
    rintro y ⟨j, hj, rfl⟩
    change A.symm (v j) ∈ S
    rw [hback]
    by_cases h : j = -(m : ℤ)
    · simpa [h] using hlower
    · apply p31_mem
      obtain ⟨hlo, hhi⟩ := hj
      omega
  have heq : S.map (A.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = S := by
    apply Submodule.eq_of_le_of_finrank_eq hmap
    exact LinearEquiv.finrank_map_eq A.symm S
  have hlast : v ((m : ℤ) - 1) ∈ S := p31_mem v m _ (by omega)
  rw [← heq] at hlast
  obtain ⟨y, hy, hAy⟩ := hlast
  have hy' : A (v ((m : ℤ) - 1)) = y := by
    rw [← hAy]
    simp
  convert hy using 1
  rw [← hy', hstep]
  congr 1
  omega

/-- P31-C1: the invariant-subspace conclusion of Proposition 3.4. -/
theorem p31_c1_rank_breakdown_invariant
    (n m : ℕ) (hm : 1 ≤ m)
    (v : ℤ → Fin n → ℝ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1))
    (hbreak : ¬ LinearIndependent ℝ (p31BreakdownDirections v m)) :
    ∀ x ∈ p31LaurentSpan v (m + 1),
      A x ∈ p31LaurentSpan v (m + 1) := by
  -- PROOF_START P31-C1-H001
  rw [linearIndependent_fin2] at hbreak
  push_neg at hbreak
  have hnext : v ((m : ℤ) + 1) ∈ p31LaurentSpan v (m + 1) := by
    by_cases hzero : p31BreakdownDirections v m 1 = 0
    · have hupper : v (m : ℤ) ∈ p31LaurentSpan v m := by
        exact (Submodule.Quotient.mk_eq_zero (p31LaurentSpan v m)).mp
          (by simpa [p31BreakdownDirections] using hzero)
      simpa only [hstep] using p31_map_old v A hstep m _ hupper
    · obtain ⟨a, ha⟩ := hbreak hzero
      have hrel : v (-(m : ℤ) - 1) - a • v (m : ℤ) ∈ p31LaurentSpan v m := by
        apply (Submodule.Quotient.eq (p31LaurentSpan v m)).mp
        simpa [p31BreakdownDirections, ← Submodule.Quotient.mk_smul] using ha.symm
      by_cases hane : a = 0
      · have hlower : v (-(m : ℤ) - 1) ∈ p31LaurentSpan v m := by
          simpa [hane] using hrel
        have hupper := p31_lower_in_old_implies_upper_in_old v A hstep m hm hlower
        simpa only [hstep] using p31_map_old v A hstep m _ hupper
      · have hshift := p31_map_old v A hstep m _ hrel
        have hshift' : v (-(m : ℤ)) - a • v ((m : ℤ) + 1) ∈
            p31LaurentSpan v (m + 1) := by
          simpa [map_sub, map_smul, hstep] using hshift
        have hstart : v (-(m : ℤ)) ∈ p31LaurentSpan v (m + 1) :=
          p31_mem v (m + 1) _ (by omega)
        have hsmul : a • v ((m : ℤ) + 1) ∈ p31LaurentSpan v (m + 1) := by
          convert (p31LaurentSpan v (m + 1)).sub_mem hstart hshift' using 1
          abel
        exact ((p31LaurentSpan v (m + 1)).smul_mem_iff hane).mp hsmul
  exact p31_invariant_of_next v A hstep m hnext

end VSCLReuse

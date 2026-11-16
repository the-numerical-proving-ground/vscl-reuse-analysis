import VSCLReuse.P31.Definitions

namespace VSCLReuse

/-- P31-C1: the invariant-subspace conclusion of Proposition 3.4. -/
theorem p31_c1_rank_breakdown_invariant
    (n m : ℕ) (hm : 1 ≤ m)
    (v : ℤ → Fin n → ℝ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1))
    (hbreak : ¬ LinearIndependent ℝ (p31BreakdownDirections v m)) :
    ∀ x ∈ p31LaurentSpan v (m + 1),
      A x ∈ p31LaurentSpan v (m + 1) := by
  -- PROOF_START P31-C1-H001
  let S := p31LaurentSpan v m
  let E := p31LaurentSpan v (m + 1)
  let neg := v (-((m : ℤ)) - 1)
  let pos := v (m : ℤ)
  have hS_mem (j : ℤ) (hj : j ∈ Set.Ico (-(m : ℤ)) (m : ℤ)) : v j ∈ S := by
    change v j ∈ Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  have hE_mem (j : ℤ) (hj : j ∈ Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)) :
      v j ∈ E := by
    change v j ∈ Submodule.span ℝ (v '' Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ))
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  have hS_le_E : S ≤ E := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    rcases hj with ⟨hjlo, hjhi⟩
    exact hE_mem j (by constructor <;> omega)
  have hAS : S.map (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≤ E := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    rcases hj with ⟨hjlo, hjhi⟩
    change A (v j) ∈ E
    rw [hstep j]
    exact hE_mem (j + 1) (by constructor <;> omega)
  have hAneg : A neg ∈ E := by
    change A (v (-((m : ℤ)) - 1)) ∈ E
    rw [hstep]
    convert hS_le_E (hS_mem (-(m : ℤ)) (by constructor <;> omega)) using 1 <;> congr 1 <;> omega
  have hposnext : A pos ∈ E := by
    rw [linearIndependent_fin2] at hbreak
    change ¬ ((Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) ≠ 0 ∧
      ∀ a : ℝ, a • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) ≠
        (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S)) at hbreak
    by_cases hp : (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) = 0
    · exact hAS ⟨pos, (Submodule.Quotient.mk_eq_zero S).mp hp, rfl⟩
    · have hr : ¬ ∀ a : ℝ, a • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) ≠
          (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) := by
        intro hn
        exact hbreak ⟨hp, hn⟩
      obtain ⟨a, ha⟩ := not_forall.mp hr
      have ha : a • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) =
          (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) := of_not_not ha
      by_cases ha0 : a = 0
      · have hnegS : neg ∈ S := by
          have hz : (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) = 0 := by
            calc
              (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) =
                  a • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) := ha.symm
              _ = 0 := by
                rw [ha0]
                exact Module.zero_smul (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S)
          exact (Submodule.Quotient.mk_eq_zero S).mp hz
        have hS_le_AS : S ≤ S.map (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
          apply Submodule.span_le.mpr
          rintro y ⟨j, hj, rfl⟩
          rcases hj with ⟨hjlo, hjhi⟩
          by_cases hjmin : j = -(m : ℤ)
          · subst j
            have hs := hstep (-((m : ℤ)) - 1)
            have heq : A neg = v (-(m : ℤ)) := by
              simpa [neg] using hs
            exact ⟨neg, hnegS, heq⟩
          · have hjprev : j - 1 ∈ Set.Ico (-(m : ℤ)) (m : ℤ) := by
              constructor <;> omega
            have heq : A (v (j - 1)) = v j := by
              convert hstep (j - 1) using 1 <;> congr 1 <;> omega
            exact ⟨v (j - 1), hS_mem (j - 1) hjprev, heq⟩
        have hAS_eq : S.map (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = S := by
          symm
          apply Submodule.eq_of_le_of_finrank_eq hS_le_AS
          exact (LinearEquiv.finrank_map_eq A S).symm
        have hposS : pos ∈ S := by
          have hj : (m : ℤ) - 1 ∈ Set.Ico (-(m : ℤ)) (m : ℤ) := by
            constructor <;> omega
          have heq : A (v ((m : ℤ) - 1)) = pos := by
            simpa [pos] using hstep ((m : ℤ) - 1)
          have hmem : pos ∈ S.map (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
            ⟨v ((m : ℤ) - 1), hS_mem _ hj, heq⟩
          rwa [hAS_eq] at hmem
        exact hAS ⟨pos, hposS, rfl⟩
      · have hqpos : (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) =
            a⁻¹ • (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) := by
          calc
            (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) =
                (a⁻¹ * a) • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S) := by simp [ha0]
            _ = a⁻¹ • (a • (Submodule.Quotient.mk pos : (Fin n → ℝ) ⧸ S)) :=
                (smul_smul _ _ _).symm
            _ = a⁻¹ • (Submodule.Quotient.mk neg : (Fin n → ℝ) ⧸ S) := by rw [ha]
        have hdiff : pos - a⁻¹ • neg ∈ S := by
          apply (Submodule.Quotient.eq S).mp
          rw [Submodule.Quotient.mk_smul]
          exact hqpos
        have hAdiff : A (pos - a⁻¹ • neg) ∈ E :=
          hAS ⟨pos - a⁻¹ • neg, hdiff, rfl⟩
        have hid : A pos = A (pos - a⁻¹ • neg) + a⁻¹ • A neg := by simp
        rw [hid]
        exact E.add_mem hAdiff (E.smul_mem _ hAneg)
  intro x hx
  change x ∈ E at hx
  change A x ∈ E
  have hAE : E ≤ E.comap (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, hj, rfl⟩
    rcases hj with ⟨hjlo, hjhi⟩
    change A (v j) ∈ E
    by_cases hjtop : j = (m : ℤ)
    · subst j
      exact hposnext
    · rw [hstep j]
      exact hE_mem (j + 1) (by constructor <;> omega)
  exact hAE hx

end VSCLReuse

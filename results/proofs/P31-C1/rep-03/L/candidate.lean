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
  let S : Submodule ℝ (Fin n → ℝ) := p31LaurentSpan v m
  let W : Submodule ℝ (Fin n → ℝ) := p31LaurentSpan v (m + 1)
  have memS (j : ℤ) (hlo : -(m : ℤ) ≤ j) (hhi : j < (m : ℤ)) : v j ∈ S := by
    change v j ∈ Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))
    exact Submodule.subset_span ⟨j, ⟨hlo, hhi⟩, rfl⟩
  have memW (j : ℤ) (hlo : -((m + 1 : ℕ) : ℤ) ≤ j)
      (hhi : j < ((m + 1 : ℕ) : ℤ)) : v j ∈ W := by
    change v j ∈ Submodule.span ℝ
      (v '' Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ))
    exact Submodule.subset_span ⟨j, ⟨hlo, hhi⟩, rfl⟩
  have hSW : S ≤ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, ⟨hjlo, hjhi⟩, rfl⟩ := hy
        exact memW j (by omega) (by omega)
    | zero => exact W.zero_mem
    | add x y hx hy ihx ihy => exact W.add_mem ihx ihy
    | smul a x hx ih => exact W.smul_mem a ih
  have hAold : ∀ x ∈ S, A x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, ⟨hjlo, hjhi⟩, rfl⟩ := hy
        rw [hstep]
        exact memW (j + 1) (by omega) (by omega)
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using W.add_mem ihx ihy
    | smul a x hx ih => simpa only [map_smul] using W.smul_mem a ih
  obtain ⟨c, hc, ⟨i, hi⟩⟩ := Fintype.not_linearIndependent_iff.mp hbreak
  have hcoeff : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hrelq : c 0 • (Submodule.Quotient.mk (v (-((m : ℤ)) - 1)) :
      (Fin n → ℝ) ⧸ S) +
      c 1 • (Submodule.Quotient.mk (v (m : ℤ)) : (Fin n → ℝ) ⧸ S) = 0 := by
    simpa [Fin.sum_univ_two, p31BreakdownDirections, S] using hc
  have hrelS : c 0 • v (-((m : ℤ)) - 1) + c 1 • v (m : ℤ) ∈ S := by
    apply (Submodule.Quotient.mk_eq_zero S).mp
    simpa only [map_add, map_smul] using hrelq
  have htop : v ((m : ℤ) + 1) ∈ W := by
    by_cases hc1 : c 1 = 0
    · have hc0 : c 0 ≠ 0 := hcoeff.resolve_right (by simpa using hc1)
      have hneg : v (-((m : ℤ)) - 1) ∈ S := by
        have hh : c 0 • v (-((m : ℤ)) - 1) ∈ S := by
          simpa [hc1] using hrelS
        have hh' := S.smul_mem (c 0)⁻¹ hh
        simpa [smul_smul, hc0] using hh'
      have hback : S.map A.symm.toLinearMap ≤ S := by
        change (Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ))).map
          A.symm.toLinearMap ≤ S
        rw [Submodule.map_span_le]
        rintro y ⟨j, hj, rfl⟩
        have heq : A.symm (v j) = v (j - 1) := by
          have hh := hstep (j - 1)
          have hj' : j - 1 + 1 = j := by omega
          rw [hj'] at hh
          rw [← hh, A.symm_apply_apply]
        change A.symm (v j) ∈ S
        rw [heq]
        by_cases hjlo : j = -(m : ℤ)
        · simpa [hjlo] using hneg
        · exact memS (j - 1) (by have := hj.1; omega) (by have := hj.2; omega)
      have heqS : S.map A.symm.toLinearMap = S := by
        apply Submodule.eq_of_le_of_finrank_eq hback
        exact LinearEquiv.finrank_map_eq A.symm S
      have hAinv : ∀ x ∈ S, A x ∈ S := by
        intro x hx
        have hmap : x ∈ S.map A.symm.toLinearMap := heqS.symm ▸ hx
        obtain ⟨y, hy, hxy⟩ := hmap
        have hAx : A x = y := by
          have := congrArg A hxy
          simpa using this.symm
        exact hAx.symm ▸ hy
      have hm1 : v ((m : ℤ) - 1) ∈ S := memS _ (by omega) (by omega)
      have hm : v (m : ℤ) ∈ S := by
        convert hAinv _ hm1 using 1
        rw [hstep]
        congr 1
        omega
      have := hAinv _ hm
      exact hSW (by simpa [hstep] using this)
    · have hrelA : c 0 • v (-(m : ℤ)) + c 1 • v ((m : ℤ) + 1) ∈ W := by
        have hh := hAold _ hrelS
        simpa only [map_add, map_smul, hstep, sub_add_cancel] using hh
      have hh : c 1 • v ((m : ℤ) + 1) ∈ W := by
        have := W.sub_mem hrelA
          (W.smul_mem (c 0) (memW (-(m : ℤ)) (by omega) (by omega)))
        simpa only [add_sub_cancel_left] using this
      have hh' := W.smul_mem (c 1)⁻¹ hh
      simpa [smul_smul, hc1] using hh'
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨j, ⟨hjlo, hjhi⟩, rfl⟩ := hy
      rw [hstep]
      by_cases hjtop : j = (m : ℤ)
      · simpa [hjtop] using htop
      · exact memW (j + 1) (by omega) (by omega)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using W.add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using W.smul_mem a ih

end VSCLReuse

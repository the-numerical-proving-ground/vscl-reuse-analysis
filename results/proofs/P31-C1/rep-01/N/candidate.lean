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
  let W := p31LaurentSpan v (m + 1)
  have hmemS (j : ℤ) (hj : -(m : ℤ) ≤ j ∧ j < (m : ℤ)) : v j ∈ S := by
    apply Submodule.subset_span
    exact ⟨j, hj, rfl⟩
  have hmemW (j : ℤ) (hj : -((m + 1 : ℕ) : ℤ) ≤ j ∧ j < ((m + 1 : ℕ) : ℤ)) :
      v j ∈ W := by
    apply Submodule.subset_span
    exact ⟨j, hj, rfl⟩
  have hAold : ∀ x ∈ S, A x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨j, hj, rfl⟩
        change -(m : ℤ) ≤ j ∧ j < (m : ℤ) at hj
        rw [hstep]
        apply hmemW
        constructor <;> omega
    | zero => simp
    | add x y hx hy ihx ihy => simpa using W.add_mem ihx ihy
    | smul a x hx ih => simpa using W.smul_mem a ih
  have hnegpos : v (-(m : ℤ) - 1) ∈ S → v (m : ℤ) ∈ S := by
    intro hneg
    have hback : ∀ x ∈ S, A.symm x ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
          rcases hy with ⟨j, hj, rfl⟩
          change -(m : ℤ) ≤ j ∧ j < (m : ℤ) at hj
          have hprev : A.symm (v j) = v (j - 1) := by
            have hh := hstep (j - 1)
            have he : j - 1 + 1 = j := by omega
            rw [he] at hh
            rw [← hh, A.symm_apply_apply]
          rw [hprev]
          by_cases hmin : j = -(m : ℤ)
          · have he : j - 1 = -(m : ℤ) - 1 := by omega
            rw [he]
            exact hneg
          · apply hmemS
            constructor <;> omega
      | zero => simp
      | add x y hx hy ihx ihy => simpa using S.add_mem ihx ihy
      | smul a x hx ih => simpa using S.smul_mem a ih
    have hsurj : Set.SurjOn A.symm S S :=
      (LinearMap.injOn_iff_surjOn (f := A.symm.toLinearMap) hback).mp
        (fun _ _ _ _ heq => A.symm.injective heq)
    have hA : ∀ x ∈ S, A x ∈ S := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hsurj hx
      have he : A.symm y = x := hxy
      have : A x = y := by rw [← he, A.apply_symm_apply]
      simpa [this] using hy
    have htop : v ((m : ℤ) - 1) ∈ S := hmemS _ (by constructor <;> omega)
    have := hA _ htop
    have he : (m : ℤ) - 1 + 1 = (m : ℤ) := by omega
    simpa [hstep, he] using this
  have hdep : (p31BreakdownDirections v m) 1 = 0 ∨
      ∃ a : ℝ, a • (p31BreakdownDirections v m) 1 =
        (p31BreakdownDirections v m) 0 := by
    by_cases hz : (p31BreakdownDirections v m) 1 = 0
    · exact Or.inl hz
    · right
      by_contra hh
      push_neg at hh
      exact hbreak ((linearIndependent_fin2).mpr ⟨hz, hh⟩)
  have hposnext : v ((m : ℤ) + 1) ∈ W := by
    rcases hdep with hposzero | ⟨a, hrel⟩
    · have hpos : v (m : ℤ) ∈ S := by
        exact (Submodule.Quotient.mk_eq_zero S).mp (by simpa [p31BreakdownDirections] using hposzero)
      simpa [hstep] using hAold _ hpos
    · have hrel' : v (-(m : ℤ) - 1) - a • v (m : ℤ) ∈ S := by
        apply (Submodule.Quotient.mk_eq_zero S).mp
        rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        apply sub_eq_zero.mpr
        simpa [p31BreakdownDirections] using hrel.symm
      by_cases ha : a = 0
      · have hneg : v (-(m : ℤ) - 1) ∈ S := by simpa [ha] using hrel'
        have hpos := hnegpos hneg
        simpa [hstep] using hAold _ hpos
      · have hshift := hAold _ hrel'
        have hnegshift : A (v (-(m : ℤ) - 1)) ∈ W := by
          rw [hstep]
          apply hmemW
          constructor <;> omega
        have hsmul : a • A (v (m : ℤ)) ∈ W := by
          have hh : A (v (-(m : ℤ) - 1)) - a • A (v (m : ℤ)) ∈ W := by
            simpa using hshift
          have := W.sub_mem hnegshift hh
          simpa [sub_sub_cancel_left] using this
        have hposshift : A (v (m : ℤ)) ∈ W := by
          have := W.smul_mem a⁻¹ hsmul
          simpa [smul_smul, inv_mul_cancel₀ ha] using this
        simpa [hstep] using hposshift
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨j, hj, rfl⟩
      change -((m + 1 : ℕ) : ℤ) ≤ j ∧ j < ((m + 1 : ℕ) : ℤ) at hj
      by_cases htop : j = (m : ℤ)
      · subst j
        simpa [hstep] using hposnext
      · rw [hstep]
        apply hmemW
        constructor <;> omega
  | zero => simp
  | add x y hx hy ihx ihy => simpa using W.add_mem ihx ihy
  | smul a x hx ih => simpa using W.smul_mem a ih

end VSCLReuse

import VSCLReuse.P31.Definitions

namespace VSCLReuse

private theorem p31_reverse_invariance
    {n : ℕ} (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (W : Submodule ℝ (Fin n → ℝ))
    (hback : ∀ x ∈ W, A.symm x ∈ W) :
    ∀ x ∈ W, A x ∈ W := by
  let T : W →ₗ[ℝ] W := {
    toFun := fun x => ⟨A.symm x, hback x x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      simp
    map_smul' := by
      intro c x
      apply Subtype.ext
      simp
  }
  have hTinj : Function.Injective T := by
    intro x y hxy
    apply Subtype.ext
    exact A.symm.injective (congrArg Subtype.val hxy)
  have hTsurj : Function.Surjective T :=
    LinearMap.injective_iff_surjective.mp hTinj
  intro x hx
  obtain ⟨y, hy⟩ := hTsurj ⟨x, hx⟩
  have hy' : A.symm (y : Fin n → ℝ) = x :=
    congrArg Subtype.val hy
  have hax : A x = (y : Fin n → ℝ) := by
    rw [← hy', A.apply_symm_apply]
  rw [hax]
  exact y.property

private theorem p31_span_mem {n : ℕ} (v : ℤ → Fin n → ℝ)
    (k : ℕ) (j : ℤ) (hj : -(k : ℤ) ≤ j ∧ j < (k : ℤ)) :
    v j ∈ p31LaurentSpan v k := by
  apply Submodule.subset_span
  exact ⟨j, hj, rfl⟩

/-- P31-C1: the invariant-subspace conclusion of Proposition 3.4. -/
theorem p31_c1_rank_breakdown_invariant
    (n m : ℕ) (hm : 1 ≤ m)
    (v : ℤ → Fin n → ℝ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hstep : ∀ j, A (v j) = v (j + 1))
    (hbreak : ¬ LinearIndependent ℝ (p31BreakdownDirections v m)) :
    ∀ x ∈ p31LaurentSpan v (m + 1),
      A x ∈ p31LaurentSpan v (m + 1) := by
  -- PROOF_START P31-C1-H001
  let Q := p31LaurentSpan v m
  let W := p31LaurentSpan v (m + 1)
  let S : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ (v '' Set.Icc (-(m : ℤ)) (m : ℤ))
  have hQW : Q ≤ W := by
    change Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ)) ≤ W
    apply Submodule.span_le.mpr
    rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
    apply p31_span_mem v (m + 1) j
    constructor <;> omega
  have hQS : Q ≤ S := by
    change Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ)) ≤ S
    apply Submodule.span_le.mpr
    rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
    apply Submodule.subset_span
    exact ⟨j, ⟨hjlo, by omega⟩, rfl⟩
  have hposW : v (m : ℤ) ∈ W :=
    p31_span_mem v (m + 1) (m : ℤ) (by constructor <;> omega)
  have hposS : v (m : ℤ) ∈ S := by
    apply Submodule.subset_span
    exact ⟨(m : ℤ), ⟨by omega, le_refl _⟩, rfl⟩
  let b := p31BreakdownDirections v m
  by_cases hb : b 1 = 0
  · have hposQ : v (m : ℤ) ∈ Q := by
      exact (Submodule.Quotient.mk_eq_zero Q).mp
        (by simpa [b, p31BreakdownDirections] using hb)
    have hstableQ : ∀ x ∈ Q, A x ∈ Q := by
      intro x hx
      have hle : Q ≤ Q.comap A.toLinearMap := by
        change Submodule.span ℝ (v '' Set.Ico (-(m : ℤ)) (m : ℤ)) ≤ _
        apply Submodule.span_le.mpr
        rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
        change A (v j) ∈ Q
        rw [hstep j]
        by_cases hjtop : j = (m : ℤ) - 1
        · simpa [hjtop] using hposQ
        · exact p31_span_mem v m (j + 1) (by constructor <;> omega)
      exact hle hx
    have hstableW : ∀ x ∈ W, A x ∈ W := by
      intro x hx
      have hle : W ≤ W.comap A.toLinearMap := by
        change Submodule.span ℝ (v '' Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)) ≤ _
        apply Submodule.span_le.mpr
        rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
        change A (v j) ∈ W
        rw [hstep j]
        by_cases hjtop : j = (m : ℤ)
        · have : v (j + 1) ∈ Q := by
            simpa [hjtop, ← hstep] using hstableQ (v (m : ℤ)) hposQ
          exact hQW this
        · exact p31_span_mem v (m + 1) (j + 1) (by constructor <;> omega)
      exact hle hx
    exact hstableW
  · have hcoeff : ∃ c : ℝ, c • b 1 = b 0 := by
      by_contra hc
      apply hbreak
      exact linearIndependent_fin2.mpr ⟨hb, by
        intro c heq
        exact hc ⟨c, heq⟩⟩
    obtain ⟨c, hc⟩ := hcoeff
    have hrel : v (-((m : ℤ)) - 1) - c • v (m : ℤ) ∈ Q := by
      apply (Submodule.Quotient.eq Q).mp
      simpa [b, p31BreakdownDirections] using hc.symm
    have hnegS : v (-((m : ℤ)) - 1) ∈ S := by
      have h := S.add_mem (hQS hrel) (S.smul_mem c hposS)
      simpa only [sub_add_cancel] using h
    have hWS : W ≤ S := by
      change Submodule.span ℝ (v '' Set.Ico (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)) ≤ S
      apply Submodule.span_le.mpr
      rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
      by_cases hjlo' : j = -((m : ℤ)) - 1
      · simpa [hjlo'] using hnegS
      · apply Submodule.subset_span
        exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    have hback : ∀ x ∈ W, A.symm x ∈ W := by
      intro x hx
      have hle : S ≤ W.comap A.symm.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro y ⟨j, ⟨hjlo, hjhi⟩, rfl⟩
        change A.symm (v j) ∈ W
        have hshift : A.symm (v j) = v (j - 1) := by
          have heq : A (v (j - 1)) = v j := by
            simpa only [sub_add_cancel] using hstep (j - 1)
          exact (A.symm_apply_eq).mpr heq.symm
        rw [hshift]
        apply p31_span_mem v (m + 1) (j - 1)
        constructor <;> omega
      exact hle (hWS hx)
    exact p31_reverse_invariance A W hback

end VSCLReuse

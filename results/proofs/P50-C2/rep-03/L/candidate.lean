import VSCLReuse.P50.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p50AsFPModel (fp : P50FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

private lemma p50Dot_eq_library (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p50Dot fp n x y = NumStability.fl_dotProduct (p50AsFPModel fp) n x y := by
  cases n <;> rfl

/-- P50-C2: complete named Theorem 3.5, the position-specific diagonal
backward-error representation for the sequential dot product. -/
theorem p50_c2_full_theorem35 (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P50GammaValid fp.u n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget n i)) ∧
      p50Dot fp n x y =
        ∑ i : Fin n, x i * y i * (1 + θ i) := by
  -- PROOF_START P50-C2-H001
  cases n with
  | zero =>
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [p50Dot]⟩
  | succ n =>
      let gfp := p50AsFPModel fp
      have hvalid : NumStability.gammaValid gfp (n + 1) := hn
      have hvalid1 : NumStability.gammaValid gfp 1 :=
        NumStability.gammaValid_mono gfp (by omega) hvalid
      have hvalidn : NumStability.gammaValid gfp n :=
        NumStability.gammaValid_mono gfp (by omega) hvalid
      obtain ⟨mulDelta, addDelta, hmul, hadd, hfl⟩ :=
        NumStability.dotProduct_factor_expansion_sum_succ gfp n x y
      have hmul1 : ∀ i : Fin (n + 1),
          |mulDelta i| ≤ NumStability.gamma gfp 1 := by
        intro i
        exact le_trans (hmul i) (NumStability.u_le_gamma gfp one_pos hvalid1)
      have hlocal : ∀ i : Fin (n + 1),
          ∃ η : ℝ,
            |η| ≤ p50Gamma fp.u (p50SourceBudget (n + 1) i) ∧
            NumStability.dotProductLocalFactor n mulDelta addDelta i = 1 + η := by
        intro i
        refine Fin.cases ?_ ?_ i
        · obtain ⟨θadd, hθadd, hprod⟩ :=
            NumStability.prod_error_bound gfp n addDelta hadd hvalidn
          have hcomb : NumStability.gammaValid gfp (1 + n) := by
            simpa [Nat.add_comm] using hvalid
          obtain ⟨η, hη, heq⟩ :=
            NumStability.gamma_mul gfp 1 n (mulDelta 0) θadd
              (hmul1 0) hθadd hcomb
          refine ⟨η, ?_, ?_⟩
          · simpa [p50SourceBudget, p50Gamma, NumStability.gamma,
              gfp, p50AsFPModel, Nat.add_comm] using hη
          · simpa [NumStability.dotProductLocalFactor, hprod] using heq
        · intro j
          have hvalidrem : NumStability.gammaValid gfp (n - j.val) :=
            NumStability.gammaValid_mono gfp (by omega) hvalid
          obtain ⟨θsuffix, hθsuffix, hsuffix⟩ :=
            NumStability.sumSuffixErrorProduct_exists_theta_le_gamma
              gfp n addDelta hadd j hvalidrem
          have hvalidcomb : NumStability.gammaValid gfp (1 + (n - j.val)) :=
            NumStability.gammaValid_mono gfp (by omega) hvalid
          obtain ⟨η, hη, heq⟩ :=
            NumStability.gamma_mul gfp 1 (n - j.val) (mulDelta j.succ) θsuffix
              (hmul1 j.succ) hθsuffix hvalidcomb
          have hbudget : p50SourceBudget (n + 1) j.succ = 1 + (n - j.val) := by
            simp [p50SourceBudget]
            omega
          refine ⟨η, ?_, ?_⟩
          · simpa [hbudget, p50Gamma, NumStability.gamma, gfp, p50AsFPModel]
              using hη
          · simpa [NumStability.dotProductLocalFactor, hsuffix] using heq
      let θ : Fin (n + 1) → ℝ := fun i => Classical.choose (hlocal i)
      refine ⟨θ, ?_, ?_⟩
      · intro i
        exact (Classical.choose_spec (hlocal i)).1
      · rw [p50Dot_eq_library, hfl]
        apply Finset.sum_congr rfl
        intro i _
        rw [(Classical.choose_spec (hlocal i)).2]

end VSCLReuse

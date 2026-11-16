import VSCLReuse.P50.Definitions
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p50AsFPModel (fp : P50FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun a b => a - b
  fl_mul := fp.fl_mul
  fl_div := fun a b => a / b
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro a b
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_mul := fp.model_mul
  model_div := by
    intro a b _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_sqrt := by
    intro a _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

/-- P50-C2: complete named Theorem 3.5, the position-specific diagonal
backward-error representation for the sequential dot product. -/
theorem p50_c2_full_theorem35 (fp : P50FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hn : P50GammaValid fp.u n) :
    ∃ θ : Fin n → ℝ,
      (∀ i, |θ i| ≤ p50Gamma fp.u (p50SourceBudget n i)) ∧
      p50Dot fp n x y =
        ∑ i : Fin n, x i * y i * (1 + θ i) := by
  -- PROOF_START P50-C2-H001
  let f := p50AsFPModel fp
  have hu : f.u = fp.u := rfl
  have hvalid : NumStability.gammaValid f n := by
    simpa [NumStability.gammaValid, f, p50AsFPModel, P50GammaValid] using hn
  cases n with
  | zero =>
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [p50Dot]⟩
  | succ k =>
      obtain ⟨mulDelta, addDelta, hmul, hadd, hdot⟩ :=
        NumStability.dotProduct_factor_expansion_sum_succ f k x y
      have hvalidOne : NumStability.gammaValid f 1 :=
        NumStability.gammaValid_mono f (by omega) hvalid
      have hmulGamma : ∀ i : Fin (k + 1),
          |mulDelta i| ≤ NumStability.gamma f 1 := by
        intro i
        exact (hmul i).trans (NumStability.u_le_gamma f Nat.one_pos hvalidOne)
      have hvalidK : NumStability.gammaValid f k :=
        NumStability.gammaValid_mono f (by omega) hvalid
      have hfactor : ∀ i : Fin (k + 1),
          ∃ η : ℝ,
            |η| ≤ p50Gamma fp.u (p50SourceBudget (k + 1) i) ∧
            NumStability.dotProductLocalFactor k mulDelta addDelta i = 1 + η := by
        intro i
        refine Fin.cases ?_ ?_ i
        · obtain ⟨θa, hθa, hprod⟩ :=
            NumStability.prod_error_bound f k addDelta hadd hvalidK
          obtain ⟨η, hη, heq⟩ :=
            NumStability.gamma_mul f 1 k (mulDelta 0) θa
              (hmulGamma 0) hθa (by simpa [Nat.add_comm] using hvalid)
          refine ⟨η, ?_, ?_⟩
          · simpa [p50Gamma, p50SourceBudget, NumStability.gamma,
              f, p50AsFPModel, Nat.add_comm] using hη
          · simpa [NumStability.dotProductLocalFactor, hprod] using heq
        · intro j
          have hbudget : p50SourceBudget (k + 1) j.succ = (k - j.val) + 1 := by
            simp [p50SourceBudget]
          have hvalidSuffix : NumStability.gammaValid f (k - j.val) :=
            NumStability.gammaValid_mono f (by omega) hvalid
          obtain ⟨θa, hθa, hsuffix⟩ :=
            NumStability.sumSuffixErrorProduct_exists_theta_le_gamma
              f k addDelta hadd j hvalidSuffix
          have hvalidCombined : NumStability.gammaValid f (1 + (k - j.val)) :=
            NumStability.gammaValid_mono f (by omega) hvalid
          obtain ⟨η, hη, heq⟩ :=
            NumStability.gamma_mul f 1 (k - j.val) (mulDelta j.succ) θa
              (hmulGamma j.succ) hθa hvalidCombined
          refine ⟨η, ?_, ?_⟩
          · simpa [p50Gamma, hbudget, NumStability.gamma,
              f, p50AsFPModel, Nat.add_comm] using hη
          · simpa [NumStability.dotProductLocalFactor, hsuffix] using heq
      let θ : Fin (k + 1) → ℝ :=
        fun i => NumStability.dotProductLocalFactor k mulDelta addDelta i - 1
      refine ⟨θ, ?_, ?_⟩
      · intro i
        obtain ⟨η, hη, heq⟩ := hfactor i
        have hθ : θ i = η := by dsimp [θ]; linarith
        simpa [hθ] using hη
      · have hbridge : p50Dot fp (k + 1) x y =
            NumStability.fl_dotProduct f (k + 1) x y := by
          rfl
        rw [hbridge, hdot]
        apply Finset.sum_congr rfl
        intro i _
        simp [θ]

end VSCLReuse

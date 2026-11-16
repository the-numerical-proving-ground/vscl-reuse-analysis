import VSCLReuse.P44.Definitions
import NumStability.Analysis.Summation.ErrorBounds

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p44AsFPModel (fp : P44FPModel) : NumStability.FPModel where
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

/-- Section 2 multiword-product accumulation representation. -/
theorem p44_c2_multiword_accumulation
    (fp : P44FPModel) (p n : ℕ)
    (pairs : Fin (p * p) ≃ Fin p × Fin p)
    (a b : Fin p → Fin n → ℝ)
    (hp : 0 < p)
    (hvalid : P44GammaValid fp.u (p * p - 1)) :
    ∃ θ : Fin (p * p) → ℝ,
      (∀ t, |θ t| ≤ p44Gamma fp.u (p * p - 1)) ∧
      p44MultiwordDotMany fp p n pairs a b =
        ∑ t : Fin (p * p),
          p44BlockDot fp n (a (pairs t).1) (b (pairs t).2) * (1 + θ t) := by
  -- PROOF_START P44-C2-H001
  let v : Fin (p * p) → ℝ := fun t =>
    p44BlockDot fp n (a (pairs t).1) (b (pairs t).2)
  have hpos : 0 < p * p := Nat.mul_pos hp hp
  have hgamma : NumStability.gammaValid (p44AsFPModel fp) (p * p - 1) := by
    simpa only [NumStability.gammaValid, p44AsFPModel, P44GammaValid] using hvalid
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.fl_sum_error_tight (p44AsFPModel fp) (p * p) hpos v hgamma
  refine ⟨θ, ?_, ?_⟩
  · intro t
    simpa only [NumStability.gamma, p44AsFPModel, p44Gamma] using hθ t
  · simpa only [p44MultiwordDotMany, p44RecursiveSum, v, p44AsFPModel] using hsum

end VSCLReuse

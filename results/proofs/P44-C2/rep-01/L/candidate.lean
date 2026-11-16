import VSCLReuse.P44.Definitions
import NumStability.Algorithms.Summation.Recursive.Core

namespace VSCLReuse

open scoped BigOperators

/-- Extend the addition and multiplication operations to the library's full
floating point interface using exact operations for the unused fields. -/
noncomputable def p44FPModelToNumStability (fp : P44FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

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
  let f := p44FPModelToNumStability fp
  have hfvalid : NumStability.gammaValid f (p * p - 1) := by
    simpa [f, p44FPModelToNumStability, NumStability.gammaValid,
      P44GammaValid] using hvalid
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.recursiveSum_backward_error f (p * p)
      (fun t => p44BlockDot fp n (a (pairs t).1) (b (pairs t).2)) hfvalid
  refine ⟨θ, ?_, ?_⟩
  · intro t
    simpa [f, p44FPModelToNumStability, NumStability.gamma,
      p44Gamma] using hθ t
  · simpa [p44MultiwordDotMany, p44RecursiveSum,
      NumStability.fl_recursiveSum, f, p44FPModelToNumStability] using hsum

end VSCLReuse

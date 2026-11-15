import VSCLReuse.P44.Definitions

namespace VSCLReuse

open scoped BigOperators

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
  sorry

end VSCLReuse

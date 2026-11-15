import VSCLReuse.P42.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Theorem 3.1, recursive-block and pairwise-outer specialization. -/
theorem p42_c3_fabsum_backward_error
    (fp : P42FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ)
    (hb : 0 < b)
    (hbvalid : P42GammaValid fp.u (b - 1))
    (hrvalid : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → Fin b → ℝ,
      (∀ i j, |μ i j| ≤
        p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r) ∧
      p42FABsum fp b r x =
        ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
  -- PROOF_START P42-C3-H001
  sorry

end VSCLReuse

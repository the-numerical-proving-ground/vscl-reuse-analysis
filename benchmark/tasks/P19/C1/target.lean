import VSCLReuse.P19.Definitions

namespace VSCLReuse

/-- P19-C1: the sharp structured first-order condition formula in (3.3)--(3.4). -/
theorem p19_c1_sharp_structured_condition_formula
    {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ)
    (hg : ∀ j, 0 ≤ g j) (hf : ∀ i, 0 ≤ f i) (hx : 0 < xNorm) :
    p19LinearizedCondition K H g f xNorm =
      p19ConditionFormula K H g f xNorm := by
  -- PROOF_START P19-C1-H001
  sorry

end VSCLReuse

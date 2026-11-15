import VSCLReuse.P04.Definitions

namespace VSCLReuse

theorem p04_c1_multidimensional_rms_error_bound
    {m : ℕ} [NeZero m]
    (plan : P04MultidimensionalFftPlan m) (γ : ℝ)
    (family : P04AsymptoticMultidimensionalFftFamily plan γ)
    (hexactOutput : 0 < p04MultiRms (p04FamilyMultiExactOutput family)) :
    ∃ secondOrderCoeff : ℝ, 0 ≤ secondOrderCoeff ∧
      ∃ radius : ℝ, 0 < radius ∧
        ∀ ε : P04PositiveEpsilon, ε.1 ≤ radius →
          p04MultiRms (p04FamilyMultiFftRoundoffError family ε) /
              p04MultiRms (p04FamilyMultiExactOutput family) ≤
            ε.1 * (∑ i : Fin m, p04AxisK (plan.axis i) γ) +
              secondOrderCoeff * ε.1 ^ 2 := by
  -- PROOF_START P04-C1-H001
  sorry

end VSCLReuse

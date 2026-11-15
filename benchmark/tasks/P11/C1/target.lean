import VSCLReuse.P11.Definitions

namespace VSCLReuse

theorem p11_c1_multiword_forward_error
    {m n q p : ℕ} (semantics : P11FirstOrderSemantics) :
    (∀ (run : P11StaticMultiwordRun m n q p),
      P11StaticSection4Derivation semantics run →
        p11FirstOrderLe semantics
          (p11StaticMultiwordForwardError run)
          (p11NormwiseEnvelope
            (p11MultiNarrowCoefficient n p
              (p11StaticInputUnitRoundoff run.model)
              (p11StaticAccumUnitRoundoff run.model)
              (p11StaticScalingThreshold n run.model)
              (p11StaticInputUnderflowEnvelope run.model)
              (p11StaticAccumUnderflowEnvelope run.model))
            run.A run.B)) ∧
      (∀ (run : P11StaticMultiwordRun m n q p),
        P11StaticSection4Derivation semantics run →
          p11FirstOrderLe semantics
            (p11StaticMultiwordForwardError run)
            (p11NormwiseEnvelope
              (p11MultiRangeFreeCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticAccumUnitRoundoff run.model))
              run.A run.B +
            p11NormwiseEnvelope
              (p11MultiInputUnderflowCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model))
              run.A run.B +
            p11NormwiseEnvelope
              (p11MultiAccumUnderflowCoefficient n p
                (p11StaticScalingThreshold n run.model)
                (p11StaticAccumUnderflowEnvelope run.model))
              run.A run.B)) ∧
      (∀ run : P11StaticMultiwordRun m n q p,
        p11MultiInputRoundingCoefficient p
              (p11StaticInputUnitRoundoff run.model) =
            ((((p : ℝ) + 1) / 2) *
                p11StaticInputUnitRoundoff run.model ^ (p - 1)) *
              p11SingleInputRoundingCoefficient
                (p11StaticInputUnitRoundoff run.model) ∧
          (n : ℝ) *
              p11MultiInputUnderflowCoefficient n p
                (p11StaticInputUnitRoundoff run.model)
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model) =
            p11StaticInputUnitRoundoff run.model ^ (p - 1) *
              p11SingleInputUnderflowCoefficient n
                (p11StaticScalingThreshold n run.model)
                (p11StaticInputUnderflowEnvelope run.model)) := by
  -- PROOF_START P11-C1-H001
  sorry

end VSCLReuse

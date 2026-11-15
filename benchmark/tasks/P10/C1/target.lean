import VSCLReuse.P10.Definitions

namespace VSCLReuse

theorem p10_c1_right_flexible_attainable_forward_error
    {n : ℕ} (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice) :
    (∀ (right : P10StaticRightFamily n semantics)
        (mgs : P10MGSSelectionLaw right.family)
        (appendix : P10StaticRightAppendixCTheory choice right)
        (applicability : ∀ k : P10Theorem31Dimension n,
          p10IterationWellConditioned (right.family.iteration k) →
          (k.1 = n ∨ p10MGSNearDependence (right.family.iteration k)) →
          P10StaticRightConditions choice (right.iteration k)),
      ∃ k : P10Theorem31Dimension n,
        p10IterationWellConditioned (right.family.iteration k) ∧
          p10FirstOrderLe semantics
            (p10ForwardError right.family.system.xExact
              (right.family.iteration k).xHat)
            ((right.family.iteration k).dimensionFactor *
              p10StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR)) ∧
      (∀ (flexible : P10StaticFlexibleFamily n semantics)
          (mgs : P10MGSSelectionLaw flexible.family)
          (appendix : P10StaticFlexibleAppendixDTheory choice flexible)
          (applicability : ∀ k : P10Theorem31Dimension n,
            p10IterationWellConditioned (flexible.family.iteration k) →
            (k.1 = n ∨
              p10MGSNearDependence (flexible.family.iteration k)) →
            P10StaticFlexibleConditions choice (flexible.iteration k)),
        ∃ k : P10Theorem31Dimension n,
          p10IterationWellConditioned (flexible.family.iteration k) ∧
            p10FirstOrderLe semantics
              (p10ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat)
              ((flexible.family.iteration k).dimensionFactor *
                p10StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR)) ∧
        ∀ (family : P10Theorem31Family n semantics)
          (preconditioner : P10StaticFixedRightPreconditioner family)
          (ug um ua etaR rhoAR : ℝ),
          p10StaticRightAttainableEnvelope choice preconditioner
              ug um ua etaR rhoAR =
            p10StaticFlexibleAttainableEnvelope choice preconditioner
                ug ua rhoAR +
              um * etaR *
                p10StaticRightPreconditionerKappa choice preconditioner := by
  -- PROOF_START P10-C1-H001
  sorry

end VSCLReuse

import VSCLReuse.P03.Definitions

namespace VSCLReuse

theorem p03_c1_lemma_4_3_exact_residual_bound
    {n : ℕ}
    (dimensionBounds : P03DimensionOnlyConstantBounds)
    (run : P03IterativeRefinementRun n)
    (norm : P03AbsoluteMonotoneNorm n)
    (constants : P03Lemma43Constants run norm dimensionBounds)
    (roundoff :
      P03Lemma43RoundoffAnalysis run norm dimensionBounds constants)
    (hsmall :
      constants.c8 * run.u * p03KappaInverse run norm ≤ 1 / 2) :
    ∀ m i,
      |p03ExactResidualAfterCorrection run m i| ≤
        p03Lemma43Bound constants m i := by
  -- PROOF_START P03-C1-H001
  sorry

end VSCLReuse

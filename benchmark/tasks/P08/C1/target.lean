import VSCLReuse.P08.Definitions

namespace VSCLReuse

theorem p08_c1_low_rank_matmul_error {b r : ℕ}
    (run : P08LowRankMatMulExecution b r) :
    let Atilde := p08LowRankMatrix run.XA run.YA
    let Btilde := p08LowRankMatrix run.YB run.XB
    let gammaC :=
      p08GammaReal (p08LowRankMatMulCost b r) run.unitRoundoff
    p08FrobNorm (run.trace.result - p08MatMul Atilde Btilde) ≤
        gammaC * p08FrobNorm Atilde * p08FrobNorm Btilde ∧
      p08FrobNorm (run.trace.result - p08MatMul run.A run.B) ≤
        gammaC * p08FrobNorm run.A * p08FrobNorm run.B +
          run.epsilon * (1 + gammaC) *
            (run.betaA * p08FrobNorm run.B +
              p08FrobNorm run.A * run.betaB +
              run.epsilon * run.betaA * run.betaB) := by
  -- PROOF_START P08-C1-H001
  sorry

end VSCLReuse

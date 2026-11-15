import VSCLReuse.P13.Definitions

namespace VSCLReuse

open scoped BigOperators Topology
open Filter

/-- P13-C1: the cycle-reindexed linear majorant constructed in Lemma 21. -/
theorem p13_c1_lemma21_linear_convergence
    (data : P13Lemma21Data) :
    (∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k))) ∧
      (∀ n,
        data.relativeEven n ≤
            p13LinearMajorant data.toP13WidthSequence n ∧
          data.relativeOdd n ≤
            p13LinearMajorant data.toP13WidthSequence n) ∧
      (∀ n, 0 ≤ p13LinearMajorant data.toP13WidthSequence n) ∧
      (∀ n, p13LinearMajorant data.toP13WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p13LinearMajorant data.toP13WidthSequence n) ∧
      Tendsto (p13LinearMajorant data.toP13WidthSequence) atTop (nhds 0) := by
  -- PROOF_START P13-C1-H001
  sorry

end VSCLReuse

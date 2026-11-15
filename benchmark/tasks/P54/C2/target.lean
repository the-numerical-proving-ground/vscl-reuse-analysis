import VSCLReuse.P54.Definitions

namespace VSCLReuse

/-- Both displayed conclusions (7) and (8) of Langlois--Louvet Lemma 1. -/
theorem p54_c2_lemma1 (fp : P54FPModel) (x : ℝ)
    (n : ℕ) (a b : List ℝ)
    (ha : a.length = n + 1) (hb : b.length = n + 1)
    (hvalid : P54GammaValid fp.u (2 * n + 1)) :
    |p54PolyDesc x (p54SumCoeffs a b) -
      p54Horner fp x (p54RoundedSumCoeffs fp a b)| ≤
        p54Gamma fp.u (2 * n + 1) *
          p54AbsDesc x (p54SumCoeffs a b) ∧
    p54AbsDesc x (p54SumCoeffs a b) ≤
      (1 + fp.u) ^ (2 * n + 1) *
        p54Horner fp |x|
          ((p54RoundedSumCoeffs fp a b).map abs) := by
  -- PROOF_START P54-C2-H001
  sorry

end VSCLReuse

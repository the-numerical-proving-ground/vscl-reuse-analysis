import VSCLReuse.P05.Definitions

namespace VSCLReuse

theorem p05_c2_exact_subtraction
    (fmt : P05RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P05NormalizedExponentRepresentation fmt x ex)
    (hy : P05NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p05FaithfulInFormat fmt (x - y) rounded) :
    p05FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P05-C2-H001
  sorry

end VSCLReuse

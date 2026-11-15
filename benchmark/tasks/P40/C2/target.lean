import VSCLReuse.P40.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Equation (2.3): the two-precision computed residual bound. -/
theorem p40_c2_two_precision_residual
    (fpHi fpLo : P40FPModel) (n : ℕ)
    (A : P40Matrix n n) (x b : Fin n → ℝ)
    (hvalid : P40GammaValid fpHi.u (n + 1))
    (_hprecision : fpHi.u ≤ fpLo.u) :
    ∀ i : Fin n,
      |p40StoredResidual fpHi fpLo n A x b i -
        (b i - ∑ j : Fin n, A i j * x j)| ≤
      fpLo.u * |b i - ∑ j : Fin n, A i j * x j| +
        (1 + fpLo.u) * p40Gamma fpHi.u (n + 1) *
          (|b i| + ∑ j : Fin n, |A i j| * |x j|) := by
  -- PROOF_START P40-C2-H001
  sorry

end VSCLReuse

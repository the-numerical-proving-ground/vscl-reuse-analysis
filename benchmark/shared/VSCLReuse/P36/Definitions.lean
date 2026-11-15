import Mathlib

open scoped BigOperators

namespace VSCLReuse

noncomputable def p36NodePolynomial {k : ℕ}
    (nodes : Fin k → ℝ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (nodes i))

noncomputable def p36Correction {k : ℕ}
    (nodes : Fin k → ℝ) : Polynomial ℝ :=
  let phi := p36NodePolynomial nodes;
  -(Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi.divX)

noncomputable def p36ExtendedApproximant {k : ℕ}
    (nodes : Fin k → ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  let phi := p36NodePolynomial nodes;
  p36Correction nodes +
    Polynomial.C ((Polynomial.eval 0 phi)⁻¹) * phi * p

noncomputable def p36IntervalFactor {k : ℕ}
    (a b : ℝ) (nodes : Fin k → ℝ) : ℝ :=
  |(Polynomial.eval 0 (p36NodePolynomial nodes))⁻¹| *
    ∏ i, max (b - nodes i) (nodes i - a)

end VSCLReuse

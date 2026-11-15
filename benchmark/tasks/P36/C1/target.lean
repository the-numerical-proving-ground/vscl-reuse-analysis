import VSCLReuse.P36.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P36-C1: the exceptional-point construction in Lemma 4.2. -/
theorem p36_c1_exceptional_point_approximation
    (k n : ℕ) (a b epsilon : ℝ)
    (nodes : Fin k → ℝ) (p : Polynomial ℝ)
    (ha : 0 < a) (hab : a < b)
    (hnodes : ∀ i, 0 < nodes i)
    (hinj : Function.Injective nodes)
    (hpdegree : p.natDegree ≤ n)
    (hpapprox : ∀ t, a ≤ t → t ≤ b →
      |t⁻¹ - Polynomial.eval t p| ≤ epsilon) :
    (p36ExtendedApproximant nodes p).natDegree ≤ n + k ∧
      (∀ i, Polynomial.eval (nodes i)
        (p36ExtendedApproximant nodes p) = (nodes i)⁻¹) ∧
      ∀ t, a ≤ t → t ≤ b →
        |t⁻¹ - Polynomial.eval t (p36ExtendedApproximant nodes p)| ≤
          p36IntervalFactor a b nodes * epsilon := by
  -- PROOF_START P36-C1-H001
  sorry

end VSCLReuse

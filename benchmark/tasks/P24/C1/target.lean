import VSCLReuse.P24.Definitions

namespace VSCLReuse

/-- P24-C1: the shifted-vector spanning equalities in Theorem 6.1. -/
theorem p24_c1_consecutive_shifted_vectors_span
    (n : ℕ) (hn : 0 < n)
    (A : Module.End ℝ (Fin n → ℝ)) (hA : Function.Bijective A)
    (B : Fin n → ℝ) (hB : B ≠ 0)
    (p : ℤ → ℝ) (v : ℤ → Fin n → ℝ)
    (hv0 : v 0 = B)
    (hstep : ∀ j, v (j + 1) = p24Shift A (p j) (v j))
    (hinv : ∀ j, Function.Bijective (p24Shift A (p j)))
    (s : ℤ) :
    p24TwoSidedSpan v = p24ConsecutiveSpan v s n ∧
      p24ConsecutiveSpan v s n = p24KrylovSpan A (v s) n ∧
      p24KrylovSpan A (v s) n = p24KrylovSpan A B n := by
  -- PROOF_START P24-C1-H001
  sorry

end VSCLReuse

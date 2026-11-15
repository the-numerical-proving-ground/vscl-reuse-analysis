import VSCLReuse.P32.Definitions

namespace VSCLReuse

/-- P32-C1: the real scalar specialization of the factorization in Lemma 3.4. -/
theorem p32_c1_first_companion_factorization
    (m : ℕ) (hm : 0 < m) (A : Fin (m + 1) → ℝ)
    (alpha beta : ℝ) :
    p32MatMul (p32Multiplier m A alpha beta)
        (p32FirstCompanion m hm A alpha beta) =
      fun i j => if i = j then p32Polynomial m A alpha beta else 0 := by
  -- PROOF_START P32-C1-H001
  sorry

end VSCLReuse

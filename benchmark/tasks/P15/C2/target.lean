import VSCLReuse.P15.Definitions

namespace VSCLReuse

theorem p15_c2_lemma_3_2
    (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P15RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p15FrobNorm (p15RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p15FrobNorm
        (p15Residual (p15RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P15-C2-H001
  sorry

end VSCLReuse

import VSCLReuse.P18.Definitions

namespace VSCLReuse

/-- P18-C2: the first-step Schur-complement error calculation in Appendix B. -/
theorem p18_c2_first_schur_error
    (fp : P18FPModel) (m r : ℕ)
    (A22 : P18Matrix m m) (L11 : P18Matrix m r)
    (A12 : P18Matrix r m)
    (hvalid : P18GammaValid fp.u r) :
    ∀ i j,
      |p18RoundedSchur fp A22 L11 A12 i j -
          p18ExactSchur A22 L11 A12 i j| ≤
        p18SchurErrorMajorant fp A22 L11 A12 i j := by
  -- PROOF_START P18-C2-H001
  sorry

end VSCLReuse

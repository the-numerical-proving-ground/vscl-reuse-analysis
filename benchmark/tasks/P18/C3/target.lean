import VSCLReuse.P18.Definitions

namespace VSCLReuse

/-- P18-C3: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p18_c3_ldlt_solve_backward_stability
    (fp : P18FPModel) (n : ℕ) (A L D E0 : P18Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p18LDLT L D = A + E0)
    (hE0 : p18EntryNorm E0 ≤ factorEta * p18EntryNorm A)
    (hDsolve : P18BlockSolveStable n D
      (p18ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P18Matrix n n),
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      p18EntryNorm ΔD ≤ eta * p18EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p18Gamma fp.u n * |p18Transpose L i j|) ∧
      F = p18TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p18BackSub fp n (p18Transpose L) z j = b i) ∧
      p18EntryNorm F ≤
        p18TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P18-C3-H001
  sorry

end VSCLReuse

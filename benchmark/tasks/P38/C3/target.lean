import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- The Method B off-diagonal block estimate in the proof of (6.1). -/
theorem p38_c3_methodB_offdiagonal_residual
    (fp : P38FPModel) (n r p : ℕ)
    (L22 : P38Matrix n n) (L21 : P38Matrix n r)
    (X11 : P38Matrix r p)
    (hdiag : ∀ i, L22 i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L22 i j = 0)
    (hn : P38GammaValid fp.u n)
    (hr : P38GammaValid fp.u r) :
    ∀ i j,
      |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
      p38Gamma fp.u r *
        (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
  -- PROOF_START P38-C3-H001
  sorry

end VSCLReuse

import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- P08-C3: complete Theorem 4.4 for a triangular BLR block system. -/
theorem p08_c3_blr_triangular_backward_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b)
    (trace : P08BLRTrace fp T X Y v)
    (hp : 0 < p) (hb : 0 < b)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hupper : ∀ i j : Fin p, i < j → T i j = 0)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    let x := trace.x
    let c := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)
    ∃ DT : P08BlockMatrix p b, ∃ dv : P08BlockVector p b,
      Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
          (p08AssembleVector x) =
        p08AssembleVector v + p08AssembleVector dv ∧
      p08BlockFrobNorm DT ≤
        p08GammaReal c fp.u * p08BlockFrobNorm T ∧
      p08BlockVecNorm dv ≤
        p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
  -- PROOF_START P08-C3-H001
  sorry

end VSCLReuse

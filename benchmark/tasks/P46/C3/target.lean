import VSCLReuse.P46.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Section 3.2: high-precision kernels rounded once to low precision. -/
theorem p46_c3_simulated_product_and_triangular_solve
    (fp : P46TriFPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hu : 0 < fp.u)
    (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    (∀ i j,
      |p46SimulatedMatMul fp.toP46FPModel A B i j - p46MatMul A B i j| ≤
        2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j) ∧
    (∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j|) := by
  -- PROOF_START P46-C3-H001
  sorry

end VSCLReuse

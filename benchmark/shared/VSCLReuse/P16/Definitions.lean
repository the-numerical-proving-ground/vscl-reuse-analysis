import Mathlib

namespace VSCLReuse

open scoped BigOperators

abbrev P16Vector (n : ℕ) := Fin n → ℝ

abbrev P16Coupling (k q : ℕ) := Matrix (Fin k) (Fin q) ℝ

noncomputable def p16VecNormSq {n : ℕ} (x : P16Vector n) : ℝ :=
  ∑ i, x i ^ 2

noncomputable def p16PairNormSq {k q : ℕ}
    (u : P16Vector k) (v : P16Vector q) : ℝ :=
  p16VecNormSq u + p16VecNormSq v

noncomputable def p16MatVec {k q : ℕ}
    (X : P16Coupling k q) (v : P16Vector q) : P16Vector k :=
  fun i ↦ ∑ j, X i j * v j

/-- The action of the block matrix `W₁` in the proof of Theorem 3.2. -/
noncomputable def p16W1 {k q : ℕ} (X : P16Coupling k q) (α : ℝ)
    (u : P16Vector k) (v : P16Vector q) : P16Vector k × P16Vector q :=
  (u + p16MatVec X v, α • v)

/-- The action of the block matrix `W₂` in the proof of Theorem 3.2. -/
noncomputable def p16W2 {k q : ℕ} (X : P16Coupling k q) (α : ℝ)
    (u : P16Vector k) (v : P16Vector q) : P16Vector k × P16Vector q :=
  (α • u - p16MatVec X v, v)

/-- A squared Euclidean operator-gain bound for a block transformation. -/
def P16SquaredGainBound {k q : ℕ}
    (W : P16Vector k → P16Vector q → P16Vector k × P16Vector q)
    (gSq : ℝ) : Prop :=
  ∀ u v, p16PairNormSq (W u v).1 (W u v).2 ≤
    gSq * p16PairNormSq u v

/-- The quantities used in the proof of Theorem 3.2.  Here `X` represents
`Aₖ⁻¹Bₖ`, `ratio i j` represents `γⱼ(Cₖ)/ωᵢ(Aₖ)`, and the final
two fields are the two applications of the cited singular-value product
comparison. -/
structure P16Theorem32Data (k q : ℕ) where
  f : ℝ
  X : P16Coupling k q
  ratio : P16Coupling k q
  alpha : ℝ
  sigmaMTop : Fin k → ℝ
  sigmaMTail : Fin q → ℝ
  sigmaA : Fin k → ℝ
  sigmaC : Fin q → ℝ
  p_lt_f : ∀ i j, X i j ^ 2 + ratio i j ^ 2 < f ^ 2
  alpha_sq_le : alpha ^ 2 ≤ ∑ i, ∑ j, ratio i j ^ 2
  hornJohnson_top : ∀ gSq, 0 ≤ gSq →
    P16SquaredGainBound (p16W1 X alpha) gSq →
    ∀ i, sigmaMTop i ≤ sigmaA i * Real.sqrt gSq
  hornJohnson_tail : ∀ gSq, 0 ≤ gSq →
    P16SquaredGainBound (p16W2 X alpha) gSq →
    ∀ j, sigmaC j ≤ sigmaMTail j * Real.sqrt gSq

noncomputable def p16StrongFactor (k q : ℕ) (f : ℝ) : ℝ :=
  Real.sqrt (1 + f ^ 2 * (k : ℝ) * (q : ℝ))

end VSCLReuse

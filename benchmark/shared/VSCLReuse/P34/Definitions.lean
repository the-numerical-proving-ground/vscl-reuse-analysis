import Mathlib

open scoped BigOperators

namespace VSCLReuse

abbrev P34Vector (n : ℕ) := Fin n → ℝ

/-- The squared modified coordinate from equation (3.2). -/
noncomputable def p34SecularWeight {n : ℕ}
    (d lambda : P34Vector n) (i : Fin n) : ℝ :=
  (∏ j, (lambda j - d i)) /
    (∏ j ∈ Finset.univ.erase i, (d j - d i))

/-- The secular function used in Lemma 1 and Sections 3--4. -/
noncomputable def p34Secular {n : ℕ}
    (d weight : P34Vector n) (x : ℝ) : ℝ :=
  1 + ∑ i, weight i / (d i - x)

/-- The product formula (3.3) for the modified coordinate. -/
noncomputable def p34ModifiedCoordinate {n : ℕ}
    (d lambda : P34Vector n) (i : Fin n) : ℝ :=
  Real.sqrt (p34SecularWeight d lambda i)

/-- The product on either side of the determinant identity preceding (3.2). -/
noncomputable def p34Characteristic {n : ℕ}
    (v : P34Vector n) : Polynomial ℝ :=
  ∏ i, (Polynomial.C (v i) - Polynomial.X)

/-- The factor left after removing the pole indexed by `i` from the diagonal
characteristic product. -/
noncomputable def p34DeletedCharacteristic {n : ℕ}
    (d : P34Vector n) (i : Fin n) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.C (d j) - Polynomial.X)

end VSCLReuse

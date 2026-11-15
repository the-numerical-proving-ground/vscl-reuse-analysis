import Mathlib

open scoped BigOperators

namespace VSCLReuse

noncomputable def p37Mu (nodes : ℕ → ℝ)
    (n d i : ℕ) (x : ℝ) : ℝ :=
  (∏ j ∈ Finset.range i, (x - nodes j)) *
    ∏ j ∈ Finset.Ico (i + d + 1) (n + 1), (nodes j - x)

noncomputable def p37Denominator (nodes : ℕ → ℝ)
    (n d : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n - d + 1), p37Mu nodes n d i x

end VSCLReuse

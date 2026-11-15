import VSCLReuse.P37.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P37-C1: the interior-interval positivity argument in Theorem 1. -/
theorem p37_c1_denominator_positive_between_nodes
    (nodes : ℕ → ℝ) (hmono : StrictMono nodes)
    (n d alpha : ℕ) (x : ℝ)
    (hdpos : 0 < d) (hdn : d ≤ n) (halpha : alpha < n)
    (hxlo : nodes alpha < x) (hxhi : x < nodes (alpha + 1)) :
    0 < p37Denominator nodes n d x := by
  -- PROOF_START P37-C1-H001
  sorry

end VSCLReuse

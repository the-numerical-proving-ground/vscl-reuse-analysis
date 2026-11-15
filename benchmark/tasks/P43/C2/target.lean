import VSCLReuse.P43.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Castaldo–Whaley–Chronopoulos, full Proposition 3.2, equation (3.2). -/
theorem p43_c2_full_superblock_dot_error
    (fp : P43FPModel) (b t : ℕ) (hb : 0 < b) (ht : 0 < t)
    (tree : P43DotTree b t)
    (hvalid : P43GammaValid fp.u (t * (b - 1) + 1)) :
    |tree.computed fp - tree.exact| ≤
      p43Gamma fp.u (t * (b - 1) + 1) * tree.absMass := by
  -- PROOF_START P43-C2-H001
  sorry

end VSCLReuse

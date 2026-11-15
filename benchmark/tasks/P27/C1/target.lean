import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open Matrix

namespace VSCLReuse

/-- P27-C1: the augmented-matrix phi-function column identity of Theorem 2.1. -/
theorem p27_c1_augmented_phi_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      ∑ r : Fin (j.val + 1),
        τ ^ (r.val + 1) *
          (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
            (p27ReverseColumn W j r)) i := by
  -- PROOF_START P27-C1-H001
  sorry

end VSCLReuse

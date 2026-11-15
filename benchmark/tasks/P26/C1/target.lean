import VSCLReuse.P26.Definitions

namespace VSCLReuse

/-- P26-C1: the weighted positive-semidefinite projection formula of Theorem 3.2. -/
theorem p26_c1_weighted_psd_projection
    (n : ℕ)
    (A S Sinv Q : Matrix (Fin n) (Fin n) ℝ) (lambda : Fin n → ℝ)
    (hSsymm : S.transpose = S)
    (hSinvSymm : Sinv.transpose = Sinv)
    (hSInv : S * Sinv = 1)
    (hInvS : Sinv * S = 1)
    (hQtQ : Q.transpose * Q = 1)
    (hQQt : Q * Q.transpose = 1)
    (hSpectral : S * A * S = Q * Matrix.diagonal lambda * Q.transpose) :
    let X := p26WeightedPsdProjection Sinv Q lambda
    X.PosSemidef ∧
      (∀ Z : Matrix (Fin n) (Fin n) ℝ,
        Z.PosSemidef →
          p26WeightedFrobeniusSq S (A - X) ≤
            p26WeightedFrobeniusSq S (A - Z)) ∧
      ∀ i, A i i ≤ X i i := by
  -- PROOF_START P26-C1-H001
  sorry

end VSCLReuse

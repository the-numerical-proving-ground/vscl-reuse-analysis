import VSCLReuse.P35.Definitions

namespace VSCLReuse

open Matrix

/-- P35-C1: Theorem 4.1, equations (4.6)--(4.7). -/
theorem p35_c1_loss_of_biorthogonality
    (k : ℕ)
    (T C Delta D F G K L N M : P35Matrix (k + 1))
    (a b z w : P35Vector (k + 1))
    (beta gamma theta : ℝ)
    (ha : a (Fin.last k) = 0)
    (hb : b (Fin.last k) = 0)
    (hmaster :
      gamma • p35Outer (p35LastBasis k) a -
          beta • p35Outer b (p35LastBasis k) =
        (C * T - T * C) + (Delta * T - T * Delta) +
          (D * T - T * D) + (F - G))
    (hDelta : Delta * T - T * Delta = K - L)
    (herror : F - G = N - M)
    (hCT : p35StrictLower (C * T - T * C))
    (hDT : p35StrictUpper (D * T - T * D))
    (hK : p35StrictLower K) (hL : p35StrictUpper L)
    (hN : p35StrictLower N) (hM : p35StrictUpper M)
    (hz : T *ᵥ z = theta • z)
    (hw : w ᵥ* T = theta • w)
    (hgamma : gamma * (w ⬝ᵥ p35LastBasis k) ≠ 0)
    (hbeta : beta * (p35LastBasis k ⬝ᵥ z) ≠ 0) :
    a ⬝ᵥ z =
        (w ⬝ᵥ ((K + N) *ᵥ z)) /
          (gamma * (w ⬝ᵥ p35LastBasis k)) ∧
      w ⬝ᵥ b =
        (w ⬝ᵥ ((L + M) *ᵥ z)) /
          (beta * (p35LastBasis k ⬝ᵥ z)) := by
  -- PROOF_START P35-C1-H001
  sorry

end VSCLReuse

import VSCLReuse.P29.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P29-C1: the inverse-action and multiplier bounds used in Theorem 3.6. -/
theorem p29_c1_calu_multiplier_growth
    (b H : ℕ) (ell : ℕ → ℕ → ℕ → ℝ)
    (probeIn probeOut z : ℕ → ℕ → ℝ)
    (hp : P29CALUMultiplierProcess b H ell probeIn probeOut z) :
    (∀ h, h < H → ∀ i, i < b →
      |probeOut h i| ≤ (2 : ℝ) ^ i) ∧
    (∀ i, i < b → |z H i| ≤ (2 : ℝ) ^ (b * H)) := by
  -- PROOF_START P29-C1-H001
  sorry

end VSCLReuse

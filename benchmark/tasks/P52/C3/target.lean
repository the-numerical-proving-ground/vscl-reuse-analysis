import VSCLReuse.P52.Definitions

namespace VSCLReuse

open scoped BigOperators

theorem p52_c3_theorem2_full_named
    (N M : ℕ) (a f : Fin N → ℝ) (b : Fin M → ℝ)
    (A B CA CB betaBound : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hN : 0 < N) (hM : 0 < M)
    (hD0 : (∑ j : Fin M, b j) ≠ 0)
    (hbetaBound : p52DenominatorCondition M b ≤ betaBound)
    (hbetaBound0 : 0 ≤ betaBound) :
    ∃ u0 C : ℝ, 0 < u0 ∧ 0 ≤ C ∧
      ∀ (fp : P52FPModel) (ahat : Fin N → ℝ) (bhat : Fin M → ℝ),
      fp.u ≤ u0 →
      (∀ i, ∃ alpha_i : ℝ,
        ahat i = a i * (1 + alpha_i) ∧
          |alpha_i| ≤ A * fp.u + CA * fp.u ^ 2) →
      (∀ j, ∃ beta_j : ℝ,
        bhat j = b j * (1 + beta_j) ∧
          |beta_j| ≤ B * fp.u + CB * fp.u ^ 2) →
      ∃ fhat : Fin N → ℝ,
        p52ComputedQuotient fp N M ahat f bhat =
          (∑ i : Fin N, a i * fhat i) / (∑ j : Fin M, b j) ∧
        ‖fhat - f‖ ≤
          ((((N : ℝ) + 1 + A) +
            (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
            C * fp.u ^ 2) * ‖f‖ := by
  -- PROOF_START P52-C3-H001
  sorry

end VSCLReuse

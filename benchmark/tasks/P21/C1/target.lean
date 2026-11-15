import VSCLReuse.P21.Definitions

namespace VSCLReuse

/-- P21-C1: Lemma 4.1 and the structural guarantees of Algorithm 4.1. -/
theorem p21_c1_dqd2_refactorization
    (n q : ℕ) (b c : ℕ → ℝ)
    (hn : 0 < n) (hqpos : 0 < q) (hqn : q ≤ n)
    (hb : ∀ i, i < n → 0 ≤ b i)
    (hc : ∀ i, i < n → 0 ≤ c i)
    (hbefore : ∀ i, 0 < i → i < q → 0 < b i)
    (hzero : ∀ i, i + 1 < n → c i = 0 → b (i + 1) = 0)
    (hstop : q < n → b q = 0) :
    (∀ i, i < n → 0 ≤ p21DqdB q b c i) ∧
    (∀ i, i < n → 0 ≤ p21DqdC q b c i) ∧
    p21DqdB q b c 0 = 0 ∧
    p21UnitLowerBidiagonal n (p21DqdB q b c) *
        p21UnitLowerBidiagonal n (p21DqdC q b c) =
      p21UnitLowerBidiagonal n b * p21UnitLowerBidiagonal n c ∧
    (∀ i, 0 < i → i < n →
      (p21DqdB q b c i = 0 ↔ b i = 0)) ∧
    (∀ i, i < n → p21DqdC q b c i = 0 → c i = 0) ∧
    (∀ i, i < n → c i = 0 → p21DqdC q b c i ≠ 0 → i + 1 = q) ∧
    (∀ i, q ≤ i →
      p21DqdB q b c i = b i ∧ p21DqdC q b c i = c i) ∧
    4 * q ≤ 4 * n := by
  -- PROOF_START P21-C1-H001
  sorry

end VSCLReuse

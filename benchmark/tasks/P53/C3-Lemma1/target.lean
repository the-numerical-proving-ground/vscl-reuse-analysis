import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

theorem p53_lemma1_whole (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ)
    (hn : 0 < n)
    (hrec : P53GammaValid fp.u n) :
    (|p53Dot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u n * ∑ i : Fin n, |a i| * |x i|) ∧
    (|p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 n + 1) *
        ∑ i : Fin n, |a i| * |x i|) := by
  -- PROOF_START P53-C3-Lemma1-H001
  sorry

end VSCLReuse

import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Blanchard–Higham–Higham, full Theorem 3.3, equation (3.6). -/
theorem p07_c2_full_basic_softmax_algorithm
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P07BasicSumExecution x (u t))
    (divError : ∀ t, Fin n → ℝ)
    (hdiv : ∀ t i, |divError t i| ≤ u t)
    (hu : Filter.Tendsto u l (nhds 0)) :
    ∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        ‖(fun i : Fin n =>
            p07ComputedSoftmax (run t) (divError t) i -
              p07ExactSoftmax x i)‖ /
          ‖(fun i : Fin n => p07ExactSoftmax x i)‖ ≤
          (n + 3 : ℝ) * u t + |remainder t| := by
  -- PROOF_START P07-C2-H001
  sorry

end VSCLReuse

import VSCLReuse.P51.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- Complete componentwise sparse matrix-vector result of Lemma 3.2. -/
theorem p51_c2_lemma32 {m n l : ℕ} (fp : P51FPModel)
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (η : ℝ)
    (hln : 2 ≤ l ∧ l < n) (hvalid : P51GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin m) :
    |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, A i j * x j| ≤
      p51Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
      (η * fp.u + p51Gamma fp.u l * (η * fp.u)) *
        (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
  -- PROOF_START P51-C2-H001
  sorry

end VSCLReuse

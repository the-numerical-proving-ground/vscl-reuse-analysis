import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

theorem p53_theorem2_all_schedules {n l : ℕ} (fp : P53FPModel)
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (η : ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ l)
    (hln : 2 ≤ l ∧ l ≤ n) (hvalid : P53GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0) :
    ∀ schedule : P53SparseSchedule A l,
      (∀ i : Fin n,
        |p53SparseMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, A i j * x j| ≤
          p53Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
          (η * fp.u + p53Gamma fp.u l * (η * fp.u)) *
            (∑ j : Fin n, |p53Sign (A i j)| * |x j|)) ∧
      (∀ i : Fin n,
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, A i j * x j| ≤
          p53Gamma fp.u (Nat.clog 2 l + 1) *
            (∑ j : Fin n, |A i j| * |x j|) +
          (η * fp.u +
            p53Gamma fp.u (Nat.clog 2 l + 1) * (η * fp.u)) *
            (∑ j : Fin n, |p53Sign (A i j)| * |x j|)) := by
  -- PROOF_START P53-C3-H001
  sorry

end VSCLReuse

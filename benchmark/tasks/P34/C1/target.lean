import VSCLReuse.P34.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P34-C1: the inverse secular construction in equations (3.2)--(3.3). -/
theorem p34_c1_inverse_secular_construction
    (n : ℕ) (hn : 0 < n)
    (d lambda : P34Vector n)
    (hd : StrictMono d)
    (hlower : ∀ i, d i < lambda i)
    (hupper : ∀ i j, i < j → lambda i < d j) :
    (∀ i, 0 < p34SecularWeight d lambda i) ∧
      p34Characteristic lambda =
        p34Characteristic d +
          ∑ i, Polynomial.C (p34SecularWeight d lambda i) *
            p34DeletedCharacteristic d i := by
  -- PROOF_START P34-C1-H001
  sorry

end VSCLReuse

import VSCLReuse.P47.Definitions

namespace VSCLReuse

theorem p47_c1_theorem2_1_at_least {n p : ℕ}
    (A B C : Matrix (Fin n) (Fin n) ℂ)
    (lambda : Fin p → ℂ) (hinj : Function.Injective lambda)
    (v : Fin p → Fin n → ℂ)
    (hnp : n ≤ p) (hp2n : p ≤ 2 * n)
    (hEig : ∀ a : Fin p,
      (p47Polynomial A B C (lambda a)).mulVec (v a) = 0)
    (hHaar : ∀ (s : Finset (Fin p)) (hs : s.card = n),
      IsUnit (p47EigenvectorMatrix v s hs).det) :
    let solvents :=
      (Finset.univ : Finset {s : Finset (Fin p) // s.card = n}).image
        (fun s => p47Solvent lambda v s.val s.property)
    solvents.card = Nat.choose p n ∧
      ∀ X ∈ solvents, A * X * X + B * X + C = 0 := by
  -- PROOF_START P47-C1-H001
  sorry

end VSCLReuse

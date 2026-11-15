import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

/-- One fan-in node product error propagated through a left factor. -/
theorem p38_c2_fanin_one_node_propagated_error
    (fp : P38FPModel) (r m n p : ℕ)
    (L : P38Matrix r m) (A : P38Matrix m n) (B : P38Matrix n p)
    (hvalid : P38GammaValid fp.u n) :
    ∀ i : Fin r, ∀ j : Fin p,
      |∑ k : Fin m, L i k *
        (p38RoundedMatMul fp A B k j - p38MatMul A B k j)| ≤
      p38Gamma fp.u n *
        ∑ k : Fin m, |L i k| *
          (∑ t : Fin n, |A k t| * |B t j|) := by
  -- PROOF_START P38-C2-H001
  sorry

end VSCLReuse

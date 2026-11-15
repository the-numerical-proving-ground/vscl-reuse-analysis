import VSCLReuse.P33.Definitions

open scoped BigOperators

namespace VSCLReuse

/-- P33-C1: the subdiagonal product and nontriviality result of Theorem 4.5. -/
theorem p33_c1_core_subdiagonal_product
    (n : ℕ) (hn : 0 < n) (run : P33CoreRollupRun n)
    (x : P33Vector n) (alpha a0 : ℂ)
    (hx : x = alpha • run.state n)
    (hxlast : x ⟨n, by omega⟩ = -1)
    (halpha : ‖alpha‖ = p33VecNorm2 x)
    (hvw : ∀ i, ‖run.v i‖ = ‖run.w i‖)
    (Ctail Rtail Htail : P33Matrix n)
    (hCdiag : ∀ i, Ctail i i = run.w i)
    (hCtri : Ctail.BlockTriangular id)
    (hRtri : Rtail.BlockTriangular id)
    (hHtail : Htail = Ctail * Rtail)
    (hdetR : ‖Matrix.det Rtail‖ = ‖a0‖)
    (ha0 : a0 ≠ 0) :
    (∀ i, 0 < ‖Htail i i‖) ∧
      (∏ i, ‖Htail i i‖) = ‖a0‖ / p33VecNorm2 x := by
  -- PROOF_START P33-C1-H001
  sorry

end VSCLReuse

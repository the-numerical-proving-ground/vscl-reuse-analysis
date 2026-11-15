import VSCLReuse.P02.Definitions

namespace VSCLReuse

theorem p02_c1_householder_product_first_order_expansion
    {Omega : Type*} [MeasurableSpace Omega] {m r : ℕ}
    (model : P02Model15 Omega)
    (run : P02HouseholderApplicationFamily Omega m r model)
    (c5 : ℕ) (lambda : ℝ) (_hc5 : 0 < c5) (_hlambda : 0 < lambda)
    (hlocal : P02Lemma42VectorAssumption run c5 lambda) :
    ∃ (unfactoredRemainder factoredRemainder :
        ℝ → Omega → Matrix (Fin m) (Fin m) ℝ),
      (∀ omega, omega ∈ hlocal.localEvent →
        p02MatrixSecondOrderAtZero
          (fun u ↦ unfactoredRemainder u omega)) ∧
      (∀ omega, omega ∈ hlocal.localEvent →
        p02MatrixSecondOrderAtZero
          (fun u ↦ factoredRemainder u omega)) ∧
      (∀ u omega,
        run.computed u omega =
          p02ApplicationExactState run +
            p02MatVec
              (p02ApplicationFirstOrderMatrix run u omega +
                unfactoredRemainder u omega)
              run.b) ∧
      (∀ u omega,
        run.computed u omega =
            p02ApplicationExactState run +
            p02MatVec
              (Matrix.transpose (p02ApplicationQ run) *
                (p02ApplicationFSum run u omega +
                  factoredRemainder u omega))
              run.b) ∧
      ∀ u omega (j : Fin r),
        p02ApplicationF run u omega j =
          Matrix.transpose
              (p02HouseholderProduct
                (p02HouseholderSequenceMatrix run.householderVector)
                (j.val + 1)) *
            run.localPerturbation u j.val omega *
              p02HouseholderProduct
                (p02HouseholderSequenceMatrix run.householderVector) j.val := by
  -- PROOF_START P02-C1-H001
  sorry

end VSCLReuse

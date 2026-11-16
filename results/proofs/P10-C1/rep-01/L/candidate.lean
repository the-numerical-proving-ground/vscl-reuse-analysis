import VSCLReuse.P10.Definitions

namespace VSCLReuse

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private lemma p10VecNorm2_eq_euclidean {n : ℕ} (x : P10Vector n) :
    p10VecNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [p10VecNorm2, p10VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private lemma p10VecNorm2_nonneg {n : ℕ} (x : P10Vector n) :
    0 ≤ p10VecNorm2 x := by
  rw [p10VecNorm2_eq_euclidean]
  exact norm_nonneg _

private lemma p10VecNorm2_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  simp only [p10VecNorm2_eq_euclidean]
  convert norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n)) using 1

private lemma p10_select_iteration {n : ℕ} {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  have aux : ∀ (m k : ℕ) (hk : 0 < k) (hkn : k + m = n),
      p10IterationWellConditioned
        (family.iteration ⟨k, hk, by omega⟩) →
      ∃ j : P10Theorem31Dimension n,
        p10IterationWellConditioned (family.iteration j) ∧
          (j.1 = n ∨ p10MGSNearDependence (family.iteration j)) := by
    intro m
    induction m with
    | zero =>
      intro k hk hkn hgood
      refine ⟨⟨k, hk, by omega⟩, hgood, Or.inl ?_⟩
      omega
    | succ m ih =>
      intro k hk hkn hgood
      have hklt : k < n := by omega
      let current : P10Theorem31Dimension n :=
        ⟨k, hk, Nat.le_of_lt hklt⟩
      let next : P10Theorem31Dimension n :=
        ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
      by_cases hnext : p10IterationWellConditioned (family.iteration next)
      · have hnext_eq : (k + 1) + m = n := by omega
        exact ih (k + 1) (Nat.succ_pos k) hnext_eq (by simpa [next] using hnext)
      · refine ⟨current, ?_, Or.inr ?_⟩
        · simpa [current] using hgood
        · exact mgs.loss_implies_near_dependence k hk hklt hnext
  have hn := family.system.dimension_pos
  exact aux (n - 1) 1 Nat.zero_lt_one (by omega) mgs.first_dimension_good

private lemma p10VecNorm2_three_div_le {n : ℕ}
    (a b r : P10Vector n) (d : ℝ) (hd : 0 ≤ d) :
    p10VecNorm2 (a + b + r) / d ≤
      p10VecNorm2 a / d + p10VecNorm2 b / d + p10VecNorm2 r / d := by
  have h₁ := p10VecNorm2_add_le a b
  have h₂ := p10VecNorm2_add_le (a + b) r
  have h : p10VecNorm2 (a + b + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r := by linarith
  calc
    _ ≤ (p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r) / d :=
      div_le_div_of_nonneg_right h hd
    _ = _ := by ring

private lemma p10VecNorm2_four_div_le {n : ℕ}
    (a b c r : P10Vector n) (d : ℝ) (hd : 0 ≤ d) :
    p10VecNorm2 (a + b + c + r) / d ≤
      p10VecNorm2 a / d + p10VecNorm2 b / d +
        p10VecNorm2 c / d + p10VecNorm2 r / d := by
  have h₁ := p10VecNorm2_add_le a b
  have h₂ := p10VecNorm2_add_le (a + b) c
  have h₃ := p10VecNorm2_add_le (a + b + c) r
  have h : p10VecNorm2 (a + b + c + r) ≤
      p10VecNorm2 a + p10VecNorm2 b +
        p10VecNorm2 c + p10VecNorm2 r := by linarith
  calc
    _ ≤ (p10VecNorm2 a + p10VecNorm2 b +
        p10VecNorm2 c + p10VecNorm2 r) / d :=
      div_le_div_of_nonneg_right h hd
    _ = _ := by ring

private lemma p10_static_kappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
    change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
    have hA : 0 ≤ p10FrobNorm A := by unfold p10FrobNorm; exact norm_nonneg A
    have hAinv : 0 ≤ p10FrobNorm Ainv := by unfold p10FrobNorm; exact norm_nonneg Ainv
    exact mul_nonneg hAinv hA
  | inducedTwo =>
    change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
    have hA : 0 ≤ p10OpNorm2 A := by
      unfold p10OpNorm2
      exact @norm_nonneg _
        Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup A
    have hAinv : 0 ≤ p10OpNorm2 Ainv := by
      unfold p10OpNorm2
      exact @norm_nonneg _
        Matrix.instL2OpNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup Ainv
    exact mul_nonneg hA hAinv

private lemma p10_right_magnitude_bound
    (d ug um ua eta rho kop kmr ksys g r m : ℝ)
    (hkop : 0 ≤ kop) (hkmr : 0 ≤ kmr) (hksys : 0 ≤ ksys)
    (hrho : 0 ≤ rho) (hg : g ≤ d * ug)
    (hr : r ≤ d * um * eta) (hm : m ≤ d * ua) :
    g * kop * kmr + r * kmr + m * ksys * rho ≤
      d * (ug * kop * kmr + um * eta * kmr + ua * ksys * rho) := by
  have hg' : g * kop * kmr ≤ (d * ug) * kop * kmr :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hkop) hkmr
  have hr' : r * kmr ≤ (d * um * eta) * kmr :=
    mul_le_mul_of_nonneg_right hr hkmr
  have hm' : m * ksys * rho ≤ (d * ua) * ksys * rho :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hksys) hrho
  calc
    _ ≤ (d * ug) * kop * kmr + (d * um * eta) * kmr +
        (d * ua) * ksys * rho := by linarith
    _ = _ := by ring

private lemma p10_flexible_magnitude_bound
    (d ug ua rho kop kmr ksys g m : ℝ)
    (hkop : 0 ≤ kop) (hkmr : 0 ≤ kmr) (hksys : 0 ≤ ksys)
    (hrho : 0 ≤ rho) (hg : g ≤ d * ug) (hm : m ≤ d * ua) :
    g * kop * kmr + m * ksys * rho ≤
      d * (ug * kop * kmr + ua * ksys * rho) := by
  have hg' : g * kop * kmr ≤ (d * ug) * kop * kmr :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hg hkop) hkmr
  have hm' : m * ksys * rho ≤ (d * ua) * ksys * rho :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hksys) hrho
  calc
    _ ≤ (d * ug) * kop * kmr + (d * ua) * ksys * rho := by linarith
    _ = _ := by ring

private lemma p10_right_bound_at {n : ℕ}
    (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice)
    (right : P10StaticRightFamily n semantics)
    (appendix : P10StaticRightAppendixCTheory choice right)
    (k : P10Theorem31Dimension n)
    (hgood : p10IterationWellConditioned (right.family.iteration k))
    (hstop : k.1 = n ∨ p10MGSNearDependence (right.family.iteration k))
    (hcond : P10StaticRightConditions choice (right.iteration k)) :
    p10FirstOrderLe semantics
      (p10ForwardError right.family.system.xExact
        (right.family.iteration k).xHat)
      ((right.family.iteration k).dimensionFactor *
        p10StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug (right.iteration k).core.um
          (right.iteration k).core.ua (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR) := by
  let e := appendix.expansion k hgood hstop hcond
  let d := p10VecNorm2 right.family.system.xExact
  let rem := p10VecNorm2 e.remainder / d
  have hkop : 0 ≤ p10StaticRightOperatorKappa choice right.preconditioner :=
    p10_static_kappa_nonneg choice _ _
  have hkmr : 0 ≤ p10StaticRightPreconditionerKappa choice right.preconditioner :=
    p10_static_kappa_nonneg choice _ _
  have hksys : 0 ≤ p10StaticSystemKappa choice right.family :=
    p10_static_kappa_nonneg choice _ _
  have hmag :
      (right.iteration k).core.gmresMagnitude *
          p10StaticRightOperatorKappa choice right.preconditioner *
            p10StaticRightPreconditionerKappa choice right.preconditioner +
        (right.iteration k).reapplicationMagnitude *
          p10StaticRightPreconditionerKappa choice right.preconditioner +
        (right.iteration k).core.matrixMagnitude *
          p10StaticSystemKappa choice right.family *
            (right.iteration k).core.rhoAR ≤
      (right.family.iteration k).dimensionFactor *
        p10StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug (right.iteration k).core.um
          (right.iteration k).core.ua (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR := by
    simpa only [p10StaticRightAttainableEnvelope] using
      p10_right_magnitude_bound
        (right.family.iteration k).dimensionFactor
        (right.iteration k).core.ug (right.iteration k).core.um
        (right.iteration k).core.ua (right.iteration k).core.etaR
        (right.iteration k).core.rhoAR
        (p10StaticRightOperatorKappa choice right.preconditioner)
        (p10StaticRightPreconditionerKappa choice right.preconditioner)
        (p10StaticSystemKappa choice right.family)
        (right.iteration k).core.gmresMagnitude
        (right.iteration k).reapplicationMagnitude
        (right.iteration k).core.matrixMagnitude
        hkop hkmr hksys hcond.core.parameters_nonneg.2.2.2.2
        hcond.core.gmres_magnitude_bound
        hcond.reapplication_magnitude_bound
        hcond.core.matrix_magnitude_bound
  refine ⟨rem, e.remainder_second_order, ?_⟩
  change p10VecNorm2
      ((right.family.iteration k).xHat - right.family.system.xExact) / d ≤
    (right.family.iteration k).dimensionFactor *
      p10StaticRightAttainableEnvelope choice right.preconditioner
        (right.iteration k).core.ug (right.iteration k).core.um
        (right.iteration k).core.ua (right.iteration k).core.etaR
        (right.iteration k).core.rhoAR + |rem|
  rw [e.error_decomposition]
  calc
    _ ≤ p10VecNorm2 e.gmresContribution / d +
          p10VecNorm2 e.reapplicationContribution / d +
          p10VecNorm2 e.matrixContribution / d + rem :=
      p10VecNorm2_four_div_le _ _ _ _ d (p10VecNorm2_nonneg _)
    _ ≤ (right.iteration k).core.gmresMagnitude *
            p10StaticRightOperatorKappa choice right.preconditioner *
              p10StaticRightPreconditionerKappa choice right.preconditioner +
          (right.iteration k).reapplicationMagnitude *
            p10StaticRightPreconditionerKappa choice right.preconditioner +
          (right.iteration k).core.matrixMagnitude *
            p10StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR + rem := by
      dsimp [rem, d]
      linarith [e.gmres_gain_bound, e.reapplication_gain_bound,
        e.matrix_gain_bound]
    _ ≤ _ := by linarith [le_abs_self rem]

private lemma p10_flexible_bound_at {n : ℕ}
    (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice)
    (flexible : P10StaticFlexibleFamily n semantics)
    (appendix : P10StaticFlexibleAppendixDTheory choice flexible)
    (k : P10Theorem31Dimension n)
    (hgood : p10IterationWellConditioned (flexible.family.iteration k))
    (hstop : k.1 = n ∨ p10MGSNearDependence (flexible.family.iteration k))
    (hcond : P10StaticFlexibleConditions choice (flexible.iteration k)) :
    p10FirstOrderLe semantics
      (p10ForwardError flexible.family.system.xExact
        (flexible.family.iteration k).xHat)
      ((flexible.family.iteration k).dimensionFactor *
        p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
          (flexible.iteration k).core.ug (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR) := by
  let e := appendix.expansion k hgood hstop hcond
  let d := p10VecNorm2 flexible.family.system.xExact
  let rem := p10VecNorm2 e.remainder / d
  have hkop : 0 ≤ p10StaticRightOperatorKappa choice flexible.preconditioner :=
    p10_static_kappa_nonneg choice _ _
  have hkmr : 0 ≤ p10StaticRightPreconditionerKappa choice flexible.preconditioner :=
    p10_static_kappa_nonneg choice _ _
  have hksys : 0 ≤ p10StaticSystemKappa choice flexible.family :=
    p10_static_kappa_nonneg choice _ _
  have hmag :
      (flexible.iteration k).core.gmresMagnitude *
          p10StaticRightOperatorKappa choice flexible.preconditioner *
            p10StaticRightPreconditionerKappa choice flexible.preconditioner +
        (flexible.iteration k).core.matrixMagnitude *
          p10StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR ≤
      (flexible.family.iteration k).dimensionFactor *
        p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
          (flexible.iteration k).core.ug (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR := by
    simpa only [p10StaticFlexibleAttainableEnvelope] using
      p10_flexible_magnitude_bound
        (flexible.family.iteration k).dimensionFactor
        (flexible.iteration k).core.ug (flexible.iteration k).core.ua
        (flexible.iteration k).core.rhoAR
        (p10StaticRightOperatorKappa choice flexible.preconditioner)
        (p10StaticRightPreconditionerKappa choice flexible.preconditioner)
        (p10StaticSystemKappa choice flexible.family)
        (flexible.iteration k).core.gmresMagnitude
        (flexible.iteration k).core.matrixMagnitude
        hkop hkmr hksys hcond.core.parameters_nonneg.2.2.2.2
        hcond.core.gmres_magnitude_bound
        hcond.core.matrix_magnitude_bound
  refine ⟨rem, e.remainder_second_order, ?_⟩
  change p10VecNorm2
      ((flexible.family.iteration k).xHat - flexible.family.system.xExact) / d ≤
    (flexible.family.iteration k).dimensionFactor *
      p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
        (flexible.iteration k).core.ug (flexible.iteration k).core.ua
        (flexible.iteration k).core.rhoAR + |rem|
  rw [e.error_decomposition]
  calc
    _ ≤ p10VecNorm2 e.gmresContribution / d +
          p10VecNorm2 e.matrixContribution / d + rem :=
      p10VecNorm2_three_div_le _ _ _ d (p10VecNorm2_nonneg _)
    _ ≤ (flexible.iteration k).core.gmresMagnitude *
            p10StaticRightOperatorKappa choice flexible.preconditioner *
              p10StaticRightPreconditionerKappa choice flexible.preconditioner +
          (flexible.iteration k).core.matrixMagnitude *
            p10StaticSystemKappa choice flexible.family *
              (flexible.iteration k).core.rhoAR + rem := by
      dsimp [rem, d]
      linarith [e.gmres_gain_bound, e.matrix_gain_bound]
    _ ≤ _ := by linarith [le_abs_self rem]

theorem p10_c1_right_flexible_attainable_forward_error
    {n : ℕ} (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice) :
    (∀ (right : P10StaticRightFamily n semantics)
        (mgs : P10MGSSelectionLaw right.family)
        (appendix : P10StaticRightAppendixCTheory choice right)
        (applicability : ∀ k : P10Theorem31Dimension n,
          p10IterationWellConditioned (right.family.iteration k) →
          (k.1 = n ∨ p10MGSNearDependence (right.family.iteration k)) →
          P10StaticRightConditions choice (right.iteration k)),
      ∃ k : P10Theorem31Dimension n,
        p10IterationWellConditioned (right.family.iteration k) ∧
          p10FirstOrderLe semantics
            (p10ForwardError right.family.system.xExact
              (right.family.iteration k).xHat)
            ((right.family.iteration k).dimensionFactor *
              p10StaticRightAttainableEnvelope choice right.preconditioner
                (right.iteration k).core.ug
                (right.iteration k).core.um
                (right.iteration k).core.ua
                (right.iteration k).core.etaR
                (right.iteration k).core.rhoAR)) ∧
      (∀ (flexible : P10StaticFlexibleFamily n semantics)
          (mgs : P10MGSSelectionLaw flexible.family)
          (appendix : P10StaticFlexibleAppendixDTheory choice flexible)
          (applicability : ∀ k : P10Theorem31Dimension n,
            p10IterationWellConditioned (flexible.family.iteration k) →
            (k.1 = n ∨
              p10MGSNearDependence (flexible.family.iteration k)) →
            P10StaticFlexibleConditions choice (flexible.iteration k)),
        ∃ k : P10Theorem31Dimension n,
          p10IterationWellConditioned (flexible.family.iteration k) ∧
            p10FirstOrderLe semantics
              (p10ForwardError flexible.family.system.xExact
                (flexible.family.iteration k).xHat)
              ((flexible.family.iteration k).dimensionFactor *
                p10StaticFlexibleAttainableEnvelope choice
                  flexible.preconditioner
                  (flexible.iteration k).core.ug
                  (flexible.iteration k).core.ua
                  (flexible.iteration k).core.rhoAR)) ∧
        ∀ (family : P10Theorem31Family n semantics)
          (preconditioner : P10StaticFixedRightPreconditioner family)
          (ug um ua etaR rhoAR : ℝ),
          p10StaticRightAttainableEnvelope choice preconditioner
              ug um ua etaR rhoAR =
            p10StaticFlexibleAttainableEnvelope choice preconditioner
                ug ua rhoAR +
              um * etaR *
                p10StaticRightPreconditionerKappa choice preconditioner := by
  -- PROOF_START P10-C1-H001
  refine ⟨?_, ?_, ?_⟩
  · intro right mgs appendix applicability
    obtain ⟨k, hgood, hstop⟩ := p10_select_iteration right.family mgs
    exact ⟨k, hgood,
      p10_right_bound_at semantics choice right appendix k hgood hstop
        (applicability k hgood hstop)⟩
  · intro flexible mgs appendix applicability
    obtain ⟨k, hgood, hstop⟩ := p10_select_iteration flexible.family mgs
    exact ⟨k, hgood,
      p10_flexible_bound_at semantics choice flexible appendix k hgood hstop
        (applicability k hgood hstop)⟩
  · intro family preconditioner ug um ua etaR rhoAR
    unfold p10StaticRightAttainableEnvelope
      p10StaticFlexibleAttainableEnvelope
    ring

end VSCLReuse

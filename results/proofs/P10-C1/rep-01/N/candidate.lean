import VSCLReuse.P10.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius


private theorem p10VecNorm2_eq_euclidean_norm {n : ℕ} (x : P10Vector n) :
    p10VecNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [p10VecNorm2, p10VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private theorem p10VecNorm2_nonneg {n : ℕ} (x : P10Vector n) :
    0 ≤ p10VecNorm2 x := by
  rw [p10VecNorm2_eq_euclidean_norm]
  positivity

private theorem p10VecNorm2_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  simp only [p10VecNorm2_eq_euclidean_norm]
  exact norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))
    (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))

private theorem p10ForwardError_four_le {n : ℕ}
    (x xHat a b c r : P10Vector n)
    (h : xHat - x = a + b + c + r) :
    p10ForwardError x xHat ≤
      p10VecNorm2 a / p10VecNorm2 x +
      p10VecNorm2 b / p10VecNorm2 x +
      p10VecNorm2 c / p10VecNorm2 x +
      p10VecNorm2 r / p10VecNorm2 x := by
  unfold p10ForwardError
  rw [h]
  have hnorm : p10VecNorm2 (a + b + c + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c + p10VecNorm2 r := by
    calc
      _ ≤ p10VecNorm2 (a + b + c) + p10VecNorm2 r := p10VecNorm2_add_le _ _
      _ ≤ p10VecNorm2 (a + b) + p10VecNorm2 c + p10VecNorm2 r := by
        linarith [p10VecNorm2_add_le (a + b) c]
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c +
          p10VecNorm2 r := by linarith [p10VecNorm2_add_le a b]
  calc
    _ ≤ (p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c +
      p10VecNorm2 r) / p10VecNorm2 x :=
        div_le_div_of_nonneg_right hnorm (p10VecNorm2_nonneg x)
    _ = _ := by ring

private theorem p10ForwardError_three_le {n : ℕ}
    (x xHat a b r : P10Vector n)
    (h : xHat - x = a + b + r) :
    p10ForwardError x xHat ≤
      p10VecNorm2 a / p10VecNorm2 x +
      p10VecNorm2 b / p10VecNorm2 x +
      p10VecNorm2 r / p10VecNorm2 x := by
  unfold p10ForwardError
  rw [h]
  have hnorm : p10VecNorm2 (a + b + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r := by
    calc
      _ ≤ p10VecNorm2 (a + b) + p10VecNorm2 r := p10VecNorm2_add_le _ _
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r := by
        linarith [p10VecNorm2_add_le a b]
  calc
    _ ≤ (p10VecNorm2 a + p10VecNorm2 b +
      p10VecNorm2 r) / p10VecNorm2 x :=
        div_le_div_of_nonneg_right hnorm (p10VecNorm2_nonneg x)
    _ = _ := by ring

private theorem p10StaticKappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
      exact mul_nonneg (by unfold p10FrobNorm; exact norm_nonneg _)
        (by unfold p10FrobNorm; exact norm_nonneg _)
  | inducedTwo =>
      change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
      have hA : 0 ≤ p10OpNorm2 A := by
        unfold p10OpNorm2
        rw [Matrix.l2_opNorm_def]
        exact norm_nonneg _
      have hAinv : 0 ≤ p10OpNorm2 Ainv := by
        unfold p10OpNorm2
        rw [Matrix.l2_opNorm_def]
        exact norm_nonneg _
      exact mul_nonneg hA hAinv

private theorem p10MGS_attainable_dimension {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  let P : ℕ → Prop := fun m =>
    ∀ (hmpos : 0 < m) (hmle : m ≤ n),
      (∃ k : P10Theorem31Dimension n,
        k.1 ≤ m ∧ p10IterationWellConditioned (family.iteration k) ∧
          p10MGSNearDependence (family.iteration k)) ∨
      p10IterationWellConditioned (family.iteration ⟨m, hmpos, hmle⟩)
  have hP : ∀ m, 1 ≤ m → P m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        intro hmpos hmle
        right
        exact mgs.first_dimension_good
    | succ m hm ih =>
        intro hpos hle
        have hmpos : 0 < m := by omega
        have hmle : m ≤ n := by omega
        rcases ih hmpos hmle with hnear | hgood
        · left
          obtain ⟨k, hk, hkgood, hknear⟩ := hnear
          exact ⟨k, by omega, hkgood, hknear⟩
        · by_cases hnext :
            p10IterationWellConditioned
              (family.iteration ⟨m + 1, hpos, hle⟩)
          · exact Or.inr hnext
          · left
            have hmlt : m < n := by omega
            have hnear := mgs.loss_implies_near_dependence m hmpos hmlt hnext
            exact ⟨⟨m, hmpos, hmle⟩, Nat.le_succ m, hgood, hnear⟩
  have hn : 1 ≤ n := family.system.dimension_pos
  have hfinal := hP n hn family.system.dimension_pos (le_refl n)
  rcases hfinal with hnear | hgood
  · obtain ⟨k, hk, hkgood, hknear⟩ := hnear
    exact ⟨k, hkgood, Or.inr hknear⟩
  · exact ⟨⟨n, family.system.dimension_pos, le_refl n⟩,
      hgood, Or.inl rfl⟩

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
  constructor
  · intro right mgs appendix applicability
    obtain ⟨k, hgood, hterminal⟩ :=
      p10MGS_attainable_dimension right.family mgs
    have hconditions := applicability k hgood hterminal
    let expansion := appendix.expansion k hgood hterminal hconditions
    refine ⟨k, hgood, ?_⟩
    let d := (right.family.iteration k).dimensionFactor
    let op := p10StaticRightOperatorKappa choice right.preconditioner
    let mr := p10StaticRightPreconditionerKappa choice right.preconditioner
    let sys := p10StaticSystemKappa choice right.family
    let rem := p10VecNorm2 expansion.remainder /
      p10VecNorm2 right.family.system.xExact
    refine ⟨rem, expansion.remainder_second_order, ?_⟩
    have hop : 0 ≤ op := p10StaticKappa_nonneg choice _ _
    have hmr : 0 ≤ mr := p10StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ sys := p10StaticKappa_nonneg choice _ _
    rcases hconditions.core.parameters_nonneg with ⟨hug, hum, hua, heta, hrho⟩
    have hgm :
        p10VecNorm2 expansion.gmresContribution /
          p10VecNorm2 right.family.system.xExact ≤
        (d * (right.iteration k).core.ug) * op * mr := by
      calc
        _ ≤ (right.iteration k).core.gmresMagnitude * op * mr :=
          expansion.gmres_gain_bound
        _ ≤ (d * (right.iteration k).core.ug) * op * mr :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              hconditions.core.gmres_magnitude_bound hop) hmr
    have hreapp :
        p10VecNorm2 expansion.reapplicationContribution /
          p10VecNorm2 right.family.system.xExact ≤
        (d * (right.iteration k).core.um *
          (right.iteration k).core.etaR) * mr := by
      calc
        _ ≤ (right.iteration k).reapplicationMagnitude * mr :=
          expansion.reapplication_gain_bound
        _ ≤ (d * (right.iteration k).core.um *
            (right.iteration k).core.etaR) * mr :=
          mul_le_mul_of_nonneg_right
            hconditions.reapplication_magnitude_bound hmr
    have hmatrix :
        p10VecNorm2 expansion.matrixContribution /
          p10VecNorm2 right.family.system.xExact ≤
        (d * (right.iteration k).core.ua) * sys *
          (right.iteration k).core.rhoAR := by
      calc
        _ ≤ (right.iteration k).core.matrixMagnitude * sys *
            (right.iteration k).core.rhoAR := expansion.matrix_gain_bound
        _ ≤ (d * (right.iteration k).core.ua) * sys *
            (right.iteration k).core.rhoAR :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              hconditions.core.matrix_magnitude_bound hsys) hrho
    have htriangle := p10ForwardError_four_le
      right.family.system.xExact (right.family.iteration k).xHat
      expansion.gmresContribution expansion.reapplicationContribution
      expansion.matrixContribution expansion.remainder
      expansion.error_decomposition
    have hrem : 0 ≤ rem :=
      div_nonneg (p10VecNorm2_nonneg _) (p10VecNorm2_nonneg _)
    calc
      p10ForwardError right.family.system.xExact
          (right.family.iteration k).xHat ≤
        p10VecNorm2 expansion.gmresContribution /
            p10VecNorm2 right.family.system.xExact +
          p10VecNorm2 expansion.reapplicationContribution /
            p10VecNorm2 right.family.system.xExact +
          p10VecNorm2 expansion.matrixContribution /
            p10VecNorm2 right.family.system.xExact + rem := htriangle
      _ ≤ (d * (right.iteration k).core.ug) * op * mr +
          (d * (right.iteration k).core.um *
            (right.iteration k).core.etaR) * mr +
          (d * (right.iteration k).core.ua) * sys *
            (right.iteration k).core.rhoAR + rem := by
          linarith
      _ = d * p10StaticRightAttainableEnvelope choice
          right.preconditioner (right.iteration k).core.ug
          (right.iteration k).core.um (right.iteration k).core.ua
          (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR + |rem| := by
          rw [abs_of_nonneg hrem]
          simp only [p10StaticRightAttainableEnvelope]
          ring
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hgood, hterminal⟩ :=
        p10MGS_attainable_dimension flexible.family mgs
      have hconditions := applicability k hgood hterminal
      let expansion := appendix.expansion k hgood hterminal hconditions
      refine ⟨k, hgood, ?_⟩
      let d := (flexible.family.iteration k).dimensionFactor
      let op := p10StaticRightOperatorKappa choice flexible.preconditioner
      let mr := p10StaticRightPreconditionerKappa choice flexible.preconditioner
      let sys := p10StaticSystemKappa choice flexible.family
      let rem := p10VecNorm2 expansion.remainder /
        p10VecNorm2 flexible.family.system.xExact
      refine ⟨rem, expansion.remainder_second_order, ?_⟩
      have hop : 0 ≤ op := p10StaticKappa_nonneg choice _ _
      have hmr : 0 ≤ mr := p10StaticKappa_nonneg choice _ _
      have hsys : 0 ≤ sys := p10StaticKappa_nonneg choice _ _
      rcases hconditions.core.parameters_nonneg with ⟨hug, hum, hua, heta, hrho⟩
      have hgm :
          p10VecNorm2 expansion.gmresContribution /
            p10VecNorm2 flexible.family.system.xExact ≤
          (d * (flexible.iteration k).core.ug) * op * mr := by
        calc
          _ ≤ (flexible.iteration k).core.gmresMagnitude * op * mr :=
            expansion.gmres_gain_bound
          _ ≤ (d * (flexible.iteration k).core.ug) * op * mr :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                hconditions.core.gmres_magnitude_bound hop) hmr
      have hmatrix :
          p10VecNorm2 expansion.matrixContribution /
            p10VecNorm2 flexible.family.system.xExact ≤
          (d * (flexible.iteration k).core.ua) * sys *
            (flexible.iteration k).core.rhoAR := by
        calc
          _ ≤ (flexible.iteration k).core.matrixMagnitude * sys *
              (flexible.iteration k).core.rhoAR := expansion.matrix_gain_bound
          _ ≤ (d * (flexible.iteration k).core.ua) * sys *
              (flexible.iteration k).core.rhoAR :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                hconditions.core.matrix_magnitude_bound hsys) hrho
      have htriangle := p10ForwardError_three_le
        flexible.family.system.xExact (flexible.family.iteration k).xHat
        expansion.gmresContribution expansion.matrixContribution
        expansion.remainder expansion.error_decomposition
      have hrem : 0 ≤ rem :=
        div_nonneg (p10VecNorm2_nonneg _) (p10VecNorm2_nonneg _)
      calc
        p10ForwardError flexible.family.system.xExact
            (flexible.family.iteration k).xHat ≤
          p10VecNorm2 expansion.gmresContribution /
              p10VecNorm2 flexible.family.system.xExact +
            p10VecNorm2 expansion.matrixContribution /
              p10VecNorm2 flexible.family.system.xExact + rem := htriangle
        _ ≤ (d * (flexible.iteration k).core.ug) * op * mr +
            (d * (flexible.iteration k).core.ua) * sys *
              (flexible.iteration k).core.rhoAR + rem := by
            linarith
        _ = d * p10StaticFlexibleAttainableEnvelope choice
            flexible.preconditioner (flexible.iteration k).core.ug
            (flexible.iteration k).core.ua
            (flexible.iteration k).core.rhoAR + |rem| := by
            rw [abs_of_nonneg hrem]
            simp only [p10StaticFlexibleAttainableEnvelope]
            ring
    · intro family preconditioner ug um ua etaR rhoAR
      simp only [p10StaticRightAttainableEnvelope,
        p10StaticFlexibleAttainableEnvelope]
      ring

end VSCLReuse

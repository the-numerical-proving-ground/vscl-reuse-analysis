import VSCLReuse.P10.Definitions
import NumStability.Analysis.MatrixAlgebra

namespace VSCLReuse

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private theorem p10_vecNorm2_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  simpa only [p10VecNorm2, p10VecNorm2Sq, NumStability.vecNorm2,
    NumStability.vecNorm2Sq, Pi.add_apply] using NumStability.vecNorm2_add_le x y

private theorem p10_vecNorm2_nonneg {n : ℕ} (x : P10Vector n) :
    0 ≤ p10VecNorm2 x := by
  exact Real.sqrt_nonneg _

private theorem p10_mgs_selected {n : ℕ} {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  classical
  have go : ∀ fuel : ℕ, ∀ k : P10Theorem31Dimension n,
      n - k.1 ≤ fuel →
      p10IterationWellConditioned (family.iteration k) →
      ∃ j : P10Theorem31Dimension n,
        p10IterationWellConditioned (family.iteration j) ∧
          (j.1 = n ∨ p10MGSNearDependence (family.iteration j)) := by
    intro fuel
    induction fuel with
    | zero =>
        intro k hdist hgood
        refine ⟨k, hgood, Or.inl ?_⟩
        omega
    | succ fuel ih =>
        intro k hdist hgood
        by_cases hlast : k.1 = n
        · exact ⟨k, hgood, Or.inl hlast⟩
        · have hlt : k.1 < n := by omega
          let next : P10Theorem31Dimension n :=
            ⟨k.1 + 1, by omega, by omega⟩
          by_cases hnext : p10IterationWellConditioned (family.iteration next)
          · apply ih next
            · dsimp [next]
              omega
            · exact hnext
          · have hnear : p10MGSNearDependence (family.iteration k) := by
              simpa only [next] using
                (mgs.loss_implies_near_dependence k.1 k.2.1 hlt hnext)
            exact ⟨k, hgood, Or.inr hnear⟩
  let first : P10Theorem31Dimension n :=
    ⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩
  apply go (n - 1) first
  · rfl
  · exact mgs.first_dimension_good

private theorem p10_static_kappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
      have h₁ : 0 ≤ p10FrobNorm Ainv := by
        unfold p10FrobNorm
        exact norm_nonneg _
      have h₂ : 0 ≤ p10FrobNorm A := by
        unfold p10FrobNorm
        exact norm_nonneg _
      exact mul_nonneg h₁ h₂
  | inducedTwo =>
      change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
      have h₁ : 0 ≤ p10OpNorm2 A := by
        unfold p10OpNorm2
        exact @norm_nonneg _
          Matrix.instL2OpNormedAddCommGroup.toNormedAddGroup.toSeminormedAddGroup A
      have h₂ : 0 ≤ p10OpNorm2 Ainv := by
        unfold p10OpNorm2
        exact @norm_nonneg _
          Matrix.instL2OpNormedAddCommGroup.toNormedAddGroup.toSeminormedAddGroup Ainv
      exact mul_nonneg h₁ h₂

private theorem p10_right_expansion_bound {n : ℕ}
    (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice)
    (right : P10StaticRightFamily n semantics)
    (k : P10Theorem31Dimension n)
    (conditions : P10StaticRightConditions choice (right.iteration k))
    (exp : P10StaticRightAppendixCExpansion choice right k) :
    p10FirstOrderLe semantics
      (p10ForwardError right.family.system.xExact
        (right.family.iteration k).xHat)
      ((right.family.iteration k).dimensionFactor *
        p10StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug (right.iteration k).core.um
          (right.iteration k).core.ua (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR) := by
  let D := (right.family.iteration k).dimensionFactor
  let d := p10VecNorm2 right.family.system.xExact
  let G := p10StaticRightOperatorKappa choice right.preconditioner
  let M := p10StaticRightPreconditionerKappa choice right.preconditioner
  let A := p10StaticSystemKappa choice right.family
  have hG : 0 ≤ G := p10_static_kappa_nonneg choice _ _
  have hM : 0 ≤ M := p10_static_kappa_nonneg choice _ _
  have hA : 0 ≤ A := p10_static_kappa_nonneg choice _ _
  have hgm : p10VecNorm2 exp.gmresContribution / d ≤
      D * ((right.iteration k).core.ug * G * M) := by
    calc
      _ ≤ (right.iteration k).core.gmresMagnitude * G * M :=
        exp.gmres_gain_bound
      _ ≤ (D * (right.iteration k).core.ug) * G * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound hG) hM
      _ = _ := by ring
  have hrep : p10VecNorm2 exp.reapplicationContribution / d ≤
      D * ((right.iteration k).core.um *
        (right.iteration k).core.etaR * M) := by
    calc
      _ ≤ (right.iteration k).reapplicationMagnitude * M :=
        exp.reapplication_gain_bound
      _ ≤ (D * (right.iteration k).core.um *
          (right.iteration k).core.etaR) * M :=
        mul_le_mul_of_nonneg_right conditions.reapplication_magnitude_bound hM
      _ = _ := by ring
  have hmat : p10VecNorm2 exp.matrixContribution / d ≤
      D * ((right.iteration k).core.ua * A *
        (right.iteration k).core.rhoAR) := by
    have hrho : 0 ≤ (right.iteration k).core.rhoAR :=
      conditions.core.parameters_nonneg.2.2.2.2
    calc
      _ ≤ (right.iteration k).core.matrixMagnitude * A *
          (right.iteration k).core.rhoAR := exp.matrix_gain_bound
      _ ≤ (D * (right.iteration k).core.ua) * A *
          (right.iteration k).core.rhoAR := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound hA) hrho
      _ = _ := by ring
  have htriangle : p10ForwardError right.family.system.xExact
      (right.family.iteration k).xHat ≤
      p10VecNorm2 exp.gmresContribution / d +
      p10VecNorm2 exp.reapplicationContribution / d +
      p10VecNorm2 exp.matrixContribution / d +
      p10VecNorm2 exp.remainder / d := by
    have hsum : p10VecNorm2
        (exp.gmresContribution + exp.reapplicationContribution +
          exp.matrixContribution + exp.remainder) ≤
        p10VecNorm2 exp.gmresContribution +
          p10VecNorm2 exp.reapplicationContribution +
          p10VecNorm2 exp.matrixContribution +
          p10VecNorm2 exp.remainder := by
      calc
        _ ≤ p10VecNorm2
              (exp.gmresContribution + exp.reapplicationContribution +
                exp.matrixContribution) + p10VecNorm2 exp.remainder :=
            p10_vecNorm2_add_le _ _
        _ ≤ (p10VecNorm2
              (exp.gmresContribution + exp.reapplicationContribution) +
              p10VecNorm2 exp.matrixContribution) +
              p10VecNorm2 exp.remainder := by
            gcongr
            exact p10_vecNorm2_add_le _ _
        _ ≤ (p10VecNorm2 exp.gmresContribution +
              p10VecNorm2 exp.reapplicationContribution +
              p10VecNorm2 exp.matrixContribution) +
              p10VecNorm2 exp.remainder := by
            gcongr
            exact p10_vecNorm2_add_le _ _
        _ = _ := by ring
    unfold p10ForwardError
    rw [exp.error_decomposition]
    calc
      _ ≤ (p10VecNorm2 exp.gmresContribution +
          p10VecNorm2 exp.reapplicationContribution +
          p10VecNorm2 exp.matrixContribution +
          p10VecNorm2 exp.remainder) / d :=
        div_le_div_of_nonneg_right hsum (p10_vecNorm2_nonneg _)
      _ = _ := by ring
  refine ⟨p10VecNorm2 exp.remainder / d, exp.remainder_second_order, ?_⟩
  calc
    _ ≤ p10VecNorm2 exp.gmresContribution / d +
        p10VecNorm2 exp.reapplicationContribution / d +
        p10VecNorm2 exp.matrixContribution / d +
        p10VecNorm2 exp.remainder / d := htriangle
    _ ≤ D * (p10StaticRightAttainableEnvelope choice right.preconditioner
          (right.iteration k).core.ug (right.iteration k).core.um
          (right.iteration k).core.ua (right.iteration k).core.etaR
          (right.iteration k).core.rhoAR) +
        p10VecNorm2 exp.remainder / d := by
      dsimp [p10StaticRightAttainableEnvelope]
      linarith only [hgm, hrep, hmat]
    _ ≤ _ := by
      exact add_le_add_right (le_abs_self (p10VecNorm2 exp.remainder / d)) _

private theorem p10_flexible_expansion_bound {n : ℕ}
    (semantics : P10FirstOrderSemantics)
    (choice : P10StaticSquareKappaChoice)
    (flexible : P10StaticFlexibleFamily n semantics)
    (k : P10Theorem31Dimension n)
    (conditions : P10StaticFlexibleConditions choice (flexible.iteration k))
    (exp : P10StaticFlexibleAppendixDExpansion choice flexible k) :
    p10FirstOrderLe semantics
      (p10ForwardError flexible.family.system.xExact
        (flexible.family.iteration k).xHat)
      ((flexible.family.iteration k).dimensionFactor *
        p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
          (flexible.iteration k).core.ug (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR) := by
  let D := (flexible.family.iteration k).dimensionFactor
  let d := p10VecNorm2 flexible.family.system.xExact
  let G := p10StaticRightOperatorKappa choice flexible.preconditioner
  let M := p10StaticRightPreconditionerKappa choice flexible.preconditioner
  let A := p10StaticSystemKappa choice flexible.family
  have hG : 0 ≤ G := p10_static_kappa_nonneg choice _ _
  have hM : 0 ≤ M := p10_static_kappa_nonneg choice _ _
  have hA : 0 ≤ A := p10_static_kappa_nonneg choice _ _
  have hgm : p10VecNorm2 exp.gmresContribution / d ≤
      D * ((flexible.iteration k).core.ug * G * M) := by
    calc
      _ ≤ (flexible.iteration k).core.gmresMagnitude * G * M :=
        exp.gmres_gain_bound
      _ ≤ (D * (flexible.iteration k).core.ug) * G * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound hG) hM
      _ = _ := by ring
  have hmat : p10VecNorm2 exp.matrixContribution / d ≤
      D * ((flexible.iteration k).core.ua * A *
        (flexible.iteration k).core.rhoAR) := by
    have hrho : 0 ≤ (flexible.iteration k).core.rhoAR :=
      conditions.core.parameters_nonneg.2.2.2.2
    calc
      _ ≤ (flexible.iteration k).core.matrixMagnitude * A *
          (flexible.iteration k).core.rhoAR := exp.matrix_gain_bound
      _ ≤ (D * (flexible.iteration k).core.ua) * A *
          (flexible.iteration k).core.rhoAR := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound hA) hrho
      _ = _ := by ring
  have htriangle : p10ForwardError flexible.family.system.xExact
      (flexible.family.iteration k).xHat ≤
      p10VecNorm2 exp.gmresContribution / d +
      p10VecNorm2 exp.matrixContribution / d +
      p10VecNorm2 exp.remainder / d := by
    have hsum : p10VecNorm2
        (exp.gmresContribution + exp.matrixContribution + exp.remainder) ≤
        p10VecNorm2 exp.gmresContribution +
          p10VecNorm2 exp.matrixContribution +
          p10VecNorm2 exp.remainder := by
      calc
        _ ≤ p10VecNorm2 (exp.gmresContribution + exp.matrixContribution) +
              p10VecNorm2 exp.remainder := p10_vecNorm2_add_le _ _
        _ ≤ (p10VecNorm2 exp.gmresContribution +
              p10VecNorm2 exp.matrixContribution) +
              p10VecNorm2 exp.remainder := by
            gcongr
            exact p10_vecNorm2_add_le _ _
        _ = _ := by ring
    unfold p10ForwardError
    rw [exp.error_decomposition]
    calc
      _ ≤ (p10VecNorm2 exp.gmresContribution +
          p10VecNorm2 exp.matrixContribution +
          p10VecNorm2 exp.remainder) / d :=
        div_le_div_of_nonneg_right hsum (p10_vecNorm2_nonneg _)
      _ = _ := by ring
  refine ⟨p10VecNorm2 exp.remainder / d, exp.remainder_second_order, ?_⟩
  calc
    _ ≤ p10VecNorm2 exp.gmresContribution / d +
        p10VecNorm2 exp.matrixContribution / d +
        p10VecNorm2 exp.remainder / d := htriangle
    _ ≤ D * (p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
          (flexible.iteration k).core.ug (flexible.iteration k).core.ua
          (flexible.iteration k).core.rhoAR) +
        p10VecNorm2 exp.remainder / d := by
      dsimp [p10StaticFlexibleAttainableEnvelope]
      linarith only [hgm, hmat]
    _ ≤ _ := by
      exact add_le_add_right (le_abs_self (p10VecNorm2 exp.remainder / d)) _

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
    obtain ⟨k, hgood, hstop⟩ := p10_mgs_selected right.family mgs
    let conditions := applicability k hgood hstop
    let exp := appendix.expansion k hgood hstop conditions
    exact ⟨k, hgood, p10_right_expansion_bound semantics choice right k conditions exp⟩
  constructor
  · intro flexible mgs appendix applicability
    obtain ⟨k, hgood, hstop⟩ := p10_mgs_selected flexible.family mgs
    let conditions := applicability k hgood hstop
    let exp := appendix.expansion k hgood hstop conditions
    exact ⟨k, hgood,
      p10_flexible_expansion_bound semantics choice flexible k conditions exp⟩
  · intro family preconditioner ug um ua etaR rhoAR
    unfold p10StaticRightAttainableEnvelope
      p10StaticFlexibleAttainableEnvelope
    ring

end VSCLReuse

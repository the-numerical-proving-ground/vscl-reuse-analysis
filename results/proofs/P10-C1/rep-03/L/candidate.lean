import VSCLReuse.P10.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private lemma p10VecNorm2_eq_norm {n : ℕ} (x : P10Vector n) :
    p10VecNorm2 x = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [p10VecNorm2, p10VecNorm2Sq, Real.norm_eq_abs, sq_abs]

private lemma p10VecNorm2_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  simp only [p10VecNorm2_eq_norm]
  exact norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

private lemma p10VecNorm2_nonneg {n : ℕ} (x : P10Vector n) :
    0 ≤ p10VecNorm2 x := Real.sqrt_nonneg _

private lemma p10FirstOrderLe_of_four_contributions {n : ℕ}
    (semantics : P10FirstOrderSemantics) (x xHat a b c r : P10Vector n)
    (A B C E : ℝ)
    (hdecomp : xHat - x = a + b + c + r)
    (hrem : semantics.secondOrder (p10VecNorm2 r / p10VecNorm2 x))
    (ha : p10VecNorm2 a / p10VecNorm2 x ≤ A)
    (hb : p10VecNorm2 b / p10VecNorm2 x ≤ B)
    (hc : p10VecNorm2 c / p10VecNorm2 x ≤ C)
    (hE : A + B + C ≤ E) :
    p10FirstOrderLe semantics (p10ForwardError x xHat) E := by
  refine ⟨p10VecNorm2 r / p10VecNorm2 x, hrem, ?_⟩
  have hnorm : p10VecNorm2 (a + b + c + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c + p10VecNorm2 r := by
    calc
      p10VecNorm2 (a + b + c + r) ≤
          p10VecNorm2 (a + b + c) + p10VecNorm2 r := p10VecNorm2_add_le _ _
      _ ≤ p10VecNorm2 (a + b) + p10VecNorm2 c + p10VecNorm2 r := by
          linarith [p10VecNorm2_add_le (a + b) c]
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c + p10VecNorm2 r := by
          linarith [p10VecNorm2_add_le a b]
  have hdiv := div_le_div_of_nonneg_right hnorm (p10VecNorm2_nonneg x)
  rw [p10ForwardError, hdecomp]
  rw [add_div, add_div, add_div] at hdiv
  linarith [le_abs_self (p10VecNorm2 r / p10VecNorm2 x)]

private lemma p10FirstOrderLe_of_three_contributions {n : ℕ}
    (semantics : P10FirstOrderSemantics) (x xHat a b r : P10Vector n)
    (A B E : ℝ)
    (hdecomp : xHat - x = a + b + r)
    (hrem : semantics.secondOrder (p10VecNorm2 r / p10VecNorm2 x))
    (ha : p10VecNorm2 a / p10VecNorm2 x ≤ A)
    (hb : p10VecNorm2 b / p10VecNorm2 x ≤ B)
    (hE : A + B ≤ E) :
    p10FirstOrderLe semantics (p10ForwardError x xHat) E := by
  refine ⟨p10VecNorm2 r / p10VecNorm2 x, hrem, ?_⟩
  have hnorm : p10VecNorm2 (a + b + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r := by
    calc
      p10VecNorm2 (a + b + r) ≤ p10VecNorm2 (a + b) + p10VecNorm2 r :=
        p10VecNorm2_add_le _ _
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 r := by
          linarith [p10VecNorm2_add_le a b]
  have hdiv := div_le_div_of_nonneg_right hnorm (p10VecNorm2_nonneg x)
  rw [p10ForwardError, hdecomp]
  rw [add_div, add_div] at hdiv
  linarith [le_abs_self (p10VecNorm2 r / p10VecNorm2 x)]

private lemma p10_exists_well_conditioned_terminal {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  classical
  let P : ℕ → Prop := fun j =>
    ∃ hj : 0 < j ∧ j ≤ n,
      p10IterationWellConditioned (family.iteration ⟨j, hj⟩)
  let m := Nat.findGreatest P n
  have hP1 : P 1 :=
    ⟨⟨Nat.zero_lt_one, family.system.dimension_pos⟩, mgs.first_dimension_good⟩
  have hmpos : 0 < m :=
    lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_findGreatest family.system.dimension_pos hP1)
  have hmle : m ≤ n := Nat.findGreatest_le n
  have hPm : P m := Nat.findGreatest_spec family.system.dimension_pos hP1
  let k : P10Theorem31Dimension n := ⟨m, hmpos, hmle⟩
  have hgood : p10IterationWellConditioned (family.iteration k) := by
    obtain ⟨_, h⟩ := hPm
    exact h
  refine ⟨k, hgood, ?_⟩
  by_cases heq : m = n
  · exact Or.inl heq
  · have hlt : m < n := lt_of_le_of_ne hmle heq
    have hnextBad : ¬ P (m + 1) :=
      Nat.findGreatest_is_greatest (Nat.lt_succ_self m)
        (Nat.succ_le_iff.mpr hlt)
    have hnotnext :
        ¬ p10IterationWellConditioned
            (family.iteration
              ⟨m + 1, Nat.succ_pos m, Nat.succ_le_iff.mpr hlt⟩) := by
      intro h
      exact hnextBad ⟨⟨Nat.succ_pos m, Nat.succ_le_iff.mpr hlt⟩, h⟩
    exact Or.inr (mgs.loss_implies_near_dependence m hmpos hlt hnotnext)

private lemma p10StaticKappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  | inducedTwo =>
      change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
      have hA : 0 ≤ p10OpNorm2 A := by
        change 0 ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℝ)
          (m := Fin n) (n := Fin n)).trans LinearMap.toContinuousLinearMap A‖
        exact norm_nonneg _
      have hAinv : 0 ≤ p10OpNorm2 Ainv := by
        change 0 ≤ ‖(Matrix.toEuclideanLin (𝕜 := ℝ)
          (m := Fin n) (n := Fin n)).trans LinearMap.toContinuousLinearMap Ainv‖
        exact norm_nonneg _
      exact mul_nonneg hA hAinv

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
    obtain ⟨k, hwell, hterminal⟩ :=
      p10_exists_well_conditioned_terminal right.family mgs
    let conditions := applicability k hwell hterminal
    let expansion := appendix.expansion k hwell hterminal conditions
    let D := (right.family.iteration k).dimensionFactor
    let KO := p10StaticRightOperatorKappa choice right.preconditioner
    let KR := p10StaticRightPreconditionerKappa choice right.preconditioner
    let KA := p10StaticSystemKappa choice right.family
    have hKO : 0 ≤ KO := by
      change 0 ≤ p10StaticKappa choice
        (p10SquareRectMul right.family.system.A right.preconditioner.MRinv)
        (p10SquareRectMul right.preconditioner.MR right.family.system.Ainv)
      exact p10StaticKappa_nonneg choice _ _
    have hKR : 0 ≤ KR := p10StaticKappa_nonneg choice _ _
    have hKA : 0 ≤ KA := p10StaticKappa_nonneg choice _ _
    have hrho : 0 ≤ (right.iteration k).core.rhoAR :=
      conditions.core.parameters_nonneg.2.2.2.2
    have hgm :
        (right.iteration k).core.gmresMagnitude * KO * KR ≤
          (D * (right.iteration k).core.ug) * KO * KR :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          conditions.core.gmres_magnitude_bound hKO) hKR
    have hre :
        (right.iteration k).reapplicationMagnitude * KR ≤
          (D * (right.iteration k).core.um *
            (right.iteration k).core.etaR) * KR :=
      mul_le_mul_of_nonneg_right
        conditions.reapplication_magnitude_bound hKR
    have hmat :
        (right.iteration k).core.matrixMagnitude * KA *
            (right.iteration k).core.rhoAR ≤
          (D * (right.iteration k).core.ua) * KA *
            (right.iteration k).core.rhoAR :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          conditions.core.matrix_magnitude_bound hKA) hrho
    refine ⟨k, hwell, ?_⟩
    apply p10FirstOrderLe_of_four_contributions semantics
      right.family.system.xExact (right.family.iteration k).xHat
      expansion.gmresContribution expansion.reapplicationContribution
      expansion.matrixContribution expansion.remainder
      (expansion.gmresContribution |> fun v =>
        p10VecNorm2 v / p10VecNorm2 right.family.system.xExact)
      (expansion.reapplicationContribution |> fun v =>
        p10VecNorm2 v / p10VecNorm2 right.family.system.xExact)
      (expansion.matrixContribution |> fun v =>
        p10VecNorm2 v / p10VecNorm2 right.family.system.xExact)
    · exact expansion.error_decomposition
    · exact expansion.remainder_second_order
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · calc
        _ ≤ (right.iteration k).core.gmresMagnitude * KO * KR +
            (right.iteration k).reapplicationMagnitude * KR +
            (right.iteration k).core.matrixMagnitude * KA *
              (right.iteration k).core.rhoAR := by
          exact add_le_add
            (add_le_add expansion.gmres_gain_bound
              expansion.reapplication_gain_bound)
            expansion.matrix_gain_bound
        _ ≤ (D * (right.iteration k).core.ug) * KO * KR +
            (D * (right.iteration k).core.um *
              (right.iteration k).core.etaR) * KR +
            (D * (right.iteration k).core.ua) * KA *
              (right.iteration k).core.rhoAR := by
          exact add_le_add (add_le_add hgm hre) hmat
        _ = D * p10StaticRightAttainableEnvelope choice right.preconditioner
              (right.iteration k).core.ug
              (right.iteration k).core.um
              (right.iteration k).core.ua
              (right.iteration k).core.etaR
              (right.iteration k).core.rhoAR := by
          dsimp [p10StaticRightAttainableEnvelope, D, KO, KR, KA]
          ring
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hwell, hterminal⟩ :=
        p10_exists_well_conditioned_terminal flexible.family mgs
      let conditions := applicability k hwell hterminal
      let expansion := appendix.expansion k hwell hterminal conditions
      let D := (flexible.family.iteration k).dimensionFactor
      let KO := p10StaticRightOperatorKappa choice flexible.preconditioner
      let KR := p10StaticRightPreconditionerKappa choice flexible.preconditioner
      let KA := p10StaticSystemKappa choice flexible.family
      have hKO : 0 ≤ KO := by
        change 0 ≤ p10StaticKappa choice
          (p10SquareRectMul flexible.family.system.A flexible.preconditioner.MRinv)
          (p10SquareRectMul flexible.preconditioner.MR flexible.family.system.Ainv)
        exact p10StaticKappa_nonneg choice _ _
      have hKR : 0 ≤ KR := p10StaticKappa_nonneg choice _ _
      have hKA : 0 ≤ KA := p10StaticKappa_nonneg choice _ _
      have hrho : 0 ≤ (flexible.iteration k).core.rhoAR :=
        conditions.core.parameters_nonneg.2.2.2.2
      have hgm :
          (flexible.iteration k).core.gmresMagnitude * KO * KR ≤
            (D * (flexible.iteration k).core.ug) * KO * KR :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.gmres_magnitude_bound hKO) hKR
      have hmat :
          (flexible.iteration k).core.matrixMagnitude * KA *
              (flexible.iteration k).core.rhoAR ≤
            (D * (flexible.iteration k).core.ua) * KA *
              (flexible.iteration k).core.rhoAR :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            conditions.core.matrix_magnitude_bound hKA) hrho
      refine ⟨k, hwell, ?_⟩
      apply p10FirstOrderLe_of_three_contributions semantics
        flexible.family.system.xExact (flexible.family.iteration k).xHat
        expansion.gmresContribution expansion.matrixContribution expansion.remainder
        (expansion.gmresContribution |> fun v =>
          p10VecNorm2 v / p10VecNorm2 flexible.family.system.xExact)
        (expansion.matrixContribution |> fun v =>
          p10VecNorm2 v / p10VecNorm2 flexible.family.system.xExact)
      · exact expansion.error_decomposition
      · exact expansion.remainder_second_order
      · exact le_rfl
      · exact le_rfl
      · calc
          _ ≤ (flexible.iteration k).core.gmresMagnitude * KO * KR +
              (flexible.iteration k).core.matrixMagnitude * KA *
                (flexible.iteration k).core.rhoAR := by
            exact add_le_add expansion.gmres_gain_bound expansion.matrix_gain_bound
          _ ≤ (D * (flexible.iteration k).core.ug) * KO * KR +
              (D * (flexible.iteration k).core.ua) * KA *
                (flexible.iteration k).core.rhoAR := by
            exact add_le_add hgm hmat
          _ = D * p10StaticFlexibleAttainableEnvelope choice flexible.preconditioner
                (flexible.iteration k).core.ug
                (flexible.iteration k).core.ua
                (flexible.iteration k).core.rhoAR := by
            dsimp [p10StaticFlexibleAttainableEnvelope, D, KO, KR, KA]
            ring
    · intro family preconditioner ug um ua etaR rhoAR
      unfold p10StaticRightAttainableEnvelope
        p10StaticFlexibleAttainableEnvelope
      ring

end VSCLReuse

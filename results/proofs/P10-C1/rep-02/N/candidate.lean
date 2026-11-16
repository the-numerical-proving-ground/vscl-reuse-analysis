import VSCLReuse.P10.Definitions

namespace VSCLReuse

private theorem p10VecNorm2_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  let ex : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let ey : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hx : ‖ex‖ = p10VecNorm2 x := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hy : ‖ey‖ = p10VecNorm2 y := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hxy : ‖ex + ey‖ = p10VecNorm2 (x + y) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  rw [← hx, ← hy, ← hxy]
  exact norm_add_le ex ey

private theorem p10_select_iteration {n : ℕ}
    {semantics : P10FirstOrderSemantics}
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  classical
  have step : ∀ d k : ℕ, ∀ (hkpos : 0 < k) (hkle : k ≤ n),
      n - k = d →
      p10IterationWellConditioned (family.iteration ⟨k, hkpos, hkle⟩) →
      ∃ j : P10Theorem31Dimension n,
        p10IterationWellConditioned (family.iteration j) ∧
          (j.1 = n ∨ p10MGSNearDependence (family.iteration j)) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro k hkpos hkle hd hgood
      by_cases hkn : k = n
      · exact ⟨⟨k, hkpos, hkle⟩, hgood, Or.inl hkn⟩
      · have hklt : k < n := Nat.lt_of_le_of_ne hkle hkn
        let current : P10Theorem31Dimension n := ⟨k, hkpos, hkle⟩
        let next : P10Theorem31Dimension n :=
          ⟨k + 1, Nat.succ_pos k, Nat.succ_le_iff.mpr hklt⟩
        by_cases hnext : p10IterationWellConditioned (family.iteration next)
        · exact ih (n - (k + 1)) (by omega) (k + 1)
            (Nat.succ_pos k) (Nat.succ_le_iff.mpr hklt) rfl hnext
        · have hnear : p10MGSNearDependence (family.iteration current) :=
            mgs.loss_implies_near_dependence k hkpos hklt hnext
          exact ⟨current, hgood, Or.inr hnear⟩
  apply step (n - 1) 1 Nat.zero_lt_one family.system.dimension_pos rfl
  exact mgs.first_dimension_good

private theorem p10_norm_sum3_div_le {n : ℕ}
    (x xHat a b c : P10Vector n)
    (h : xHat - x = a + b + c) :
    p10ForwardError x xHat ≤
      p10VecNorm2 a / p10VecNorm2 x +
        p10VecNorm2 b / p10VecNorm2 x +
          p10VecNorm2 c / p10VecNorm2 x := by
  have ht : p10VecNorm2 (a + b + c) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c := by
    calc
      p10VecNorm2 (a + b + c) ≤
          p10VecNorm2 (a + b) + p10VecNorm2 c :=
        p10VecNorm2_add_le (a + b) c
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c := by
        linarith [p10VecNorm2_add_le a b]
  unfold p10ForwardError
  rw [h]
  have hnonneg : 0 ≤ p10VecNorm2 x := by unfold p10VecNorm2; positivity
  have hdiv := div_le_div_of_nonneg_right ht hnonneg
  convert hdiv using 1 <;> ring

private theorem p10_norm_sum4_div_le {n : ℕ}
    (x xHat a b c r : P10Vector n)
    (h : xHat - x = a + b + c + r) :
    p10ForwardError x xHat ≤
      p10VecNorm2 a / p10VecNorm2 x +
        p10VecNorm2 b / p10VecNorm2 x +
          p10VecNorm2 c / p10VecNorm2 x +
            p10VecNorm2 r / p10VecNorm2 x := by
  have ht : p10VecNorm2 (a + b + c + r) ≤
      p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c +
        p10VecNorm2 r := by
    calc
      p10VecNorm2 (a + b + c + r) ≤
          p10VecNorm2 (a + b + c) + p10VecNorm2 r :=
        p10VecNorm2_add_le (a + b + c) r
      _ ≤ p10VecNorm2 a + p10VecNorm2 b + p10VecNorm2 c +
          p10VecNorm2 r := by
        have h1 := p10VecNorm2_add_le (a + b) c
        have h2 := p10VecNorm2_add_le a b
        linarith
  unfold p10ForwardError
  rw [h]
  have hnonneg : 0 ≤ p10VecNorm2 x := by unfold p10VecNorm2; positivity
  have hdiv := div_le_div_of_nonneg_right ht hnonneg
  convert hdiv using 1 <;> ring

private theorem p10StaticKappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
      have h₁ : 0 ≤ p10FrobNorm Ainv := by
        letI : NormedAddCommGroup (P10Matrix n) := Matrix.frobeniusNormedAddCommGroup
        unfold p10FrobNorm
        exact norm_nonneg _
      have h₂ : 0 ≤ p10FrobNorm A := by
        letI : NormedAddCommGroup (P10Matrix n) := Matrix.frobeniusNormedAddCommGroup
        unfold p10FrobNorm
        exact norm_nonneg _
      exact mul_nonneg h₁ h₂
  | inducedTwo =>
      change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
      have h₁ : 0 ≤ p10OpNorm2 A := by
        letI : NormedAddCommGroup (P10Matrix n) := Matrix.instL2OpNormedAddCommGroup
        unfold p10OpNorm2
        exact norm_nonneg _
      have h₂ : 0 ≤ p10OpNorm2 Ainv := by
        letI : NormedAddCommGroup (P10Matrix n) := Matrix.instL2OpNormedAddCommGroup
        unfold p10OpNorm2
        exact norm_nonneg _
      exact mul_nonneg h₁ h₂

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
    obtain ⟨k, hgood, hstop⟩ := p10_select_iteration right.family mgs
    have hc := applicability k hgood hstop
    have e := appendix.expansion k hgood hstop hc
    refine ⟨k, hgood, ?_⟩
    have htri := p10_norm_sum4_div_le
      right.family.system.xExact (right.family.iteration k).xHat
      e.gmresContribution e.reapplicationContribution
      e.matrixContribution e.remainder e.error_decomposition
    have hop : 0 ≤ p10StaticRightOperatorKappa choice right.preconditioner :=
      p10StaticKappa_nonneg choice _ _
    have hmr : 0 ≤ p10StaticRightPreconditionerKappa choice right.preconditioner :=
      p10StaticKappa_nonneg choice _ _
    have hsys : 0 ≤ p10StaticSystemKappa choice right.family :=
      p10StaticKappa_nonneg choice _ _
    have hrho : 0 ≤ (right.iteration k).core.rhoAR := hc.core.parameters_nonneg.2.2.2.2
    have hg : (right.iteration k).core.gmresMagnitude *
        p10StaticRightOperatorKappa choice right.preconditioner *
          p10StaticRightPreconditionerKappa choice right.preconditioner ≤
        (right.family.iteration k).dimensionFactor *
          ((right.iteration k).core.ug *
            p10StaticRightOperatorKappa choice right.preconditioner *
              p10StaticRightPreconditionerKappa choice right.preconditioner) := by
      calc
        _ = (right.iteration k).core.gmresMagnitude *
            (p10StaticRightOperatorKappa choice right.preconditioner *
              p10StaticRightPreconditionerKappa choice right.preconditioner) := by ring
        _ ≤ ((right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ug) *
            (p10StaticRightOperatorKappa choice right.preconditioner *
              p10StaticRightPreconditionerKappa choice right.preconditioner) :=
          mul_le_mul_of_nonneg_right hc.core.gmres_magnitude_bound
            (mul_nonneg hop hmr)
        _ = _ := by ring
    have hr : (right.iteration k).reapplicationMagnitude *
        p10StaticRightPreconditionerKappa choice right.preconditioner ≤
        (right.family.iteration k).dimensionFactor *
          ((right.iteration k).core.um * (right.iteration k).core.etaR *
            p10StaticRightPreconditionerKappa choice right.preconditioner) := by
      calc
        _ ≤ ((right.family.iteration k).dimensionFactor *
            (right.iteration k).core.um * (right.iteration k).core.etaR) *
              p10StaticRightPreconditionerKappa choice right.preconditioner :=
          mul_le_mul_of_nonneg_right hc.reapplication_magnitude_bound hmr
        _ = _ := by ring
    have hm : (right.iteration k).core.matrixMagnitude *
        p10StaticSystemKappa choice right.family *
          (right.iteration k).core.rhoAR ≤
        (right.family.iteration k).dimensionFactor *
          ((right.iteration k).core.ua *
            p10StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) := by
      calc
        _ = (right.iteration k).core.matrixMagnitude *
            (p10StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) := by ring
        _ ≤ ((right.family.iteration k).dimensionFactor *
              (right.iteration k).core.ua) *
            (p10StaticSystemKappa choice right.family *
              (right.iteration k).core.rhoAR) :=
          mul_le_mul_of_nonneg_right hc.core.matrix_magnitude_bound
            (mul_nonneg hsys hrho)
        _ = _ := by ring
    refine ⟨_, e.remainder_second_order, ?_⟩
    have hrem : 0 ≤ p10VecNorm2 e.remainder /
        p10VecNorm2 right.family.system.xExact := by
      apply div_nonneg
      · unfold p10VecNorm2; positivity
      · unfold p10VecNorm2; positivity
    rw [abs_of_nonneg hrem]
    unfold p10StaticRightAttainableEnvelope
    nlinarith [htri, e.gmres_gain_bound, e.reapplication_gain_bound,
      e.matrix_gain_bound, hg, hr, hm]
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hgood, hstop⟩ := p10_select_iteration flexible.family mgs
      have hc := applicability k hgood hstop
      have e := appendix.expansion k hgood hstop hc
      refine ⟨k, hgood, ?_⟩
      have htri := p10_norm_sum3_div_le
        flexible.family.system.xExact (flexible.family.iteration k).xHat
        e.gmresContribution e.matrixContribution e.remainder e.error_decomposition
      have hop : 0 ≤ p10StaticRightOperatorKappa choice flexible.preconditioner :=
        p10StaticKappa_nonneg choice _ _
      have hmr : 0 ≤ p10StaticRightPreconditionerKappa choice flexible.preconditioner :=
        p10StaticKappa_nonneg choice _ _
      have hsys : 0 ≤ p10StaticSystemKappa choice flexible.family :=
        p10StaticKappa_nonneg choice _ _
      have hrho : 0 ≤ (flexible.iteration k).core.rhoAR := hc.core.parameters_nonneg.2.2.2.2
      have hg : (flexible.iteration k).core.gmresMagnitude *
          p10StaticRightOperatorKappa choice flexible.preconditioner *
            p10StaticRightPreconditionerKappa choice flexible.preconditioner ≤
          (flexible.family.iteration k).dimensionFactor *
            ((flexible.iteration k).core.ug *
              p10StaticRightOperatorKappa choice flexible.preconditioner *
                p10StaticRightPreconditionerKappa choice flexible.preconditioner) := by
        calc
          _ = (flexible.iteration k).core.gmresMagnitude *
              (p10StaticRightOperatorKappa choice flexible.preconditioner *
                p10StaticRightPreconditionerKappa choice flexible.preconditioner) := by ring
          _ ≤ ((flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ug) *
              (p10StaticRightOperatorKappa choice flexible.preconditioner *
                p10StaticRightPreconditionerKappa choice flexible.preconditioner) :=
            mul_le_mul_of_nonneg_right hc.core.gmres_magnitude_bound
              (mul_nonneg hop hmr)
          _ = _ := by ring
      have hm : (flexible.iteration k).core.matrixMagnitude *
          p10StaticSystemKappa choice flexible.family *
            (flexible.iteration k).core.rhoAR ≤
          (flexible.family.iteration k).dimensionFactor *
            ((flexible.iteration k).core.ua *
              p10StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) := by
        calc
          _ = (flexible.iteration k).core.matrixMagnitude *
              (p10StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) := by ring
          _ ≤ ((flexible.family.iteration k).dimensionFactor *
                (flexible.iteration k).core.ua) *
              (p10StaticSystemKappa choice flexible.family *
                (flexible.iteration k).core.rhoAR) :=
            mul_le_mul_of_nonneg_right hc.core.matrix_magnitude_bound
              (mul_nonneg hsys hrho)
          _ = _ := by ring
      refine ⟨_, e.remainder_second_order, ?_⟩
      have hrem : 0 ≤ p10VecNorm2 e.remainder /
          p10VecNorm2 flexible.family.system.xExact := by
        apply div_nonneg
        · unfold p10VecNorm2; positivity
        · unfold p10VecNorm2; positivity
      rw [abs_of_nonneg hrem]
      unfold p10StaticFlexibleAttainableEnvelope
      nlinarith [htri, e.gmres_gain_bound, e.matrix_gain_bound, hg, hm]
    · intro family preconditioner ug um ua etaR rhoAR
      unfold p10StaticRightAttainableEnvelope p10StaticFlexibleAttainableEnvelope
      ring

end VSCLReuse

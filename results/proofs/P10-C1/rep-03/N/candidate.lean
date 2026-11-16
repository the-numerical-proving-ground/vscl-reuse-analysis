import VSCLReuse.P10.Definitions
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace VSCLReuse

open scoped Matrix.Norms.L2Operator Matrix.Norms.Frobenius

private lemma p10_vec_norm_eq_euclidean {n : ℕ} (x : P10Vector n) :
    p10VecNorm2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [p10VecNorm2, p10VecNorm2Sq,
    Real.norm_eq_abs, sq_abs]

private lemma p10_vec_norm_add_le {n : ℕ} (x y : P10Vector n) :
    p10VecNorm2 (x + y) ≤ p10VecNorm2 x + p10VecNorm2 y := by
  rw [p10_vec_norm_eq_euclidean, p10_vec_norm_eq_euclidean,
    p10_vec_norm_eq_euclidean, WithLp.toLp_add]
  exact norm_add_le _ _

private lemma p10_vec_norm_nonneg {n : ℕ} (x : P10Vector n) :
    0 ≤ p10VecNorm2 x := by
  rw [p10_vec_norm_eq_euclidean]
  exact norm_nonneg _

private lemma p10_op_norm_nonneg {n : ℕ} (A : P10Matrix n) :
    0 ≤ p10OpNorm2 A := by
  unfold p10OpNorm2
  rw [Matrix.l2_opNorm_def]
  exact norm_nonneg _

private lemma p10_static_kappa_nonneg (choice : P10StaticSquareKappaChoice)
    {n : ℕ} (A Ainv : P10Matrix n) :
    0 ≤ p10StaticKappa choice A Ainv := by
  cases choice with
  | frobenius =>
      change 0 ≤ p10FrobNorm Ainv * p10FrobNorm A
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  | inducedTwo =>
      change 0 ≤ p10OpNorm2 A * p10OpNorm2 Ainv
      exact mul_nonneg (p10_op_norm_nonneg A) (p10_op_norm_nonneg Ainv)

private lemma p10_selected_iteration {n : ℕ}
    (semantics : P10FirstOrderSemantics)
    (family : P10Theorem31Family n semantics)
    (mgs : P10MGSSelectionLaw family) :
    ∃ k : P10Theorem31Dimension n,
      p10IterationWellConditioned (family.iteration k) ∧
        (k.1 = n ∨ p10MGSNearDependence (family.iteration k)) := by
  classical
  letI : Finite (P10Theorem31Dimension n) :=
    Finite.of_injective
      (fun k : P10Theorem31Dimension n =>
        (⟨k.1, Nat.lt_succ_of_le k.2.2⟩ : Fin (n + 1)))
      (by intro a b h; exact Subtype.ext (Fin.ext_iff.mp h))
  letI : Fintype (P10Theorem31Dimension n) := Fintype.ofFinite _
  let s : Finset (P10Theorem31Dimension n) :=
    Finset.univ.filter (fun k => p10IterationWellConditioned (family.iteration k))
  have hs : s.Nonempty := by
    refine ⟨⟨1, Nat.zero_lt_one, family.system.dimension_pos⟩, ?_⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mgs.first_dimension_good
  obtain ⟨k, hk, hmax⟩ := s.exists_max_image (fun k => k.1) hs
  have hgood : p10IterationWellConditioned (family.iteration k) := by
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hk
  refine ⟨k, hgood, ?_⟩
  by_cases hkn : k.1 = n
  · exact Or.inl hkn
  · right
    have hklt : k.1 < n := Nat.lt_of_le_of_ne k.2.2 hkn
    have hnextbad :
        ¬ p10IterationWellConditioned
          (family.iteration
            ⟨k.1 + 1, Nat.succ_pos k.1, Nat.succ_le_iff.mpr hklt⟩) := by
      intro hnext
      have hmem :
          (⟨k.1 + 1, Nat.succ_pos k.1,
            Nat.succ_le_iff.mpr hklt⟩ : P10Theorem31Dimension n) ∈ s := by
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hnext
      exact Nat.not_succ_le_self k.1 (hmax _ hmem)
    exact mgs.loss_implies_near_dependence k.1 k.2.1 hklt hnextbad

private lemma p10_forward_error_four_le {n : ℕ}
    (x xHat gmres reapplication matrix remainder : P10Vector n)
    (hdecomp : xHat - x = gmres + reapplication + matrix + remainder) :
    p10ForwardError x xHat ≤
      p10VecNorm2 gmres / p10VecNorm2 x +
        p10VecNorm2 reapplication / p10VecNorm2 x +
        p10VecNorm2 matrix / p10VecNorm2 x +
        p10VecNorm2 remainder / p10VecNorm2 x := by
  have h₁ := p10_vec_norm_add_le gmres reapplication
  have h₂ := p10_vec_norm_add_le (gmres + reapplication) matrix
  have h₃ := p10_vec_norm_add_le (gmres + reapplication + matrix) remainder
  have hnorm :
      p10VecNorm2 (gmres + reapplication + matrix + remainder) ≤
        p10VecNorm2 gmres + p10VecNorm2 reapplication +
          p10VecNorm2 matrix + p10VecNorm2 remainder := by
    linarith
  calc
    p10ForwardError x xHat =
        p10VecNorm2 (gmres + reapplication + matrix + remainder) /
          p10VecNorm2 x := by rw [p10ForwardError, hdecomp]
    _ ≤ (p10VecNorm2 gmres + p10VecNorm2 reapplication +
          p10VecNorm2 matrix + p10VecNorm2 remainder) /
          p10VecNorm2 x :=
        div_le_div_of_nonneg_right hnorm (p10_vec_norm_nonneg x)
    _ = _ := by ring

private lemma p10_forward_error_three_le {n : ℕ}
    (x xHat gmres matrix remainder : P10Vector n)
    (hdecomp : xHat - x = gmres + matrix + remainder) :
    p10ForwardError x xHat ≤
      p10VecNorm2 gmres / p10VecNorm2 x +
        p10VecNorm2 matrix / p10VecNorm2 x +
        p10VecNorm2 remainder / p10VecNorm2 x := by
  have h₁ := p10_vec_norm_add_le gmres matrix
  have h₂ := p10_vec_norm_add_le (gmres + matrix) remainder
  have hnorm :
      p10VecNorm2 (gmres + matrix + remainder) ≤
        p10VecNorm2 gmres + p10VecNorm2 matrix +
          p10VecNorm2 remainder := by
    linarith
  calc
    p10ForwardError x xHat =
        p10VecNorm2 (gmres + matrix + remainder) /
          p10VecNorm2 x := by rw [p10ForwardError, hdecomp]
    _ ≤ (p10VecNorm2 gmres + p10VecNorm2 matrix +
          p10VecNorm2 remainder) / p10VecNorm2 x :=
        div_le_div_of_nonneg_right hnorm (p10_vec_norm_nonneg x)
    _ = _ := by ring

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
      p10_selected_iteration semantics right.family mgs
    let conditions := applicability k hgood hterminal
    let expansion := appendix.expansion k hgood hterminal conditions
    refine ⟨k, hgood, ?_⟩
    let C : ℝ := p10StaticRightOperatorKappa choice right.preconditioner
    let P : ℝ := p10StaticRightPreconditionerKappa choice right.preconditioner
    let S : ℝ := p10StaticSystemKappa choice right.family
    let D : ℝ := (right.family.iteration k).dimensionFactor
    let ug : ℝ := (right.iteration k).core.ug
    let um : ℝ := (right.iteration k).core.um
    let ua : ℝ := (right.iteration k).core.ua
    let etaR : ℝ := (right.iteration k).core.etaR
    let rhoAR : ℝ := (right.iteration k).core.rhoAR
    let r : ℝ :=
      p10VecNorm2 expansion.remainder / p10VecNorm2 right.family.system.xExact
    have hC : 0 ≤ C := p10_static_kappa_nonneg choice _ _
    have hP : 0 ≤ P := p10_static_kappa_nonneg choice _ _
    have hS : 0 ≤ S := p10_static_kappa_nonneg choice _ _
    have hrho : 0 ≤ rhoAR := conditions.core.parameters_nonneg.2.2.2.2
    have hgmScaled :
        (right.iteration k).core.gmresMagnitude * C * P ≤
          D * ug * C * P := by
      calc
        _ = (right.iteration k).core.gmresMagnitude * (C * P) := by ring
        _ ≤ (D * ug) * (C * P) :=
          mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound
            (mul_nonneg hC hP)
        _ = _ := by ring
    have hreScaled :
        (right.iteration k).reapplicationMagnitude * P ≤
          D * um * etaR * P := by
      exact mul_le_mul_of_nonneg_right conditions.reapplication_magnitude_bound hP
    have hmatScaled :
        (right.iteration k).core.matrixMagnitude * S * rhoAR ≤
          D * ua * S * rhoAR := by
      calc
        _ = (right.iteration k).core.matrixMagnitude * (S * rhoAR) := by ring
        _ ≤ (D * ua) * (S * rhoAR) :=
          mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound
            (mul_nonneg hS hrho)
        _ = _ := by ring
    have htri := p10_forward_error_four_le
      right.family.system.xExact (right.family.iteration k).xHat
      expansion.gmresContribution expansion.reapplicationContribution
      expansion.matrixContribution expansion.remainder expansion.error_decomposition
    have herror :
        p10ForwardError right.family.system.xExact
            (right.family.iteration k).xHat ≤
          D * (ug * C * P + um * etaR * P + ua * S * rhoAR) + r := by
      have hg := expansion.gmres_gain_bound
      have hp := expansion.reapplication_gain_bound
      have hm := expansion.matrix_gain_bound
      dsimp [r] at *
      nlinarith
    refine ⟨r, expansion.remainder_second_order, ?_⟩
    have hr : 0 ≤ r :=
      div_nonneg (p10_vec_norm_nonneg _) (p10_vec_norm_nonneg _)
    rw [abs_of_nonneg hr]
    change p10ForwardError right.family.system.xExact
        (right.family.iteration k).xHat ≤
      D * (ug * C * P + um * etaR * P + ua * S * rhoAR) + r
    exact herror
  · constructor
    · intro flexible mgs appendix applicability
      obtain ⟨k, hgood, hterminal⟩ :=
        p10_selected_iteration semantics flexible.family mgs
      let conditions := applicability k hgood hterminal
      let expansion := appendix.expansion k hgood hterminal conditions
      refine ⟨k, hgood, ?_⟩
      let C : ℝ := p10StaticRightOperatorKappa choice flexible.preconditioner
      let P : ℝ := p10StaticRightPreconditionerKappa choice flexible.preconditioner
      let S : ℝ := p10StaticSystemKappa choice flexible.family
      let D : ℝ := (flexible.family.iteration k).dimensionFactor
      let ug : ℝ := (flexible.iteration k).core.ug
      let ua : ℝ := (flexible.iteration k).core.ua
      let rhoAR : ℝ := (flexible.iteration k).core.rhoAR
      let r : ℝ :=
        p10VecNorm2 expansion.remainder /
          p10VecNorm2 flexible.family.system.xExact
      have hC : 0 ≤ C := p10_static_kappa_nonneg choice _ _
      have hP : 0 ≤ P := p10_static_kappa_nonneg choice _ _
      have hS : 0 ≤ S := p10_static_kappa_nonneg choice _ _
      have hrho : 0 ≤ rhoAR := conditions.core.parameters_nonneg.2.2.2.2
      have hgmScaled :
          (flexible.iteration k).core.gmresMagnitude * C * P ≤
            D * ug * C * P := by
        calc
          _ = (flexible.iteration k).core.gmresMagnitude * (C * P) := by ring
          _ ≤ (D * ug) * (C * P) :=
            mul_le_mul_of_nonneg_right conditions.core.gmres_magnitude_bound
              (mul_nonneg hC hP)
          _ = _ := by ring
      have hmatScaled :
          (flexible.iteration k).core.matrixMagnitude * S * rhoAR ≤
            D * ua * S * rhoAR := by
        calc
          _ = (flexible.iteration k).core.matrixMagnitude * (S * rhoAR) := by ring
          _ ≤ (D * ua) * (S * rhoAR) :=
            mul_le_mul_of_nonneg_right conditions.core.matrix_magnitude_bound
              (mul_nonneg hS hrho)
          _ = _ := by ring
      have htri := p10_forward_error_three_le
        flexible.family.system.xExact (flexible.family.iteration k).xHat
        expansion.gmresContribution expansion.matrixContribution
        expansion.remainder expansion.error_decomposition
      have herror :
          p10ForwardError flexible.family.system.xExact
              (flexible.family.iteration k).xHat ≤
            D * (ug * C * P + ua * S * rhoAR) + r := by
        have hg := expansion.gmres_gain_bound
        have hm := expansion.matrix_gain_bound
        dsimp [r] at *
        nlinarith
      refine ⟨r, expansion.remainder_second_order, ?_⟩
      have hr : 0 ≤ r :=
        div_nonneg (p10_vec_norm_nonneg _) (p10_vec_norm_nonneg _)
      rw [abs_of_nonneg hr]
      change p10ForwardError flexible.family.system.xExact
          (flexible.family.iteration k).xHat ≤
        D * (ug * C * P + ua * S * rhoAR) + r
      exact herror
    · intro family preconditioner ug um ua etaR rhoAR
      unfold p10StaticRightAttainableEnvelope
        p10StaticFlexibleAttainableEnvelope
      ring

end VSCLReuse

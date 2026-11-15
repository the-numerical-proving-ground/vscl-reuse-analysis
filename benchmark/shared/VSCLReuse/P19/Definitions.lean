import Mathlib

namespace VSCLReuse

open scoped BigOperators

abbrev P19Vector (n : ℕ) := Fin n → ℝ

abbrev P19CoefficientMap (n t : ℕ) := Fin n → Fin t → ℝ

/-- Componentwise perturbation boxes for the structured parameters and right-hand side. -/
def P19Admissible {n t : ℕ}
    (g : P19Vector t) (f : P19Vector n)
    (dp : P19Vector t) (db : P19Vector n) : Prop :=
  (∀ j, |dp j| ≤ g j) ∧ (∀ i, |db i| ≤ f i)

/-- The first-order response `A⁻¹ Δb - A⁻¹ X B Δp` in equation (3.2). -/
noncomputable def p19LinearResponse {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (dp : P19Vector t) (db : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j, H i j * db j - ∑ j, K i j * dp j

/-- The attainable relative first-order response norms in the perturbation box. -/
noncomputable def p19LinearizedValues {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ) : Set ℝ :=
  {q | ∃ dp db, P19Admissible g f dp db ∧
      q = ‖p19LinearResponse K H dp db‖ / xNorm}

/-- The worst attainable relative first-order response. -/
noncomputable def p19LinearizedCondition {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ) : ℝ :=
  sSup (p19LinearizedValues K H g f xNorm)

/-- The componentwise radius on the right-hand side of equation (3.3). -/
noncomputable def p19ConditionRadius {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) : P19Vector n :=
  fun i ↦ ∑ j, |K i j| * g j + ∑ j, |H i j| * f j

/-- The explicit structured condition formula in equation (3.4). -/
noncomputable def p19ConditionFormula {n t : ℕ}
    (K : P19CoefficientMap n t) (H : P19CoefficientMap n n)
    (g : P19Vector t) (f : P19Vector n) (xNorm : ℝ) : ℝ :=
  ‖p19ConditionRadius K H g f‖ / xNorm

end VSCLReuse

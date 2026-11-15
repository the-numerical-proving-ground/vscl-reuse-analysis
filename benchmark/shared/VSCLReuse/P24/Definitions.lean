import Mathlib

namespace VSCLReuse

/-- The shifted linear map `A + p I` used in (6.1)--(6.2). -/
def p24Shift {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (p : ℝ) : Module.End ℝ V :=
  A + p • LinearMap.id

/-- The span of `m` consecutive vectors beginning at the integer index `s`. -/
def p24ConsecutiveSpan {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) (s : ℤ) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun k : Fin m ↦ v (s + (k : ℕ)))

/-- The order-`m` ordinary Krylov subspace based on `A` and `b`. -/
def p24KrylovSpan {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (b : V) (m : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun k : Fin m ↦ (A ^ (k : ℕ)) b)

/-- The subspace spanned by the paper's two-sided sequence. -/
def p24TwoSidedSpan {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : ℤ → V) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range v)

end VSCLReuse

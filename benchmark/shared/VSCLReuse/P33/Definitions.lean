import Mathlib

open scoped BigOperators

namespace VSCLReuse

abbrev P33Vector (n : ℕ) := Fin (n + 1) → ℂ
abbrev P33Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Euclidean norm used for the coefficient vector `x` in Section 4. -/
noncomputable def p33VecNorm2 {n : ℕ} (x : P33Vector n) : ℝ :=
  Real.sqrt (∑ i, ‖x i‖ ^ 2)

/-- The first coordinate vector in dimension `n+1`. -/
def p33FirstBasis (n : ℕ) : P33Vector n :=
  fun j => if j.val = 0 then 1 else 0

/-- Read a finite sequence by a natural index, with zero beyond its end. -/
def p33CoreCoeff {n : ℕ} (f : Fin n → ℂ) (k : ℕ) : ℂ :=
  if hk : k < n then f ⟨k, hk⟩ else 0

/-- One application of the adjoint of the core transformation whose active
part is `[u v; w z]`. -/
noncomputable def p33AdjointCoreStep {n : ℕ} (i : Fin n) (u v w z : ℂ)
    (q : P33Vector n) : P33Vector n :=
  fun j =>
    if j = i.castSucc then
      star u * q i.castSucc + star w * q i.succ
    else if j = i.succ then
      star v * q i.castSucc + star z * q i.succ
    else
      q j

/-- The successive vectors obtained while applying
`C₁ᴴ, C₂ᴴ, ..., Cₙᴴ` to the first coordinate vector in the proof of
Theorem 4.1. -/
structure P33CoreRollupRun (n : ℕ) where
  u : Fin n → ℂ
  v : Fin n → ℂ
  w : Fin n → ℂ
  z : Fin n → ℂ
  state : ℕ → P33Vector n
  state_zero : state 0 = p33FirstBasis n
  state_succ : ∀ k (hk : k < n),
    state (k + 1) =
      p33AdjointCoreStep ⟨k, hk⟩ (u ⟨k, hk⟩) (v ⟨k, hk⟩)
        (w ⟨k, hk⟩) (z ⟨k, hk⟩) (state k)

end VSCLReuse

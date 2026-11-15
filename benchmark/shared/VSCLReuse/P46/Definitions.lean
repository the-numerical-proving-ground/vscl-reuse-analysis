import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace VSCLReuse

open scoped BigOperators

/-- The standard relative-error model used in Section 3.2, equations (3.1)--(3.2). -/
structure P46FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  u_low : ℝ
  u_low_nonneg : 0 ≤ u_low
  fl_low : ℝ → ℝ
  model_low : ∀ x : ℝ, |fl_low x - x| ≤ u_low * |x|
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P46Matrix (m n : ℕ) := Fin m → Fin n → ℝ

/-- Exact matrix multiplication in the paper's real-arithmetic analysis. -/
noncomputable def p46MatMul {m n p : ℕ}
    (A : P46Matrix m n) (B : P46Matrix n p) : P46Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

/-- Componentwise absolute value of a matrix. -/
noncomputable def p46AbsMatrix {m n : ℕ}
    (A : P46Matrix m n) : P46Matrix m n :=
  fun i j => |A i j|

/-- The accumulated rounding-error constant from equation (3.1). -/
noncomputable def p46Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

/-- The usual guard under which `p46Gamma` is valid. -/
def P46GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

/-- Sequentially accumulated floating-point dot product. -/
noncomputable def p46RoundedDotProduct (fp : P46FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

/-- Matrix multiplication computed entry by entry with rounded dot products. -/
noncomputable def p46RoundedMatMul (fp : P46FPModel) {m n p : ℕ}
    (A : P46Matrix m n) (B : P46Matrix n p) : P46Matrix m p :=
  fun i j => p46RoundedDotProduct fp n (A i) (fun k => B k j)

/-- Matrix multiplication done at high precision and rounded once to low precision. -/
noncomputable def p46SimulatedMatMul (fp : P46FPModel) {m n p : ℕ}
    (A : P46Matrix m n) (B : P46Matrix n p) : P46Matrix m p :=
  fun i j => fp.fl_low (p46RoundedMatMul fp A B i j)

/-- The same high/low precision setting for a triangular solve. -/
structure P46TriFPModel extends P46FPModel where
  fl_sub : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

/-- High-precision back substitution for Section 3.2. -/
noncomputable def p46BackSubSteps (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      p46BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'

noncomputable def p46BackSub (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p46BackSubSteps fp n U b n (le_refl n) (fun _ => 0)

/-- The final low-precision storage of a computed high-precision solve. -/
noncomputable def p46SimulatedBackSub (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fp.fl_low (p46BackSub fp n U b i)

end VSCLReuse

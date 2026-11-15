import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius

structure StandardFPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_sqrt : ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)
  model_sqrt : ∀ x : ℝ, 0 ≤ x → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sqrt x = Real.sqrt x * (1 + δ)

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def roundedDotProduct (fp : StandardFPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n + 1 =>
      Fin.foldl n
        (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def roundedMatVec (fp : StandardFPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ roundedDotProduct fp n (A i) x

noncomputable def roundedForwardSubSteps (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ k : ℕ, k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      roundedForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def roundedForwardSub (fp : StandardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  roundedForwardSubSteps fp n L b n (le_refl n) (fun _ ↦ 0)

abbrev P08Matrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

abbrev P08RectMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

abbrev P08Vector (n : ℕ) := Fin n → ℝ

noncomputable def p08RectMatMul {m n p : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) :
    P08RectMatrix m p :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p08MatMul {n : ℕ} (A B : P08Matrix n) : P08Matrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p08MatVec {n : ℕ} (A : P08Matrix n)
    (x : P08Vector n) : P08Vector n :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p08RectFrobNorm {m n : ℕ}
    (A : P08RectMatrix m n) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)

noncomputable def p08FrobNorm {n : ℕ} (A : P08Matrix n) : ℝ :=
  p08RectFrobNorm A

def p08RectTranspose {m n : ℕ} (A : P08RectMatrix m n) :
    P08RectMatrix n m :=
  fun j i ↦ A i j

def p08RectAdd {m n : ℕ}
    (A B : P08RectMatrix m n) : P08RectMatrix m n :=
  fun i j ↦ A i j + B i j

noncomputable def p08RectMatVec {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i ↦ ∑ j : Fin n, A i j * x j

noncomputable def p08RoundedRectMatVec (fp : StandardFPModel) {m n : ℕ}
    (A : P08RectMatrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  roundedMatVec fp m n A x

noncomputable def p08RoundedLowRankMatVec (fp : StandardFPModel) {b r : ℕ}
    (X Y : P08RectMatrix b r) (v : P08Vector b) : P08Vector b :=
  p08RoundedRectMatVec fp X
    (p08RoundedRectMatVec fp (p08RectTranspose Y) v)

def p08LowerTriangular {n : ℕ} (L : P08Matrix n) : Prop :=
  ∀ i j, i.val < j.val → L i j = 0

noncomputable def p08LowRankMatrix {b r : ℕ}
    (X Y : P08RectMatrix b r) : P08Matrix b :=
  p08RectMatMul X (p08RectTranspose Y)

def p08OrthonormalColumns {b r : ℕ} (X : P08RectMatrix b r) : Prop :=
  ∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0

noncomputable def p08GammaReal (k u : ℝ) : ℝ :=
  k * u / (1 - k * u)

noncomputable def p08LowRankMatMulCost (b r : ℕ) : ℝ :=
  (b : ℝ) + 2 * (r : ℝ) * Real.sqrt (r : ℝ)

structure P08RoundedMatMulStage (m n p : ℕ) (u : ℝ)
    (A : P08RectMatrix m n) (B : P08RectMatrix n p) where
  error : P08RectMatrix m p
  error_le : p08RectFrobNorm error ≤
    p08GammaReal (n : ℝ) u * p08RectFrobNorm A * p08RectFrobNorm B

noncomputable def P08RoundedMatMulStage.result {m n p : ℕ} {u : ℝ}
    {A : P08RectMatrix m n} {B : P08RectMatrix n p}
    (stage : P08RoundedMatMulStage m n p u A B) : P08RectMatrix m p :=
  p08RectMatMul A B + stage.error

inductive P08LowRankMatMulTrace {b r : ℕ} (u : ℝ)
    (XA YA XB YB : P08RectMatrix b r) where
  | leftAssociated
      (middleStage : P08RoundedMatMulStage r b r u
        (p08RectTranspose YA) YB)
      (leftStage : P08RoundedMatMulStage b r r u XA middleStage.result)
      (finalStage : P08RoundedMatMulStage b r b u leftStage.result
        (p08RectTranspose XB))
  | rightAssociated
      (middleStage : P08RoundedMatMulStage r b r u
        (p08RectTranspose YA) YB)
      (rightStage : P08RoundedMatMulStage r r b u middleStage.result
        (p08RectTranspose XB))
      (finalStage : P08RoundedMatMulStage b r b u XA rightStage.result)

noncomputable def P08LowRankMatMulTrace.result {b r : ℕ} {u : ℝ}
    {XA YA XB YB : P08RectMatrix b r}
    (trace : P08LowRankMatMulTrace u XA YA XB YB) : P08Matrix b :=
  match trace with
  | .leftAssociated _ _ finalStage => finalStage.result
  | .rightAssociated _ _ finalStage => finalStage.result

structure P08LowRankMatMulExecution (b r : ℕ) where
  A : P08Matrix b
  B : P08Matrix b
  XA : P08RectMatrix b r
  YA : P08RectMatrix b r
  XB : P08RectMatrix b r
  YB : P08RectMatrix b r
  epsilon : ℝ
  betaA : ℝ
  betaB : ℝ
  unitRoundoff : ℝ
  unitRoundoff_nonneg : 0 ≤ unitRoundoff
  gamma_valid :
    p08LowRankMatMulCost b r * unitRoundoff < 1
  xA_orthonormal : p08OrthonormalColumns XA
  xB_orthonormal : p08OrthonormalColumns XB
  approximationErrorA : P08Matrix b
  approximationErrorB : P08Matrix b
  approximationA_eq :
    p08LowRankMatrix XA YA = A + approximationErrorA
  approximationB_eq :
    p08LowRankMatrix YB XB = B + approximationErrorB
  approximationErrorA_le :
    p08FrobNorm approximationErrorA ≤ epsilon * betaA
  approximationErrorB_le :
    p08FrobNorm approximationErrorB ≤ epsilon * betaB
  trace : P08LowRankMatMulTrace unitRoundoff XA YA XB YB


/-- Block objects and the concrete ordered BLR solve trace for Theorem 4.4. -/
abbrev P08BlockMatrix (p b : ℕ) :=
  Fin p → Fin p → P08Matrix b

abbrev P08BlockVector (p b : ℕ) :=
  Fin p → P08Vector b

def p08AssembleMatrix {p b : ℕ} (T : P08BlockMatrix p b) :
    Matrix (Fin p × Fin b) (Fin p × Fin b) ℝ :=
  fun i j => T i.1 j.1 i.2 j.2

def p08AssembleVector {p b : ℕ} (v : P08BlockVector p b) :
    Fin p × Fin b → ℝ :=
  fun i => v i.1 i.2

noncomputable def p08BlockFrobNorm {p b : ℕ}
    (T : P08BlockMatrix p b) : ℝ :=
  Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
    ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2)

noncomputable def p08BlockVecNorm {p b : ℕ}
    (v : P08BlockVector p b) : ℝ :=
  Real.sqrt (∑ i : Fin p, ∑ α : Fin b, (v i α) ^ 2)

structure P08BLRTrace
    (fp : StandardFPModel) {p b r : ℕ}
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b) where
  x : P08BlockVector p b
  rhs : P08BlockVector p b
  rhs_eq : ∀ i : Fin p,
    rhs i = Fin.foldl i.val
      (fun acc (j : Fin i.val) =>
        let j' : Fin p := ⟨j.val, by omega⟩
        fun α => fp.fl_sub (acc α)
          (p08RoundedLowRankMatVec fp (X i j') (Y i j') (x j') α))
      (v i)
  x_eq : ∀ i : Fin p,
    x i = roundedForwardSub fp b (T i i) (rhs i)


end VSCLReuse

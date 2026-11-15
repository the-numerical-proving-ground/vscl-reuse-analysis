import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Castaldo–Whaley–Chronopoulos, two-level superblock dot product. -/

structure P43FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

noncomputable def p43Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P43GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p43RecursiveSum (fp : P43FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p43BlockDot (fp : P43FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p43SuperblockDot (fp : P43FPModel) (b : ℕ)
    (x y : Fin b → Fin b → ℝ) : ℝ :=
  p43RecursiveSum fp b (fun i => p43BlockDot fp b (x i) (y i))

/-- Proposition 3.1's two-level, b-by-b superblock summation. -/
noncomputable def p43SuperblockSum (fp : P43FPModel) (b : ℕ)
    (x : Fin b → Fin b → ℝ) : ℝ :=
  p43RecursiveSum fp b (fun i => p43RecursiveSum fp b (x i))


/-- A complete `b`-ary tree of `t` superblock levels; its leaves are the
`N=b^t` input pairs of Proposition 3.2. -/
inductive P43DotTree (b : ℕ) : ℕ → Type where
  | leaf (x y : ℝ) : P43DotTree b 0
  | node {t : ℕ} (children : Fin b → P43DotTree b t) : P43DotTree b (t + 1)

noncomputable def P43DotTree.exact {b : ℕ} :
    {t : ℕ} → P43DotTree b t → ℝ
  | 0, .leaf x y => x * y
  | _ + 1, .node children => ∑ i : Fin b, (children i).exact

noncomputable def P43DotTree.absMass {b : ℕ} :
    {t : ℕ} → P43DotTree b t → ℝ
  | 0, .leaf x y => |x * y|
  | _ + 1, .node children => ∑ i : Fin b, (children i).absMass

noncomputable def P43DotTree.computed {b : ℕ} (fp : P43FPModel) :
    {t : ℕ} → P43DotTree b t → ℝ
  | 0, .leaf x y => fp.fl_mul x y
  | _ + 1, .node children =>
      p43RecursiveSum fp b (fun i : Fin b => (children i).computed fp)

end VSCLReuse

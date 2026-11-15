import Mathlib

namespace VSCLReuse

open scoped BigOperators

structure P49FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P49Matrix (m n : ℕ) := Fin m → Fin n → ℝ

noncomputable def p49Gamma (u : ℝ) (n : ℕ) : ℝ :=
  (n * u) / (1 - n * u)

def P49GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p49MatMul {m n p : ℕ}
    (A : P49Matrix m n) (B : P49Matrix n p) : P49Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p49RoundedDot (fp : P49FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p49RoundedMatMul (fp : P49FPModel) {m n p : ℕ}
    (A : P49Matrix m n) (B : P49Matrix n p) : P49Matrix m p :=
  fun i j => p49RoundedDot fp n (A i) (fun k => B k j)

noncomputable def p49RoundedSchur (fp : P49FPModel) {n m : ℕ}
    (C : P49Matrix m n) (V : P49Matrix n m) (D : P49Matrix m m) :
    P49Matrix m m :=
  fun i j => fp.fl_sub (D i j) (p49RoundedMatMul fp C V i j)

abbrev P49BlockIndex (n m : ℕ) := Fin n ⊕ Fin m
abbrev P49BlockMatrix (n m : ℕ) := P49BlockIndex n m → P49BlockIndex n m → ℝ

noncomputable def p49BorderedMatrix {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m) :
    P49BlockMatrix n m :=
  fun i j => match i, j with
  | .inl i, .inl j => A i j
  | .inl i, .inr j => B i j
  | .inr i, .inl j => C i j
  | .inr i, .inr j => D i j

noncomputable def p49ComputedBlockLU {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n)
    (V : P49Matrix n m) (Delta : P49Matrix m m) :
    P49BlockMatrix n m :=
  p49BorderedMatrix A (p49MatMul A V) C
    (fun i j => p49MatMul C V i j + Delta i j)

noncomputable def p49LowerFactor {n m : ℕ}
    (A : P49Matrix n n) (C : P49Matrix m n) : P49BlockMatrix n m :=
  p49BorderedMatrix A (fun _ _ => 0) C (fun i j => if i = j then 1 else 0)

noncomputable def p49UpperFactor {n m : ℕ}
    (V : P49Matrix n m) (Delta : P49Matrix m m) : P49BlockMatrix n m :=
  p49BorderedMatrix (fun i j => if i = j then 1 else 0) V
    (fun _ _ => 0) Delta

noncomputable def p49BlockMatMul {n m : ℕ}
    (L U : P49BlockMatrix n m) : P49BlockMatrix n m :=
  fun i j => ∑ k : P49BlockIndex n m, L i k * U k j

noncomputable def p49FactorizationMajorant {n m : ℕ}
    (A : P49Matrix n n) (B : P49Matrix n m)
    (C : P49Matrix m n) (D : P49Matrix m m)
    (V : P49Matrix n m) :
    P49BlockMatrix n m :=
  p49BlockMatMul
    (fun i j => |p49BorderedMatrix A B C D i j|)
    (p49BorderedMatrix (fun _ _ => 0) (fun i j => |V i j|)
      (fun _ _ => 0) (fun i j => if i = j then 1 else 0))

end VSCLReuse

import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Private paper-scoped source-order quotient model for Fuda–Campagna–Hormann. -/
structure P52FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_sub : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_div : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_sub : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_sub x y = (x - y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)
  model_div : ∀ x y : ℝ, y ≠ 0 → ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_div x y = (x / y) * (1 + δ)

noncomputable def p52Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P52GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p52RoundedDotProduct (fp : P52FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc
        (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p52RecursiveSum (fp : P52FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  Fin.foldl n (fun acc i => fp.fl_add acc (v i)) 0

noncomputable def p52ComputedQuotient (fp : P52FPModel) (N M : ℕ)
    (ahat : Fin N → ℝ) (f : Fin N → ℝ) (bhat : Fin M → ℝ) : ℝ :=
  fp.fl_div (p52RoundedDotProduct fp N ahat f)
    (p52RecursiveSum fp M bhat)


/-- The numerator cancellation factor in the paper's equation (17). -/
noncomputable def p52NumeratorCondition (N : ℕ)
    (a f : Fin N → ℝ) : ℝ :=
  (∑ i : Fin N, |a i| * |f i|) / |∑ i : Fin N, a i * f i|

/-- The denominator cancellation factor in the paper's equation (18). -/
noncomputable def p52DenominatorCondition (M : ℕ)
    (b : Fin M → ℝ) : ℝ :=
  (∑ j : Fin M, |b j|) / |∑ j : Fin M, b j|

/-! Source-order evaluation model for the directly computed weights in Lemma 2. -/
noncomputable def p52Lemma2RoundedDenom (fp : P52FPModel) (x : ℝ) :
    (d : ℕ) → (Fin (d + 1) → ℝ) → ℝ
  | 0, nodes => fp.fl_sub x (nodes 0)
  | d + 1, nodes =>
      fp.fl_mul
        (p52Lemma2RoundedDenom fp x d (fun j => nodes j.castSucc))
        (fp.fl_sub x (nodes (Fin.last (d + 1))))

noncomputable def p52Lemma2ExactLambda (x : ℝ) (d : ℕ)
    (nodes : Fin (d + 1) → ℝ) (sign : ℝ) : ℝ :=
  sign / (∏ j : Fin (d + 1), (x - nodes j))

noncomputable def p52Lemma2RoundedLambda (fp : P52FPModel) (x : ℝ) (d : ℕ)
    (nodes : Fin (d + 1) → ℝ) (sign : ℝ) : ℝ :=
  fp.fl_div sign (p52Lemma2RoundedDenom fp x d nodes)


noncomputable def p52Lemma2Window (n d : ℕ) (hd : d ≤ n)
    (nodes : Fin (n + 1) → ℝ) (i : Fin (n - d + 1)) :
    Fin (d + 1) → ℝ :=
  fun j => nodes ⟨i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    omega⟩

end VSCLReuse

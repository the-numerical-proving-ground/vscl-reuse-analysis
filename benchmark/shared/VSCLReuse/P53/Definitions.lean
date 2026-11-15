import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Floating-point execution model for the two algorithms in Plonka–Tasche Theorem 2. -/

structure P53FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = x * y * (1 + δ)

noncomputable def p53Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

def P53GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

lemma p53_left_lt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ]
  omega

lemma p53_right_lt (r : ℕ) (i : Fin (2 ^ r)) :
    i.val + 2 ^ r < 2 ^ (r + 1) := by
  have := i.isLt
  simp [pow_succ] at *
  omega

/-- Source-order balanced cascade summation of a power-of-two input. -/
noncomputable def p53PairwiseSum (fp : P53FPModel) :
    (r : ℕ) → (Fin (2 ^ r) → ℝ) → ℝ
  | 0, v => v ⟨0, by norm_num⟩
  | r + 1, v => fp.fl_add
      (p53PairwiseSum fp r (fun i => v ⟨i.val, p53_left_lt r i⟩))
      (p53PairwiseSum fp r (fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩))

/-- A generic zero pad used for the source cascade schedule. -/
noncomputable def p53ScalarPad (n m : ℕ) (v : Fin n → ℝ)
    (i : Fin m) : ℝ :=
  if h : i.val < n then v ⟨i.val, h⟩ else 0

/-- Zero-padding to the next power of two keeps the arbitrary row length. -/
noncomputable def p53ZeroPad (n : ℕ) (v : Fin n → ℝ)
    (i : Fin (2 ^ Nat.clog 2 n)) : ℝ :=
  p53ScalarPad n (2 ^ Nat.clog 2 n) v i

noncomputable def p53CascadeSum (fp : P53FPModel) (n : ℕ)
    (v : Fin n → ℝ) : ℝ :=
  p53PairwiseSum fp (Nat.clog 2 n) (p53ZeroPad n v)

noncomputable def p53CascadeDot (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) : ℝ :=
  p53CascadeSum fp n (fun i => fp.fl_mul (a i) (x i))

noncomputable def p53Dot (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) : ℝ :=
  match k with
  | 0 => 0
  | k' + 1 =>
      Fin.foldl k' (fun acc t => fp.fl_add acc
        (fp.fl_mul (a t.succ) (x t.succ)))
        (fp.fl_mul (a 0) (x 0))

noncomputable def p53Sign (a : ℝ) : ℝ :=
  if a = 0 then 0 else a / |a|

/-- An ordered enumeration of exactly the nonzero columns in each source row. -/
structure P53SparseSchedule {m n : ℕ} (A : Fin m → Fin n → ℝ) (l : ℕ) where
  count : Fin m → ℕ
  count_le : ∀ i, count i ≤ l
  col : ∀ i, Fin (count i) → Fin n
  col_injective : ∀ i, Function.Injective (col i)
  col_nonzero : ∀ i t, A i (col i t) ≠ 0
  covers : ∀ i j, A i j ≠ 0 → ∃ t, col i t = j

noncomputable def p53SparseMatVec (fp : P53FPModel) {m n l : ℕ}
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P53SparseSchedule A l) : Fin m → ℝ :=
  fun i => p53Dot fp (schedule.count i)
    (fun t => Ahat i (schedule.col i t))
    (fun t => x (schedule.col i t))


noncomputable def p53SparseCascadeMatVec (fp : P53FPModel) {m n l : ℕ}
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P53SparseSchedule A l) : Fin m → ℝ :=
  fun i => p53CascadeDot fp (schedule.count i)
    (fun t => Ahat i (schedule.col i t))
    (fun t => x (schedule.col i t))

/-- Every source matrix satisfying the row sparsity condition has an ordered
    execution schedule (chosen in increasing column order). -/
noncomputable def p53CanonicalSchedule {m n l : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ l) :
    P53SparseSchedule A l := by
  let support (i : Fin m) : Finset (Fin n) :=
    Finset.univ.filter (fun j => A i j ≠ 0)
  let order (i : Fin m) : Fin (support i).card ≃o (support i) :=
    Finset.orderIsoOfFin (support i) rfl
  refine {
    count := fun i => (support i).card
    count_le := ?_
    col := fun i t => (order i t).val
    col_injective := ?_
    col_nonzero := ?_
    covers := ?_
  }
  · intro i
    exact hcard i
  · intro i a b hab
    apply (order i).injective
    exact Subtype.ext hab
  · intro i t
    exact (Finset.mem_filter.mp (order i t).property).2
  · intro i j hj
    refine ⟨(order i).symm ⟨j, ?_⟩, ?_⟩
    · simp [support, hj]
    · simp




noncomputable def p53SourceRecursiveMatVec (fp : P53FPModel) {m n l : ℕ}
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ l) :
    Fin m → ℝ :=
  p53SparseMatVec fp A Ahat x (p53CanonicalSchedule A hcard)

noncomputable def p53SourceCascadeMatVec (fp : P53FPModel) {m n l : ℕ}
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ l) :
    Fin m → ℝ :=
  p53SparseCascadeMatVec fp A Ahat x (p53CanonicalSchedule A hcard)

end VSCLReuse

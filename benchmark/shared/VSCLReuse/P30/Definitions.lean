import Mathlib

open scoped BigOperators

namespace VSCLReuse

abbrev P30Vector (n : ℕ) := Fin n → ℝ
abbrev P30Matrix (n : ℕ) := Fin n → Fin n → ℝ

noncomputable def p30MatMul {n : ℕ}
    (A B : P30Matrix n) : P30Matrix n :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p30MatVec {n : ℕ}
    (A : P30Matrix n) (x : P30Vector n) : P30Vector n :=
  fun i => ∑ j : Fin n, A i j * x j

def p30Id (n : ℕ) : P30Matrix n :=
  fun i j => if i = j then 1 else 0

noncomputable def p30VecNorm (x : P30Vector n) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

noncomputable def p30Inner (x y : P30Vector n) : ℝ :=
  ∑ i : Fin n, x i * y i

def p30Basis (j : Fin n) : P30Vector n :=
  fun i => if i = j then 1 else 0

/-- The exact plane rotation used in the QR factorization in the proof of
P30, Lemma 5.1. -/
noncomputable def p30GivensRotation (n : ℕ) (p q : Fin n) (c s : ℝ) :
    P30Matrix n :=
  fun i j =>
    if i = p ∧ j = p then c
    else if i = q ∧ j = q then c
    else if i = p ∧ j = q then s
    else if i = q ∧ j = p then -s
    else if i = j then 1
    else 0

/-- One valid Givens rotation in the product `Omega_m ... Omega_k` used in
the proof of P30, Lemma 5.1. -/
structure P30GivensStep (n : ℕ) where
  p : Fin n
  q : Fin n
  c : ℝ
  s : ℝ
  distinct : p ≠ q
  unit : c ^ 2 + s ^ 2 = 1

noncomputable def P30GivensStep.matrix {n : ℕ}
    (step : P30GivensStep n) : P30Matrix n :=
  p30GivensRotation n step.p step.q step.c step.s

/-- Ordered product of the Givens rotations. If the list is
`[Omega_k, ..., Omega_m]`, this returns `Omega_m ... Omega_k`. -/
noncomputable def p30GivensProduct {n : ℕ} :
    List (P30GivensStep n) → P30Matrix n
  | [] => p30Id n
  | step :: steps => p30MatMul (p30GivensProduct steps) step.matrix

/-- Paper model for the adjacent Givens rotations (5.1)–(5.2). -/
structure P30Lemma51Angles (m : ℕ) where
  c : Fin m → ℝ
  s : Fin m → ℝ
  unit : ∀ i, c i ^ 2 + s i ^ 2 = 1

def p30_lemma51_step {m : ℕ} (a : P30Lemma51Angles m)
    (i : Fin m) : P30GivensStep (m + 1) where
  p := i.castSucc
  q := i.succ
  c := a.c i
  s := a.s i
  distinct := Fin.castSucc_lt_succ.ne
  unit := a.unit i

noncomputable def p30_lemma51_steps {m : ℕ}
    (a : P30Lemma51Angles m) : List (P30GivensStep (m + 1)) :=
  List.ofFn (fun i : Fin m => p30_lemma51_step a i)

noncomputable def p30_lemma51_qt {m : ℕ}
    (a : P30Lemma51Angles m) : P30Matrix (m + 1) :=
  p30GivensProduct (p30_lemma51_steps a)

noncomputable def p30_lemma51_g {m : ℕ}
    (a : P30Lemma51Angles m) (β : ℝ) : Fin m → ℝ :=
  fun i => p30MatVec (p30_lemma51_qt a)
    (fun j => if j = (0 : Fin (m + 1)) then β else 0) i.castSucc

noncomputable def p30_lemma51_trace {m : ℕ}
    (a : P30Lemma51Angles m) (β : ℝ) : ℕ → P30Vector (m + 1)
  | 0 => fun j => if j = 0 then β else 0
  | k + 1 =>
      if h : k < m then
        p30MatVec (p30_lemma51_step a ⟨k, h⟩).matrix
          (p30_lemma51_trace a β k)
      else p30_lemma51_trace a β k

def p30_lemma51_prefixSteps {m : ℕ}
    (a : P30Lemma51Angles m) : ℕ → List (P30GivensStep (m + 1))
  | 0 => []
  | k + 1 =>
      if h : k < m then p30_lemma51_prefixSteps a k ++
        [p30_lemma51_step a ⟨k, h⟩]
      else p30_lemma51_prefixSteps a k

/-- The rectangular (m+1)-by-m Hessenberg matrix in P30 Lemma 5.1. -/
abbrev P30TallMatrix (m : ℕ) := Fin (m + 1) → Fin m → ℝ

noncomputable def p30_tall_matvec {m : ℕ}
    (H : P30TallMatrix m) (x : P30Vector m) : P30Vector (m + 1) :=
  fun i => ∑ j : Fin m, H i j * x j

noncomputable def p30_tall_left_mul {m : ℕ}
    (Q : P30Matrix (m + 1)) (B : P30TallMatrix m) : P30TallMatrix m :=
  fun i j => ∑ k : Fin (m + 1), Q i k * B k j

def p30_tall_embed_matrix {m : ℕ}
    (R : P30Matrix m) : P30TallMatrix m :=
  fun i j => if h : i.val < m then R ⟨i.val, h⟩ j else 0

def p30_tall_embed_vector {m : ℕ}
    (y : P30Vector m) : P30Vector (m + 1) :=
  fun i => if h : i.val < m then y ⟨i.val, h⟩ else 0

def p30_lemma51_headVec {m : ℕ}
    (k : ℕ) (x : P30Vector (m + 1)) : P30Vector (m + 1) :=
  fun j => if j.val < k then x j else 0

/-- The Arnoldi basis matrix, with the ambient dimension independent of the
    Krylov iteration count. -/
noncomputable def p30_lemma51_basisMatVec {n m : ℕ}
    (V : Fin n → Fin (m + 1) → ℝ)
    (x : P30Vector (m + 1)) : P30Vector n :=
  fun i => ∑ j : Fin (m + 1), V i j * x j

end VSCLReuse

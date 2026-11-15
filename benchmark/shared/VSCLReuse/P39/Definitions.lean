import Mathlib

namespace VSCLReuse

open scoped BigOperators

/-! Paper-local rounded triangular inverses and final product for Method D in Section 3.4. -/

structure P39FPModel where
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

abbrev P39Matrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

noncomputable def p39Gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def P39GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def p39MatMul {m n p : ℕ}
    (A : P39Matrix m n) (B : P39Matrix n p) : P39Matrix m p :=
  fun i j => ∑ k : Fin n, A i k * B k j

noncomputable def p39RoundedDotProduct (fp : P39FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i => fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p39RoundedMatMul (fp : P39FPModel) {m n p : ℕ}
    (A : P39Matrix m n) (B : P39Matrix n p) : P39Matrix m p :=
  fun i j => p39RoundedDotProduct fp n (A i) (fun k => B k j)

noncomputable def p39ForwardSubSteps (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0, _, x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      p39ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'

noncomputable def p39ForwardSub (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p39ForwardSubSteps fp n L b n (le_refl n) (fun _ => 0)

noncomputable def p39BackSubSteps (fp : P39FPModel) (n : ℕ)
    (U : P39Matrix n n) (b : Fin n → ℝ) :
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
      p39BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'

noncomputable def p39BackSub (fp : P39FPModel) (n : ℕ)
    (U : P39Matrix n n) (b : Fin n → ℝ) : Fin n → ℝ :=
  p39BackSubSteps fp n U b n (le_refl n) (fun _ => 0)

/-- Method 1 in Section 2 applied to each column of the lower triangular inverse. -/
noncomputable def p39LowerInverse (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) : P39Matrix n n :=
  fun i j => p39ForwardSub fp n L (fun k => if k = j then 1 else 0) i

/-- The upper-triangular analogue of Method 1. -/
noncomputable def p39UpperInverse (fp : P39FPModel) (n : ℕ)
    (U : P39Matrix n n) : P39Matrix n n :=
  fun i j => p39BackSub fp n U (fun k => if k = j then 1 else 0) i

/-- Method D's final rounded product of the two computed triangular inverses. -/
noncomputable def p39ComputedInverse (fp : P39FPModel) (n : ℕ)
    (L U : P39Matrix n n) : P39Matrix n n :=
  p39RoundedMatMul fp (p39UpperInverse fp n U) (p39LowerInverse fp n L)

/-- Scalar indices grouped into the consecutive blocks of Method 1B. -/
abbrev P39BlockIndex {k : ℕ} (d : Fin k → ℕ) :=
  Σ j : Fin k, Fin (d j)

/-- The ordinary scalar order within an arbitrary lower triangular block partition. -/
def P39ScalarBefore {k : ℕ} {d : Fin k → ℕ} :
    P39BlockIndex d → P39BlockIndex d → Prop :=
  Sigma.Lex (· < ·) (fun _ : Fin k => (· < ·))

def P39ScalarLower {k : ℕ} {d : Fin k → ℕ}
    (M : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) : Prop :=
  ∀ a b, P39ScalarBefore a b → M a b = 0

/-- Scalar rows after one diagonal block in Method 1B. -/
abbrev P39SuffixIndex {k : ℕ} (d : Fin k → ℕ) (j : Fin k) :=
  Σₗ t : {t : Fin k // j < t}, Fin (d t.val)

def p39_suffix_embed {k : ℕ} {d : Fin k → ℕ} {j : Fin k}
    (v : P39SuffixIndex d j) : P39BlockIndex d :=
  Sigma.mk v.1.val v.2

noncomputable def p39_suffix_order_equiv
    {k : ℕ} {d : Fin k → ℕ} (j : Fin k) :
    Fin (Fintype.card (P39SuffixIndex d j)) ≃ P39SuffixIndex d j :=
  (monoEquivOfFin (P39SuffixIndex d j) rfl).toEquiv

def p39_block_diag {k : ℕ} {d : Fin k → ℕ}
    (M : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ)
    (i : Fin k) : P39Matrix (d i) (d i) :=
  fun a b => M (Sigma.mk i a) (Sigma.mk i b)

def p39_block_cross {k : ℕ} {d : Fin k → ℕ}
    (L : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) (j : Fin k)
    (e : Fin (Fintype.card (P39SuffixIndex d j)) ≃ P39SuffixIndex d j) :
    P39Matrix (Fintype.card (P39SuffixIndex d j)) (d j) :=
  fun q b => L (p39_suffix_embed (e q)) (Sigma.mk j b)

def p39_block_suffix {k : ℕ} {d : Fin k → ℕ}
    (L : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) (j : Fin k)
    (e : Fin (Fintype.card (P39SuffixIndex d j)) ≃ P39SuffixIndex d j) :
    P39Matrix (Fintype.card (P39SuffixIndex d j))
      (Fintype.card (P39SuffixIndex d j)) :=
  fun q r => L (p39_suffix_embed (e q)) (p39_suffix_embed (e r))

/-- One block column of Method 1B: a rounded cross product and a triangular solve. -/
noncomputable def p39IBLowerBlock
    (fp : P39FPModel) (r s : ℕ)
    (L11 : P39Matrix r r) (L21 : P39Matrix s r)
    (L22 : P39Matrix s s) : P39Matrix s r :=
  let X11 := p39LowerInverse fp r L11
  let Bhat := p39RoundedMatMul fp L21 X11
  fun i j => p39ForwardSub fp s L22 (fun k => -Bhat k j) i

/-- Method 1B applied to every block column of an arbitrary lower triangular partition. -/
noncomputable def p39IBGlobalInverse
    (fp : P39FPModel) {k : ℕ} (d : Fin k → ℕ)
    (L : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) :
    Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ :=
  fun a b =>
    if h : a.1 = b.1 then
      p39LowerInverse fp (d b.1) (p39_block_diag L b.1) (h ▸ a.2) b.2
    else if hlt : b.1 < a.1 then
      p39IBLowerBlock fp (d b.1) (Fintype.card (P39SuffixIndex d b.1))
        (p39_block_diag L b.1)
        (p39_block_cross L b.1 (p39_suffix_order_equiv b.1))
        (p39_block_suffix L b.1 (p39_suffix_order_equiv b.1))
        ((p39_suffix_order_equiv b.1).symm
          (Sigma.mk (⟨a.1, hlt⟩ : {t : Fin k // b.1 < t}) a.2)) b.2
    else 0





noncomputable def p39Method2SourceStep (fp : P39FPModel) (n : ℕ)
    (L X : P39Matrix n n) (j : Fin n) : P39Matrix n n :=
  let d := fp.fl_div 1 (L j j)
  fun i k =>
    if hkj : k = j then
      if hij : i = j then d
      else if hijlt : j.val < i.val then
        fp.fl_mul (-d)
          (p39RoundedDotProduct fp (n - j.val - 1)
            (fun t => X i ⟨j.val + 1 + t.val, by omega⟩)
            (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j))
      else 0
    else X i k


noncomputable def p39Method2SourceSteps (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) :
    (k : ℕ) → k ≤ n → P39Matrix n n → P39Matrix n n
  | 0, _, X => X
  | k + 1, hk, X =>
      let j : Fin n := ⟨k, hk⟩
      p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
        (p39Method2SourceStep fp n L X j)

noncomputable def p39Method2SourceInverse (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) : P39Matrix n n :=
  p39Method2SourceSteps fp n L n (le_refl n) 0


noncomputable def p39Method2SourceUniformCoefficient
    (fp : P39FPModel) (n : ℕ) : ℝ :=
  p39Gamma fp.u n +
    (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n) +
    fp.u / (1 - fp.u)



/-- Method 2C's rounded off-diagonal product and right triangular solve. -/
noncomputable def p39Method2COffdiag
    (fp : P39FPModel) (r s : ℕ)
    (L11 : P39Matrix r r) (L21 : P39Matrix s r)
    (X22 : P39Matrix s s) : P39Matrix s r :=
  let Bhat := p39RoundedMatMul fp X22 L21
  fun i j => p39BackSub fp r L11.transpose (fun k => -Bhat i k) j


/-- The trailing rows of one block column. -/
def p39_block_tail {k : ℕ} {d : Fin k → ℕ}
    (X : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) (j : Fin k)
    (e : Fin (Fintype.card (P39SuffixIndex d j)) ≃ P39SuffixIndex d j) :
    P39Matrix (Fintype.card (P39SuffixIndex d j)) (d j) :=
  fun q b => X (p39_suffix_embed (e q)) (Sigma.mk j b)


/-- Source-order Method 2C on an arbitrary block partition. -/
def P39BlockLower {k : ℕ} {d : Fin k → ℕ}
    (M : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) : Prop :=
  ∀ a b, a.1 < b.1 → M a b = 0

def p39Method2CActualOutput
    (fp : P39FPModel) {k : ℕ} (d : Fin k → ℕ)
    (L X : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) : Prop :=
  P39BlockLower X ∧
    ∀ j : Fin k,
      p39_block_diag X j =
        p39Method2SourceInverse fp (d j) (p39_block_diag L j) ∧
      p39_block_tail X j (p39_suffix_order_equiv j) =
        p39Method2COffdiag fp (d j) (Fintype.card (P39SuffixIndex d j))
          (p39_block_diag L j)
          (p39_block_cross L j (p39_suffix_order_equiv j))
          (p39_block_suffix X j (p39_suffix_order_equiv j))


noncomputable def p39Method2CActualColumn
    (fp : P39FPModel) {k : ℕ} (d : Fin k → ℕ)
    (L : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ)
    (j : Fin k) : P39BlockIndex d → Fin (d j) → ℝ :=
  (measure (fun t : Fin k => k - t.val)).wf.fix
    (C := fun t => P39BlockIndex d → Fin (d t) → ℝ)
    (fun t rec a b =>
      if h : a.1 = t then
        p39Method2SourceInverse fp (d t) (p39_block_diag L t) (h ▸ a.2) b
      else if hlt : t < a.1 then
        let e := p39_suffix_order_equiv (d := d) t
        let q := e.symm (Sigma.mk (⟨a.1, hlt⟩ : {s : Fin k // t < s}) a.2)
        let X22 : P39Matrix (Fintype.card (P39SuffixIndex d t))
            (Fintype.card (P39SuffixIndex d t)) :=
          fun q' r =>
            rec (e r).1.val (by
              change k - (e r).1.val.val < k - t.val
              have htr := (e r).1.property
              omega)
              (p39_suffix_embed (e q')) (e r).2
        p39Method2COffdiag fp (d t) (Fintype.card (P39SuffixIndex d t))
          (p39_block_diag L t) (p39_block_cross L t e) X22 q b
      else 0) j

noncomputable def p39Method2CActualGlobalInverse
    (fp : P39FPModel) {k : ℕ} (d : Fin k → ℕ)
    (L : Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ) :
    Matrix (P39BlockIndex d) (P39BlockIndex d) ℝ :=
  fun a b => p39Method2CActualColumn fp d L b.1 a b.2


end VSCLReuse

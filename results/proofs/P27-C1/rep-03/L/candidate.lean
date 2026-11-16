import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open Matrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace VSCLReuse

private lemma p27_mul_shift {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℂ)
    (i : Fin m) (j : Fin p) :
    (X * p27Shift p) i j =
      if 0 < j.val then X i ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩ else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : 0 < j.val
  · simp only [if_pos hj]
    let t : Fin p := ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩
    have ht : j.val = t.val + 1 := by
      dsimp [t]
      omega
    have hs : (∑ x : Fin p, X i x * p27Shift p x j) = X i t := by
      rw [Finset.sum_eq_single t]
      · simp [p27Shift, ht]
      · intro b hb hbt
        have hne : j.val ≠ b.val + 1 := by
          intro he
          apply hbt
          apply Fin.ext
          dsimp [t]
          omega
        simp [p27Shift, hne]
      · simp
    simpa [t] using hs
  · simp only [if_neg hj]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : j.val ≠ b.val + 1 := by omega
    simp [p27Shift, hne]

private lemma p27_mul_shift_pow {m p : ℕ} (X : Matrix (Fin m) (Fin p) ℂ)
    (q : ℕ) (i : Fin m) (j : Fin p) :
    (X * (p27Shift p) ^ q) i j =
      if q ≤ j.val then
        X i ⟨j.val - q, (Nat.sub_le _ _).trans_lt j.isLt⟩
      else 0 := by
  classical
  induction q generalizing j with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, ← Matrix.mul_assoc, p27_mul_shift]
      by_cases hj : 0 < j.val
      · simp only [if_pos hj]
        let t : Fin p := ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩
        have ht : t.val = j.val - 1 := rfl
        rw [ih t]
        by_cases hq : q + 1 ≤ j.val
        · have hqt : q ≤ t.val := by dsimp [t]; omega
          simp only [if_pos hq, if_pos hqt]
          congr 1
          apply Fin.ext
          dsimp [t]
          omega
        · have hqt : ¬ q ≤ t.val := by dsimp [t]; omega
          simp only [if_neg hq, if_neg hqt]
      · have hq : ¬ q + 1 ≤ j.val := by omega
        simp only [if_neg hq, if_neg hj]

private noncomputable def p27PowerUpper {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) : Matrix (Fin n) (Fin p) ℂ :=
  ∑ q ∈ Finset.range k, A ^ q * W * (p27Shift p) ^ (k - 1 - q)

private lemma p27PowerUpper_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    p27PowerUpper A W (k + 1) = A ^ k * W + p27PowerUpper A W k * p27Shift p := by
  classical
  simp only [p27PowerUpper, Finset.sum_range_succ]
  have hterm : ∀ q ∈ Finset.range k,
      A ^ q * W * p27Shift p ^ (k + 1 - 1 - q) =
        (A ^ q * W * p27Shift p ^ (k - 1 - q)) * p27Shift p := by
    intro q hq
    have hqk : q < k := Finset.mem_range.mp hq
    have he : k + 1 - 1 - q = (k - 1 - q) + 1 := by omega
    rw [he, pow_succ]
    simp only [← Matrix.mul_assoc]
  rw [Finset.sum_congr rfl hterm]
  have hlast : k + 1 - 1 - k = 0 := by omega
  rw [hlast]
  simp only [pow_zero, Matrix.mul_one, Matrix.sum_mul]
  abel

private lemma p27Augmented_pow {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    (p27Augmented A W) ^ k =
      Matrix.fromBlocks (A ^ k) (p27PowerUpper A W k) 0 ((p27Shift p) ^ k) := by
  classical
  induction k with
  | zero => simp [p27Augmented, p27PowerUpper, ← Matrix.fromBlocks_one]
  | succ k ih =>
      rw [pow_succ, ih, p27Augmented, Matrix.fromBlocks_multiply]
      simp [p27PowerUpper_succ, pow_succ]

private lemma p27Phi_summable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : ℕ) (A : Matrix ι ι ℂ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • A ^ k) := by
  haveI : FiniteDimensional ℂ (Matrix ι ι ℂ) := Matrix.finiteDimensional
  letI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖A‖)
  intro k
  have hfac : (k.factorial : ℝ) ≤ ((k + ell).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right k ell)
  have hfacpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hfacpos' : (0 : ℝ) < ((k + ell).factorial : ℝ) := by positivity
  simp only [norm_smul, norm_inv, norm_natCast]
  calc
    ((k + ell).factorial : ℝ)⁻¹ * ‖A ^ k‖ ≤
        ((k + ell).factorial : ℝ)⁻¹ * ‖A‖ ^ k :=
      mul_le_mul_of_nonneg_left (norm_pow_le A k) (by positivity)
    _ ≤ (k.factorial : ℝ)⁻¹ * ‖A‖ ^ k :=
      mul_le_mul_of_nonneg_right ((inv_le_inv₀ hfacpos' hfacpos).mpr hfac)
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖A‖ ^ k / (k.factorial : ℝ) := by rw [div_eq_mul_inv, mul_comm]

private noncomputable def p27ColumnAt {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (j : Fin p) (r : ℕ) : Fin n → ℂ :=
  fun i => W i ⟨j.val - r, (Nat.sub_le _ _).trans_lt j.isLt⟩

private lemma p27PowerUpper_entry {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) (i : Fin n) (j : Fin p) :
    (p27PowerUpper A W k) i j =
      ∑ r ∈ Finset.range k,
        if r ≤ j.val then (Matrix.mulVec (A ^ (k - 1 - r)) (p27ColumnAt W j r)) i
        else 0 := by
  classical
  let f : ℕ → ℂ := fun r =>
    if r ≤ j.val then (Matrix.mulVec (A ^ (k - 1 - r)) (p27ColumnAt W j r)) i
    else 0
  calc
    (p27PowerUpper A W k) i j =
        ∑ q ∈ Finset.range k, (A ^ q * W * p27Shift p ^ (k - 1 - q)) i j := by
      simp only [p27PowerUpper, Matrix.sum_apply]
    _ = ∑ q ∈ Finset.range k, f (k - 1 - q) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqk : q < k := Finset.mem_range.mp hq
      have he : k - 1 - (k - 1 - q) = q := by omega
      rw [p27_mul_shift_pow]
      by_cases hr : k - 1 - q ≤ j.val
      · simp only [f, if_pos hr, he]
        rfl
      · simp only [f, if_neg hr]
    _ = ∑ r ∈ Finset.range k, f r := Finset.sum_range_reflect f k
    _ = _ := rfl

private lemma p27_sum_range_swap (k m : ℕ) (f : ℕ → ℂ) :
    (∑ r ∈ Finset.range k, if r < m then f r else 0) =
      ∑ r ∈ Finset.range m, if r < k then f r else 0 := by
  classical
  simp only [← Finset.sum_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range]
  tauto

private lemma p27_entry_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (ell : ℕ) (A : Matrix ι ι ℂ) (i j : ι) :
    Summable (fun q : ℕ => (((Nat.factorial (q + ell) : ℂ)⁻¹) • A ^ q) i j) := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intro M N; rfl
      map_smul' := by intro c M; rfl }
  haveI : FiniteDimensional ℂ (Matrix ι ι ℂ) := Matrix.finiteDimensional
  have h := ((p27Phi_summable ell A).hasSum.map e
    e.continuous_of_finiteDimensional).summable
  simpa [e] using h

private lemma p27Phi_entry_tsum {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (ell : ℕ) (A : Matrix ι ι ℂ) (i j : ι) :
    p27Phi ell A i j =
      ∑' q : ℕ, (((Nat.factorial (q + ell) : ℂ)⁻¹) • A ^ q) i j := by
  let e : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intro M N; rfl
      map_smul' := by intro c M; rfl }
  haveI : FiniteDimensional ℂ (Matrix ι ι ℂ) := Matrix.finiteDimensional
  have h := ((p27Phi_summable ell A).hasSum.map e
    e.continuous_of_finiteDimensional).tsum_eq
  simpa [e, p27Phi] using h.symm

private lemma p27_mulVec_summable {n : ℕ} [Nonempty (Fin n)]
    (ell : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    Summable (fun q : ℕ => (Nat.factorial (q + ell) : ℂ)⁻¹ *
      (Matrix.mulVec (A ^ q) v) i) := by
  classical
  have hentry (l : Fin n) :
      Summable (fun q : ℕ => ((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i l) :=
    p27_entry_summable ell A i l
  have hs : Summable (fun q : ℕ =>
      ∑ l : Fin n, (((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i l) * v l) := by
    apply summable_sum
    intro l hl
    exact (hentry l).mul_right (v l)
  refine hs.congr (fun q => ?_)
  simp only [Matrix.mulVec, dotProduct, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

private lemma p27Phi_mulVec_entry {n : ℕ} [Nonempty (Fin n)]
    (ell : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    (Matrix.mulVec (p27Phi ell A) v) i =
      ∑' q : ℕ, (Nat.factorial (q + ell) : ℂ)⁻¹ *
        (Matrix.mulVec (A ^ q) v) i := by
  classical
  have hentry (l : Fin n) :
      Summable (fun q : ℕ => ((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i l) :=
    p27_entry_summable ell A i l
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [p27Phi_entry_tsum ell A i]
  calc
    (∑ x : Fin n, (∑' q : ℕ, ((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i x) * v x)
        = ∑ x : Fin n, ∑' q : ℕ,
            (((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i x) * v x := by
          simp_rw [tsum_mul_right]
    _ = ∑' q : ℕ, ∑ x : Fin n,
          (((Nat.factorial (q + ell) : ℂ)⁻¹ • A ^ q) i x) * v x := by
          symm
          apply Summable.tsum_finsetSum
          intro x hx
          exact (hentry x).mul_right (v x)
    _ = _ := by
          apply tsum_congr
          intro q
          simp only [smul_apply, smul_eq_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring

private lemma p27_scale_power_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (τ : ℂ) (i : Fin n) (k r : ℕ) (hr : r < k) :
    τ ^ k * (Matrix.mulVec (A ^ (k - 1 - r)) v) i =
      τ ^ (r + 1) *
        (Matrix.mulVec ((τ • A) ^ (k - 1 - r)) v) i := by
  have hpow : τ ^ k = τ ^ (r + 1) * τ ^ (k - 1 - r) := by
    rw [← pow_add]
    congr 1
    omega
  have hmat : (Matrix.mulVec ((τ • A) ^ (k - 1 - r)) v) i =
      τ ^ (k - 1 - r) * (Matrix.mulVec (A ^ (k - 1 - r)) v) i := by
    rw [smul_pow, Matrix.smul_mulVec]
    rfl
  rw [hpow, hmat]
  ring

private lemma p27_augmented_power_entry {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) (i : Fin n) (j : Fin p) :
    ((τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j) =
      ∑ r : Fin (j.val + 1),
        if r.val < k then τ ^ (r.val + 1) *
          (Matrix.mulVec ((τ • A) ^ (k - 1 - r.val))
            (p27ColumnAt W j r.val)) i else 0 := by
  classical
  rw [smul_pow, p27Augmented_pow]
  simp only [smul_apply, smul_eq_mul, Matrix.fromBlocks_apply₁₂,
    p27PowerUpper_entry]
  rw [Finset.mul_sum]
  simp_rw [mul_ite, mul_zero]
  have hswap := p27_sum_range_swap k (j.val + 1)
    (fun r => τ ^ k * (Matrix.mulVec (A ^ (k - 1 - r)) (p27ColumnAt W j r)) i)
  simp only [Nat.lt_succ_iff] at hswap
  rw [hswap]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : r.val < k
  · simp only [if_pos h]
    exact p27_scale_power_mulVec A (p27ColumnAt W j r.val) τ i k r.val h
  · simp only [if_neg h]

private noncomputable def p27ColumnTerm {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n)
    (r : Fin (j.val + 1)) (k : ℕ) : ℂ :=
  if r.val < k then
    (Nat.factorial (k + ell) : ℂ)⁻¹ *
      (τ ^ (r.val + 1) *
        (Matrix.mulVec ((τ • A) ^ (k - 1 - r.val))
          (p27ColumnAt W j r.val)) i)
  else 0

private lemma p27ColumnTerm_summable {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n)
    (r : Fin (j.val + 1)) :
    Summable (p27ColumnTerm A W τ ell j i r) := by
  let v := p27ColumnAt W j r.val
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hbase := p27_mulVec_summable (ell + r.val + 1) (τ • A) v i
  have hshift : Summable (fun q : ℕ =>
      p27ColumnTerm A W τ ell j i r (q + (r.val + 1))) := by
    convert hbase.mul_left (τ ^ (r.val + 1)) using 1
    funext q
    have hlt : r.val < q + (r.val + 1) := by omega
    have hexp : q + (r.val + 1) - 1 - r.val = q := by omega
    have hfac : q + (r.val + 1) + ell = q + (ell + r.val + 1) := by omega
    simp only [p27ColumnTerm, if_pos hlt, hexp, hfac, v]
    ring
  exact (summable_nat_add_iff (r.val + 1)).mp hshift

private lemma p27ColumnTerm_tsum {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n)
    (r : Fin (j.val + 1)) :
    (∑' k : ℕ, p27ColumnTerm A W τ ell j i r k) =
      τ ^ (r.val + 1) *
        (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
          (p27ReverseColumn W j r)) i := by
  let v := p27ColumnAt W j r.val
  haveI : Nonempty (Fin n) := ⟨i⟩
  have hsum := (p27ColumnTerm_summable A W τ ell j i r).sum_add_tsum_nat_add
    (r.val + 1)
  have hzero : ∑ k ∈ Finset.range (r.val + 1),
      p27ColumnTerm A W τ ell j i r k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hle : k ≤ r.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp [p27ColumnTerm, Nat.not_lt.mpr hle]
  rw [hzero, zero_add] at hsum
  rw [← hsum]
  rw [p27Phi_mulVec_entry]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  have hlt : r.val < q + (r.val + 1) := by omega
  have hexp : q + (r.val + 1) - 1 - r.val = q := by omega
  have hfac : q + (r.val + 1) + ell = q + (ell + r.val + 1) := by omega
  simp only [p27ColumnTerm, if_pos hlt, hexp, hfac]
  have hv : p27ColumnAt W j r.val = p27ReverseColumn W j r := rfl
  rw [hv]
  ring

/-- P27-C1: the augmented-matrix phi-function column identity of Theorem 2.1. -/
theorem p27_c1_augmented_phi_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      ∑ r : Fin (j.val + 1),
        τ ^ (r.val + 1) *
          (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
            (p27ReverseColumn W j r)) i := by
  -- PROOF_START P27-C1-H001
  classical
  haveI : Nonempty (Fin n ⊕ Fin p) := ⟨Sum.inl i⟩
  rw [p27Phi_entry_tsum ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j)]
  calc
    (∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) •
        (τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j)) =
        ∑' k : ℕ, ∑ r : Fin (j.val + 1), p27ColumnTerm A W τ ell j i r k := by
      apply tsum_congr
      intro k
      simp only [smul_apply, smul_eq_mul, p27_augmented_power_entry,
        Finset.mul_sum, mul_ite, mul_zero, p27ColumnTerm]
    _ = ∑ r : Fin (j.val + 1),
          ∑' k : ℕ, p27ColumnTerm A W τ ell j i r k := by
      apply Summable.tsum_finsetSum
      intro r hr
      exact p27ColumnTerm_summable A W τ ell j i r
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact p27ColumnTerm_tsum A W τ ell j i r

end VSCLReuse

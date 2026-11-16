import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open scoped Matrix.Norms.Frobenius
open Matrix

set_option maxHeartbeats 2000000

namespace VSCLReuse

private lemma mul_p27Shift_apply {n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℂ) (i : Fin n) (j : Fin p) :
    (M * p27Shift p) i j =
      if hj : j.val = 0 then 0 else
        M i ⟨j.val - 1, by omega⟩ := by
  classical
  by_cases hj : j.val = 0
  · simp [Matrix.mul_apply, p27Shift, hj]
  · simp only [Matrix.mul_apply, p27Shift, dif_neg hj]
    let t : Fin p := ⟨j.val - 1, by omega⟩
    have ht : j.val = t.val + 1 := by dsimp [t]; omega
    rw [Finset.sum_eq_single t]
    · simp only [if_pos ht, mul_one]
      rfl
    · intro b _ hb
      have hne : j.val ≠ b.val + 1 := by
        intro h
        apply hb
        apply Fin.ext
        dsimp [t]
        omega
      simp [hne]
    · intro h; exact (h (Finset.mem_univ t)).elim

private noncomputable def p27UpperPower {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) : Matrix (Fin n) (Fin p) ℂ :=
  ∑ r ∈ Finset.range k, A ^ (k - 1 - r) * W * (p27Shift p) ^ r

private lemma p27UpperPower_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    p27UpperPower A W (k + 1) = A ^ k * W + p27UpperPower A W k * p27Shift p := by
  classical
  unfold p27UpperPower
  rw [Finset.sum_range_succ', Matrix.sum_mul]
  simp only [pow_zero, Matrix.mul_one]
  have he0 : k + 1 - 1 - 0 = k := by omega
  rw [he0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have he : k + 1 - 1 - (r + 1) = k - 1 - r := by omega
  simp only [he, pow_succ]
  simp only [Matrix.mul_assoc]

private lemma p27Augmented_pow {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    (p27Augmented A W) ^ k =
      Matrix.fromBlocks (A ^ k) (p27UpperPower A W k) 0 ((p27Shift p) ^ k) := by
  classical
  induction k with
  | zero =>
      simp [p27UpperPower, Matrix.fromBlocks_one]
  | succ k ih =>
      rw [pow_succ, ih, p27Augmented, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ]
      rw [p27UpperPower_succ]

private lemma p27Shift_pow_column {n p : ℕ}
    (M : Matrix (Fin n) (Fin p) ℂ) (k : ℕ) (i : Fin n) (j : Fin p) :
    (M * (p27Shift p) ^ k) i j =
      if h : k ≤ j.val then M i ⟨j.val - k, by omega⟩ else 0 := by
  classical
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, mul_p27Shift_apply]
      by_cases hj : j.val = 0
      · simp [hj]
      · simp only [dif_neg hj]
        let t : Fin p := ⟨j.val - 1, by omega⟩
        change (M * p27Shift p ^ k) i t = _
        rw [ih]
        by_cases hk : k + 1 ≤ j.val
        · have hkt : k ≤ t.val := by dsimp [t]; omega
          simp only [dif_pos hk, dif_pos hkt]
          congr 1
          apply Fin.ext
          dsimp [t]
          omega
        · have hkt : ¬ k ≤ t.val := by dsimp [t]; omega
          simp only [dif_neg hk, dif_neg hkt]

private lemma p27UpperPower_term {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k r : ℕ) (i : Fin n) (j : Fin p) :
    (A ^ (k - 1 - r) * W * (p27Shift p) ^ r) i j =
      if h : r ≤ j.val then
        ((A ^ (k - 1 - r)) *ᵥ
          p27ReverseColumn W j ⟨r, by omega⟩) i else 0 := by
  classical
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  by_cases h : r ≤ j.val
  · simp only [dif_pos h]
    simp_rw [p27Shift_pow_column W r]
    simp only [dif_pos h]
    rfl
  · simp only [dif_neg h]
    simp_rw [p27Shift_pow_column W r]
    simp [h]

private lemma p27_sum_range_if_swap (f : ℕ → ℂ) (k j : ℕ) :
    (∑ r ∈ Finset.range k, if r ≤ j then f r else 0) =
      ∑ r ∈ Finset.range (j + 1), if r < k then f r else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro r hr
    rfl

private lemma p27UpperPower_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) (i : Fin n) (j : Fin p) :
    (p27UpperPower A W k) i j =
      ∑ r : Fin (j.val + 1),
        if r.val < k then
          ((A ^ (k - 1 - r.val)) *ᵥ p27ReverseColumn W j r) i else 0 := by
  classical
  unfold p27UpperPower
  rw [Matrix.sum_apply]
  simp_rw [p27UpperPower_term A W k]
  let f : ℕ → ℂ := fun r =>
    if h : r ≤ j.val then
      ((A ^ (k - 1 - r)) *ᵥ p27ReverseColumn W j ⟨r, by omega⟩) i else 0
  change (∑ r ∈ Finset.range k, f r) = _
  calc
    (∑ r ∈ Finset.range k, f r) =
        ∑ r ∈ Finset.range k, if r ≤ j.val then f r else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          by_cases h : r ≤ j.val <;> simp [f, h]
    _ = ∑ r ∈ Finset.range (j.val + 1), if r < k then f r else 0 :=
      p27_sum_range_if_swap f k j.val
    _ = ∑ r : Fin (j.val + 1), if r.val < k then f r.val else 0 := by
      exact (Fin.sum_univ_eq_sum_range (fun r => if r < k then f r else 0)
        (j.val + 1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r.val ≤ j.val := by omega
      simp only [f, dif_pos hrj]

private lemma p27Phi_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) := by
  letI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have hmajor : Summable (fun k : ℕ =>
      ‖((Nat.factorial k : ℂ)⁻¹) • B ^ k‖) :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) B
  apply @Summable.of_norm_bounded ℕ (Matrix ι ι ℂ) inferInstance
    (FiniteDimensional.complete ℂ _) _ _ hmajor
  intro k
  simp only [norm_smul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_right
  · apply inv_anti₀
    · exact_mod_cast Nat.factorial_pos k
    · exact_mod_cast Nat.factorial_le (Nat.le_add_right k ell)
  · exact norm_nonneg _

private lemma p27Phi_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (i j : ι) :
    p27Phi ell B i j =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j := by
  letI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  let f : ℕ → Matrix ι ι ℂ :=
    fun k => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k
  have hf : Summable f := p27Phi_summable ell B
  have hrow : Summable (fun k => f k i) :=
    hf.map (ContinuousLinearMap.proj (R := ℂ) i)
      (ContinuousLinearMap.proj (R := ℂ) i).continuous
  change (∑' k, f k) i j = _
  have h1 := (ContinuousLinearMap.proj (R := ℂ) i).map_tsum hf
  have h2 := (ContinuousLinearMap.proj (R := ℂ) j).map_tsum hrow
  change (∑' k, f k) i = ∑' k, f k i at h1
  change (∑' k, f k i) j = ∑' k, f k i j at h2
  rw [h1, h2]
  rfl

private noncomputable def p27_mulVecEvalCLM {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (i : ι) : Matrix ι ι ℂ →L[ℂ] ℂ :=
  ({ toFun := fun M : Matrix ι ι ℂ => (M *ᵥ v) i
     map_add' := by intro M N; simp [Matrix.add_mulVec]
     map_smul' := by intro c M; simp [Matrix.smul_mulVec] } :
    Matrix ι ι ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap

private lemma p27_mulVecEvalCLM_apply {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (i : ι) (M : Matrix ι ι ℂ) :
    (p27_mulVecEvalCLM v i) M = (M *ᵥ v) i := by
  unfold p27_mulVecEvalCLM
  rfl

private lemma p27Phi_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι) :
    (p27Phi ell B *ᵥ v) i =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * ((B ^ k *ᵥ v) i) := by
  letI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have h := p27Phi_summable ell B
  have hm := (p27_mulVecEvalCLM v i).map_tsum h
  unfold p27Phi
  change (p27_mulVecEvalCLM v i)
    (∑' k, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) = _
  rw [hm]
  apply tsum_congr
  intro k
  simp [p27_mulVecEvalCLM_apply]

private lemma p27Phi_mulVec_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι) :
    Summable (fun k : ℕ =>
      ((Nat.factorial (k + ell) : ℂ)⁻¹) * ((B ^ k *ᵥ v) i)) := by
  letI : CompleteSpace (Matrix ι ι ℂ) := FiniteDimensional.complete ℂ _
  have h := (p27Phi_summable ell B).map (p27_mulVecEvalCLM v i)
    (p27_mulVecEvalCLM v i).continuous
  apply h.congr
  intro k
  simp [p27_mulVecEvalCLM_apply]

private lemma p27_shift_summable (f : ℕ → ℂ) (r : ℕ) (hf : Summable f) :
    Summable (fun k : ℕ => if r < k then f (k - r - 1) else 0) := by
  apply (summable_nat_add_iff (r + 1)).mp
  convert hf using 1
  ext q
  have h : r < q + (r + 1) := by omega
  simp [h, show q + (r + 1) - r - 1 = q by omega]

private lemma p27_tsum_shift (f : ℕ → ℂ) (r : ℕ) (hf : Summable f) :
    (∑' k : ℕ, if r < k then f (k - r - 1) else 0) = ∑' q : ℕ, f q := by
  let g : ℕ → ℂ := fun k => if r < k then f (k - r - 1) else 0
  have hg : Summable g := p27_shift_summable f r hf
  have hzero : (∑ k ∈ Finset.range (r + 1), g k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkr : k ≤ r := by have := Finset.mem_range.mp hk; omega
    simp [g, show ¬ r < k by omega]
  have htail : ∀ q : ℕ, g (q + (r + 1)) = f q := by
    intro q
    simp [g, show r < q + (r + 1) by omega,
      show q + (r + 1) - r - 1 = q by omega]
  have hsplit := hg.sum_add_tsum_nat_add (r + 1)
  rw [hzero, zero_add] at hsplit
  calc
    (∑' k, g k) = ∑' q, g (q + (r + 1)) := hsplit.symm
    _ = ∑' q, f q := tsum_congr htail

private lemma p27_augmented_power_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) (i : Fin n) (j : Fin p) :
    ((τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j) =
      ∑ r : Fin (j.val + 1),
        if r.val < k then
          τ ^ k * ((A ^ (k - 1 - r.val) *ᵥ p27ReverseColumn W j r) i) else 0 := by
  classical
  rw [smul_pow, Matrix.smul_apply, p27Augmented_pow,
    Matrix.fromBlocks_apply₁₂, p27UpperPower_column]
  simp only [smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp

private lemma p27_tail_term {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell r q : ℕ)
    (v : Fin n → ℂ) (i : Fin n) :
    ((Nat.factorial (q + ell + r + 1) : ℂ)⁻¹) * τ ^ (q + r + 1) *
        ((A ^ q *ᵥ v) i) =
      τ ^ (r + 1) *
        (((Nat.factorial (q + (ell + r + 1)) : ℂ)⁻¹) *
          (((τ • A) ^ q *ᵥ v) i)) := by
  have hfac : q + ell + r + 1 = q + (ell + r + 1) := by omega
  have hpow : q + r + 1 = (r + 1) + q := by omega
  rw [hfac, hpow, pow_add, smul_pow, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma p27_tail_summable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell r : ℕ)
    (v : Fin n → ℂ) (i : Fin n) :
    Summable (fun q : ℕ =>
      ((Nat.factorial (q + ell + r + 1) : ℂ)⁻¹) * τ ^ (q + r + 1) *
        ((A ^ q *ᵥ v) i)) := by
  have h := (p27Phi_mulVec_summable (ell + r + 1) (τ • A) v i).mul_left
    (τ ^ (r + 1))
  apply h.congr
  intro q
  exact (p27_tail_term A τ ell r q v i).symm

private lemma p27_tail_tsum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell r : ℕ)
    (v : Fin n → ℂ) (i : Fin n) :
    (∑' q : ℕ,
      ((Nat.factorial (q + ell + r + 1) : ℂ)⁻¹) * τ ^ (q + r + 1) *
        ((A ^ q *ᵥ v) i)) =
      τ ^ (r + 1) * (p27Phi (ell + r + 1) (τ • A) *ᵥ v) i := by
  have h := p27Phi_mulVec_summable (ell + r + 1) (τ • A) v i
  calc
    _ = ∑' q : ℕ, τ ^ (r + 1) *
        (((Nat.factorial (q + (ell + r + 1)) : ℂ)⁻¹) *
          (((τ • A) ^ q *ᵥ v) i)) := by
          apply tsum_congr
          intro q
          exact p27_tail_term A τ ell r q v i
    _ = τ ^ (r + 1) * ∑' q : ℕ,
        (((Nat.factorial (q + (ell + r + 1)) : ℂ)⁻¹) *
          (((τ • A) ^ q *ᵥ v) i)) := h.tsum_mul_left _
    _ = _ := by rw [← p27Phi_mulVec_apply]

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
  let F : Fin (j.val + 1) → ℕ → ℂ := fun r q =>
    ((Nat.factorial (q + ell + r.val + 1) : ℂ)⁻¹) *
      τ ^ (q + r.val + 1) *
        ((A ^ q *ᵥ p27ReverseColumn W j r) i)
  let G : Fin (j.val + 1) → ℕ → ℂ := fun r k =>
    if r.val < k then F r (k - r.val - 1) else 0
  have hF (r : Fin (j.val + 1)) : Summable (F r) :=
    p27_tail_summable A τ ell r.val (p27ReverseColumn W j r) i
  have hG (r : Fin (j.val + 1)) : Summable (G r) :=
    p27_shift_summable (F r) r.val (hF r)
  have hterm (k : ℕ) :
      ((Nat.factorial (k + ell) : ℂ)⁻¹) *
          ((τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j) =
        ∑ r : Fin (j.val + 1), G r k := by
    rw [p27_augmented_power_column]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrk : r.val < k
    · have he : k - 1 - r.val = k - r.val - 1 := by omega
      have hfac : k - r.val - 1 + ell + r.val + 1 = k + ell := by omega
      have hpow : k - r.val - 1 + r.val + 1 = k := by omega
      simp only [G, F, if_pos hrk, he, hfac, hpow]
      ring
    · simp [G, F, hrk]
  rw [p27Phi_apply]
  calc
    (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) *
        ((τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j)) =
      ∑' k : ℕ, ∑ r : Fin (j.val + 1), G r k := tsum_congr hterm
    _ = ∑ r : Fin (j.val + 1), ∑' k : ℕ, G r k := by
      exact Summable.tsum_finsetSum (s := Finset.univ) (by
        intro r hr
        exact hG r)
    _ = ∑ r : Fin (j.val + 1), ∑' q : ℕ, F r q := by
      apply Finset.sum_congr rfl
      intro r hr
      exact p27_tsum_shift (F r) r.val (hF r)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact p27_tail_tsum A τ ell r.val (p27ReverseColumn W j r) i

end VSCLReuse

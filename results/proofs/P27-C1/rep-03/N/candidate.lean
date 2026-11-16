import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open Matrix

namespace VSCLReuse

private lemma p27_mul_shift_zero {n p : ℕ}
    (M : Matrix (Fin n) (Fin (p + 1)) ℂ) (i : Fin n) :
    (M * p27Shift (p + 1)) i 0 = 0 := by
  classical
  simp [Matrix.mul_apply, p27Shift]

private lemma p27_mul_shift_succ {n p : ℕ}
    (M : Matrix (Fin n) (Fin (p + 1)) ℂ) (i : Fin n) (j : Fin p) :
    (M * p27Shift (p + 1)) i j.succ = M i j.castSucc := by
  classical
  simp only [Matrix.mul_apply, p27Shift, Fin.val_succ, mul_ite, mul_one, mul_zero]
  have h (x : Fin (p + 1)) : (j.val + 1 = x.val + 1) ↔ x = j.castSucc := by
    simp [Fin.ext_iff, eq_comm]
  simp_rw [h]
  simp

private noncomputable def p27UpperPower {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) : Matrix (Fin n) (Fin p) ℂ :=
  fun i j => ∑ r : Fin (j.val + 1),
    if r.val < k then (A ^ (k - 1 - r.val) *ᵥ p27ReverseColumn W j r) i else 0

private lemma p27UpperPower_zero {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ) :
    p27UpperPower A W 0 = 0 := by
  ext i j
  simp [p27UpperPower]

private lemma p27UpperPower_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    p27UpperPower A W (k + 1) = A ^ k * W + p27UpperPower A W k * p27Shift p := by
  classical
  cases p with
  | zero =>
      ext i j
      exact j.elim0
  | succ p =>
      ext i j
      induction j using Fin.cases with
      | zero =>
          simp only [Matrix.add_apply]
          rw [p27_mul_shift_zero, add_zero]
          have hcol : p27ReverseColumn W 0 0 = fun a => W a 0 := by
            funext a
            apply congrArg (W a)
            apply Fin.ext
            simp
          simp [p27UpperPower, Matrix.mul_apply, mulVec, dotProduct]
          apply Finset.sum_congr rfl
          intro a ha
          exact congrArg ((A ^ k) i a * ·) (congrFun hcol a)
      | succ j =>
          simp only [Matrix.add_apply]
          rw [p27_mul_shift_succ]
          simp only [p27UpperPower, Matrix.mul_apply]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Nat.sub_zero,
            Fin.val_succ]
          have hcol0 : p27ReverseColumn W j.succ 0 = fun a => W a j.succ := by
            funext a
            apply congrArg (W a)
            apply Fin.ext
            simp
          have hcol (r : Fin (j.val + 1)) :
              p27ReverseColumn W j.succ r.succ =
                p27ReverseColumn W j.castSucc r := by
            funext a
            unfold p27ReverseColumn
            apply congrArg (W a)
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          by_cases h : r.val < k
          · have h' : r.val + 1 < k + 1 := by omega
            simp only [h, h', ↓reduceIte]
            have he : k + 1 - 1 - (r.val + 1) = k - 1 - r.val := by omega
            rw [he]
            rw [hcol]
          · have h' : ¬ r.val + 1 < k + 1 := by omega
            simp [h, h']

private lemma p27_augmented_pow {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (k : ℕ) :
    (p27Augmented A W) ^ k =
      Matrix.fromBlocks (A ^ k) (p27UpperPower A W k) 0 ((p27Shift p) ^ k) := by
  induction k with
  | zero =>
      simp [p27UpperPower_zero, Matrix.fromBlocks_one]
  | succ k ih =>
      rw [pow_succ, ih]
      unfold p27Augmented
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        p27UpperPower_succ, pow_succ]

private lemma p27_matrix_pow_entry_bound {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (k : ℕ) (i j : m) :
    ‖(B ^ k) i j‖ ≤ (∑ a : m, ∑ b : m, ‖B a b‖) ^ k := by
  classical
  induction k generalizing i j with
  | zero =>
      by_cases h : i = j <;> simp [h]
  | succ k ih =>
      let C : ℝ := ∑ a : m, ∑ b : m, ‖B a b‖
      have hC : 0 ≤ C := by dsimp [C]; positivity
      have hcol : (∑ a : m, ‖B a j‖) ≤ C := by
        dsimp [C]
        apply Finset.sum_le_sum
        intro a ha
        exact Finset.single_le_sum (fun b hb => norm_nonneg (B a b)) (Finset.mem_univ j)
      rw [pow_succ, Matrix.mul_apply]
      calc
        ‖∑ a : m, (B ^ k) i a * B a j‖ ≤
            ∑ a : m, ‖(B ^ k) i a * B a j‖ := norm_sum_le _ _
        _ ≤ ∑ a : m, C ^ k * ‖B a j‖ := by
            apply Finset.sum_le_sum
            intro a ha
            rw [norm_mul]
            gcongr
            exact ih i a
        _ = C ^ k * ∑ a : m, ‖B a j‖ := by rw [Finset.mul_sum]
        _ ≤ C ^ k * C := by gcongr
        _ = C ^ (k + 1) := by rw [pow_succ]

private lemma p27_phi_series_summable {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (ell : ℕ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) := by
  classical
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  let C : ℝ := ∑ a : m, ∑ b : m, ‖B a b‖
  apply (Real.summable_pow_div_factorial C).of_norm_bounded
  intro k
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv,
    Complex.norm_natCast]
  calc
    (↑(k + ell).factorial : ℝ)⁻¹ * ‖(B ^ k) i j‖ ≤
        (↑k.factorial : ℝ)⁻¹ * C ^ k := by
      gcongr
      · exact Nat.le_add_right k ell
      · exact p27_matrix_pow_entry_bound B k i j
    _ = C ^ k / ↑k.factorial := by ring

private lemma p27_phi_entry {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m ℂ) (ell : ℕ) (i j : m) :
    p27Phi ell B i j =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j := by
  have hs := p27_phi_series_summable B ell
  have h1 : (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) i =
      ∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) i :=
    tsum_apply hs
  rw [p27Phi, h1]
  rw [tsum_apply ((Pi.summable.mp hs) i)]
  simp only [Matrix.smul_apply, smul_eq_mul]

private lemma p27_phi_mulVec_entry {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (ell : ℕ)
    (v : Fin m → ℂ) (i : Fin m) :
    (p27Phi ell B *ᵥ v) i =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * ((B ^ k *ᵥ v) i) := by
  classical
  have hs := p27_phi_series_summable B ell
  have hentry (a : Fin m) :
      Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) := by
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (Pi.summable.mp ((Pi.summable.mp hs) i)) a
  calc
    (p27Phi ell B *ᵥ v) i = ∑ a : Fin m, (p27Phi ell B) i a * v a := rfl
    _ = ∑ a : Fin m,
          (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) * v a := by
            simp_rw [p27_phi_entry]
    _ = ∑ a : Fin m, ∑' k : ℕ,
          ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a * v a := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [tsum_mul_right]
    _ = ∑' k : ℕ, ∑ a : Fin m,
          ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a * v a := by
            rw [Summable.tsum_finsetSum]
            intro a ha
            exact (hentry a).mul_right (v a)
    _ = ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * ((B ^ k *ᵥ v) i) := by
            apply tsum_congr
            intro k
            simp_rw [mul_assoc]
            rw [← Finset.mul_sum]
            rfl

private lemma p27_tsum_shift (d : ℕ) (f : ℕ → ℂ) :
    (∑' k : ℕ, if d ≤ k then f (k - d) else 0) = ∑' q : ℕ, f q := by
  classical
  apply tsum_eq_tsum_of_ne_zero_bij
    (i := fun q : ↥(Function.support f) => q.val + d)
  · intro q₁ q₂ h
    apply Subtype.ext
    simp only at h
    omega
  · intro k hk
    have hd : d ≤ k := by
      by_contra h
      have hz : (if d ≤ k then f (k - d) else 0) = 0 := by simp [h]
      exact hk hz
    have hq : k - d ∈ Function.support f := by
      intro hzero
      apply hk
      simp [hd, hzero]
    refine ⟨⟨k - d, hq⟩, ?_⟩
    simp [Nat.sub_add_cancel hd]
  · intro q
    simp

private lemma p27_shift_summable (d : ℕ) (f : ℕ → ℂ) (hf : Summable f) :
    Summable (fun k : ℕ => if d ≤ k then f (k - d) else 0) := by
  apply (summable_nat_add_iff d).mp
  simpa using hf

private lemma p27_phi_mulVec_series_summable {m : ℕ}
    (B : Matrix (Fin m) (Fin m) ℂ) (ell : ℕ)
    (v : Fin m → ℂ) (i : Fin m) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) * ((B ^ k *ᵥ v) i)) := by
  classical
  have hs := p27_phi_series_summable B ell
  have hentry (a : Fin m) :
      Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) := by
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (Pi.summable.mp ((Pi.summable.mp hs) i)) a
  have hsum : Summable (fun k : ℕ => ∑ a : Fin m,
      ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a * v a) := by
    apply summable_sum
    intro a ha
    exact (hentry a).mul_right (v a)
  apply hsum.congr
  intro k
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  rfl

private lemma p27_component_term {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell d : ℕ)
    (v : Fin n → ℂ) (i : Fin n) (k : ℕ) :
    ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if d ≤ k then (A ^ (k - d) *ᵥ v) i else 0) =
    if d ≤ k then τ ^ d *
      (((Nat.factorial (k - d + (ell + d)) : ℂ)⁻¹) *
        (((τ • A) ^ (k - d) *ᵥ v) i)) else 0 := by
  by_cases hk : d ≤ k
  · simp only [hk, ↓reduceIte]
    have hk₁ : k - d + (ell + d) = k + ell := by omega
    have hk₂ : k - d + d = k := Nat.sub_add_cancel hk
    have hpow : τ ^ k = τ ^ (k - d) * τ ^ d := by
      calc
        τ ^ k = τ ^ (k - d + d) := by rw [hk₂]
        _ = τ ^ (k - d) * τ ^ d := pow_add τ (k - d) d
    rw [hk₁, smul_pow, Matrix.smul_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hpow]
    ring
  · simp [hk]

private lemma p27_component_summable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell d : ℕ)
    (v : Fin n → ℂ) (i : Fin n) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if d ≤ k then (A ^ (k - d) *ᵥ v) i else 0)) := by
  let g : ℕ → ℂ := fun q => τ ^ d *
    (((Nat.factorial (q + (ell + d)) : ℂ)⁻¹) * (((τ • A) ^ q *ᵥ v) i))
  have hg : Summable g :=
    (p27_phi_mulVec_series_summable (τ • A) (ell + d) v i).mul_left (τ ^ d)
  have hshift := p27_shift_summable d g hg
  exact hshift.congr (fun k => (p27_component_term A τ ell d v i k).symm)

private lemma p27_component {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (τ : ℂ) (ell d : ℕ)
    (v : Fin n → ℂ) (i : Fin n) :
    (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if d ≤ k then (A ^ (k - d) *ᵥ v) i else 0)) =
      τ ^ d * (p27Phi (ell + d) (τ • A) *ᵥ v) i := by
  let g : ℕ → ℂ := fun q => τ ^ d *
    (((Nat.factorial (q + (ell + d)) : ℂ)⁻¹) * (((τ • A) ^ q *ᵥ v) i))
  have hterm (k : ℕ) :
      ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
        (if d ≤ k then (A ^ (k - d) *ᵥ v) i else 0) =
      if d ≤ k then g (k - d) else 0 := p27_component_term A τ ell d v i k
  calc
    (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if d ≤ k then (A ^ (k - d) *ᵥ v) i else 0)) =
        ∑' k : ℕ, if d ≤ k then g (k - d) else 0 := by
          apply tsum_congr hterm
    _ = ∑' q : ℕ, g q := p27_tsum_shift d g
    _ = τ ^ d * (p27Phi (ell + d) (τ • A) *ᵥ v) i := by
      rw [p27_phi_mulVec_entry]
      change (∑' q : ℕ, τ ^ d *
        (((Nat.factorial (q + (ell + d)) : ℂ)⁻¹) * (((τ • A) ^ q *ᵥ v) i))) =
          τ ^ d * (∑' q : ℕ,
            ((Nat.factorial (q + (ell + d)) : ℂ)⁻¹) * (((τ • A) ^ q *ᵥ v) i))
      exact tsum_mul_left

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
  let F : Fin (j.val + 1) → ℕ → ℂ := fun r k =>
    ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if r.val + 1 ≤ k then
        (A ^ (k - (r.val + 1)) *ᵥ p27ReverseColumn W j r) i else 0)
  have hpow (k : ℕ) :
      ((τ • p27Augmented A W) ^ k) (Sum.inl i) (Sum.inr j) =
        τ ^ k * (∑ r : Fin (j.val + 1),
          if r.val + 1 ≤ k then
            (A ^ (k - (r.val + 1)) *ᵥ p27ReverseColumn W j r) i else 0) := by
    rw [smul_pow, Matrix.smul_apply, p27_augmented_pow,
      Matrix.fromBlocks_apply₁₂]
    simp only [smul_eq_mul, p27UpperPower]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hiff : (r.val < k) ↔ (r.val + 1 ≤ k) := by omega
    by_cases h : r.val + 1 ≤ k
    · simp only [h, hiff.mpr h, ↓reduceIte]
      congr 1
      have he : k - 1 - r.val = k - (r.val + 1) := by omega
      rw [he]
    · simp [h, hiff]
  have hF (r : Fin (j.val + 1)) : Summable (F r) := by
    change Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) * τ ^ k *
      (if r.val + 1 ≤ k then
        (A ^ (k - (r.val + 1)) *ᵥ p27ReverseColumn W j r) i else 0))
    exact p27_component_summable A τ ell (r.val + 1) (p27ReverseColumn W j r) i
  calc
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
        ∑' k : ℕ, ∑ r : Fin (j.val + 1), F r k := by
      rw [p27_phi_entry]
      apply tsum_congr
      intro k
      rw [hpow]
      simp only [F, ← Finset.mul_sum, mul_assoc]
    _ = ∑ r : Fin (j.val + 1), ∑' k : ℕ, F r k :=
      Summable.tsum_finsetSum (fun r hr => hF r)
    _ = ∑ r : Fin (j.val + 1),
          τ ^ (r.val + 1) *
            (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
              (p27ReverseColumn W j r)) i := by
      apply Finset.sum_congr rfl
      intro r hr
      exact p27_component A τ ell (r.val + 1) (p27ReverseColumn W j r) i

end VSCLReuse

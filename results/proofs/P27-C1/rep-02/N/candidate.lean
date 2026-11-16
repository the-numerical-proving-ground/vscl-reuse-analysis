import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open Matrix

namespace VSCLReuse

private theorem p27Phi_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  letI : Nonempty ι := ⟨i⟩
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  refine Summable.of_norm_bounded
    (Real.summable_pow_div_factorial ‖B‖) ?_
  intro k
  change ‖((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j‖ ≤
    ‖B‖ ^ k / (↑k.factorial : ℝ)
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_comm, ← div_eq_mul_inv]
  have he : ‖(B ^ k) i j‖ ≤ ‖B ^ k‖ := by
    have hnn : ‖(B ^ k) i j‖₊ ≤ ‖B ^ k‖₊ := by
      rw [Matrix.linfty_opNNNorm_def]
      exact (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun i => ∑ j : ι, ‖(B ^ k) i j‖₊)
          (Finset.mem_univ i))
    exact_mod_cast hnn
  calc
    ‖(B ^ k) i j‖ / (↑(k + ell).factorial : ℝ) ≤
        ‖B ^ k‖ / (↑(k + ell).factorial : ℝ) := by
      gcongr
    _ ≤ ‖B‖ ^ k / (↑(k + ell).factorial : ℝ) := by
      gcongr
      exact norm_pow_le _ _
    _ ≤ ‖B‖ ^ k / (↑k.factorial : ℝ) := by
      gcongr
      exact Nat.le_add_right k ell

private theorem p27Phi_recur {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    p27Phi ell B =
      ((Nat.factorial ell : ℂ)⁻¹) • (1 : Matrix ι ι ℂ) +
        p27Phi (ell + 1) B * B := by
  unfold p27Phi
  have h := (p27Phi_summable ell B).sum_add_tsum_nat_add 1
  have hh : (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) =
      ∑ k ∈ Finset.range 1, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k +
        ∑' k : ℕ, ((Nat.factorial (k + 1 + ell) : ℂ)⁻¹) • B ^ (k + 1) := h.symm
  rw [hh]
  simp only [Finset.sum_range_one, zero_add, pow_zero]
  congr 1
  rw [← (p27Phi_summable (ell + 1) B).tsum_mul_right B]
  apply tsum_congr
  intro k
  rw [pow_succ]
  simp only [smul_mul_assoc]
  simp [Nat.add_left_comm, Nat.add_comm]

private theorem p27Augmented_smul_blocks {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) :
    τ • p27Augmented A W =
      Matrix.fromBlocks (τ • A) (τ • W) 0 (τ • p27Shift p) := by
  simp [p27Augmented, Matrix.fromBlocks_smul]

private theorem p27Augmented_pow_blocks {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) :
    ∃ U : Matrix (Fin n) (Fin p) ℂ, ∃ D : Matrix (Fin p) (Fin p) ℂ,
      (τ • p27Augmented A W) ^ k =
        Matrix.fromBlocks ((τ • A) ^ k) U 0 D := by
  induction k with
  | zero =>
      refine ⟨0, 1, ?_⟩
      simp only [pow_zero]
      exact Matrix.fromBlocks_one.symm
  | succ k ih =>
      obtain ⟨U, D, h⟩ := ih
      refine ⟨(τ • A) ^ k * (τ • W) + U * (τ • p27Shift p),
        D * (τ • p27Shift p), ?_⟩
      rw [pow_succ, h, p27Augmented_smul_blocks, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, ← pow_succ]

private theorem p27Phi_augmented_left {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i a : Fin n) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inl a) =
      p27Phi ell (τ • A) i a := by
  let B := τ • p27Augmented A W
  have hB := p27Phi_summable ell B
  have hA := p27Phi_summable ell (τ • A)
  have hBi := (Pi.summable.mp hB) (Sum.inl i)
  have hAi := (Pi.summable.mp hA) i
  unfold p27Phi
  change (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k)
      (Sum.inl i) (Sum.inl a) =
    (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • (τ • A) ^ k) i a
  calc
    _ = (∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) (Sum.inl i))
          (Sum.inl a) := congrArg (fun f => f (Sum.inl a)) (tsum_apply hB)
    _ = ∑' k : ℕ,
          (((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) (Sum.inl i) (Sum.inl a) :=
      tsum_apply hBi
    _ = ∑' k : ℕ,
          (((Nat.factorial (k + ell) : ℂ)⁻¹) • (τ • A) ^ k) i a := by
      apply tsum_congr
      intro k
      obtain ⟨U, D, hk⟩ := p27Augmented_pow_blocks A W τ k
      simp [B, hk]
    _ = (∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) • (τ • A) ^ k) i) a :=
      (tsum_apply hAi).symm
    _ = _ := congrArg (fun f => f a) (tsum_apply hA).symm

private theorem p27Shift_column_sum {p : ℕ} (v : Fin p → ℂ)
    (τ : ℂ) (j : Fin p) :
    (∑ b : Fin p, v b * (τ • p27Shift p) b j) =
      if j.val = 0 then 0 else
        τ * v ⟨j.val - 1, (Nat.sub_le j.val 1).trans_lt j.isLt⟩ := by
  by_cases hj : j.val = 0
  · simp [hj, p27Shift]
  · let b0 : Fin p :=
      ⟨j.val - 1, (Nat.sub_le j.val 1).trans_lt j.isLt⟩
    have hb0 : j.val = b0.val + 1 := by
      dsimp [b0]
      omega
    have hterm (b : Fin p) :
        v b * (τ • p27Shift p) b j =
          if b = b0 then τ * v b0 else 0 := by
      by_cases hb : b = b0
      · subst b
        simp [p27Shift, hb0, mul_comm]
      · have hn : j.val ≠ b.val + 1 := by
          intro h
          apply hb
          apply Fin.ext
          dsimp [b0]
          omega
        simp [p27Shift, hn, hb]
    simp_rw [hterm]
    simp [hj, b0]

private theorem p27Phi_augmented_recur {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A)) (fun a => W a j)) i +
        if j.val = 0 then 0 else
          τ * p27Phi (ell + 1) (τ • p27Augmented A W)
            (Sum.inl i)
            (Sum.inr ⟨j.val - 1, (Nat.sub_le j.val 1).trans_lt j.isLt⟩) := by
  have hleft :
      (∑ a : Fin n,
        p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inl a) *
          (τ • p27Augmented A W) (Sum.inl a) (Sum.inr j)) =
        τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A)) (fun a => W a j)) i := by
    simp only [p27Phi_augmented_left]
    simp only [Matrix.smul_apply, p27Augmented, Matrix.fromBlocks_apply₁₂,
      Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [smul_eq_mul]
    ring
  have hright :
      (∑ b : Fin p,
        p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr b) *
          (τ • p27Augmented A W) (Sum.inr b) (Sum.inr j)) =
        if j.val = 0 then 0 else
          τ * p27Phi (ell + 1) (τ • p27Augmented A W)
            (Sum.inl i)
            (Sum.inr ⟨j.val - 1, (Nat.sub_le j.val 1).trans_lt j.isLt⟩) := by
    simpa only [Matrix.smul_apply, p27Augmented, Matrix.fromBlocks_apply₂₂]
      using p27Shift_column_sum
        (fun b => p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr b))
        τ j
  rw [p27Phi_recur]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rw [hleft, hright]
  simp

private theorem p27ReverseColumn_succ {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (m : ℕ) (hm : m + 1 < p)
    (r : Fin (m + 1)) :
    p27ReverseColumn W ⟨m + 1, hm⟩ r.succ =
      p27ReverseColumn W ⟨m, Nat.lt_of_succ_lt hm⟩ r := by
  funext a
  unfold p27ReverseColumn
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk, Fin.val_succ]
  omega

private theorem p27ReverseColumn_zero {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (j : Fin p) :
    p27ReverseColumn W j (0 : Fin (j.val + 1)) = fun a => W a j := by
  funext a
  simp [p27ReverseColumn]

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
  suffices h : ∀ (m : ℕ) (hm : m < p) (ell : ℕ) (i : Fin n),
      p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr ⟨m, hm⟩) =
        ∑ r : Fin (m + 1),
          τ ^ (r.val + 1) *
            (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
              (p27ReverseColumn W ⟨m, hm⟩ r)) i by
    exact h j.val j.isLt ell i
  intro m
  induction m with
  | zero =>
      intro hm ell i
      have hr := p27Phi_augmented_recur A W τ ell (⟨0, hm⟩ : Fin p) i
      rw [hr]
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero, zero_add, pow_one, add_zero]
      rw [p27ReverseColumn_zero]
      simp
  | succ m ih =>
      intro hm ell i
      have hr := p27Phi_augmented_recur A W τ ell (⟨m + 1, hm⟩ : Fin p) i
      have hp := ih (Nat.lt_of_succ_lt hm) (ell + 1) i
      rw [hr]
      simp only [show m + 1 ≠ 0 by omega, if_false,
        Nat.add_sub_cancel_right]
      rw [hp]
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [Finset.mul_sum]
      congr 1
      · simp only [Fin.val_zero, zero_add, pow_one]
        rw [p27ReverseColumn_zero]
      · apply Finset.sum_congr rfl
        intro r hrmem
        rw [p27ReverseColumn_succ W m hm r]
        simp only [Fin.val_succ]
        have hidx : ell + 1 + r.val + 1 = ell + (r.val + 1) + 1 := by omega
        rw [hidx]
        have hpow : τ ^ (r.val + 1 + 1) = τ * τ ^ (r.val + 1) := by
          rw [pow_succ]
          ring
        rw [hpow]
        ring

end VSCLReuse

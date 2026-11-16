import VSCLReuse.P27.Definitions

open scoped BigOperators Topology Matrix
open scoped Matrix.Norms.Operator
open Matrix

namespace VSCLReuse

private lemma p27_norm_entry_le {ι : Type*} [Fintype ι] (B : Matrix ι ι ℂ)
    (i j : ι) : ‖B i j‖ ≤ ‖B‖ := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast (Finset.single_le_sum (s := Finset.univ)
    (fun x _ => zero_le (‖B i x‖₊)) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun x : ι => ∑ y, ‖B x y‖₊) (Finset.mem_univ i))

private lemma p27Phi_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  letI : Nonempty ι := ⟨i⟩
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖B‖) ?_
  intro k
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, norm_natCast]
  calc
    ((Nat.factorial (k + ell) : ℝ)⁻¹) * ‖(B ^ k) i j‖ ≤
      ((Nat.factorial (k + ell) : ℝ)⁻¹) * ‖B‖ ^ k := by
        gcongr
        exact (p27_norm_entry_le (B ^ k) i j).trans (norm_pow_le B k)
    _ ≤ ‖B‖ ^ k / Nat.factorial k := by
      rw [div_eq_mul_inv]
      rw [mul_comm (‖B‖ ^ k)]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
      simpa only [one_div] using (one_div_le_one_div_of_le
        (by exact_mod_cast Nat.factorial_pos k : (0 : ℝ) < (Nat.factorial k : ℝ))
        (by exact_mod_cast Nat.factorial_le (Nat.le_add_right k ell) :
          (Nat.factorial k : ℝ) ≤ (Nat.factorial (k + ell) : ℝ)))

private lemma p27Phi_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    p27Phi ell B = ((Nat.factorial ell : ℂ)⁻¹) • 1 + p27Phi (ell + 1) B * B := by
  have h := (p27Phi_summable ell B).sum_add_tsum_nat_add 1
  have htail :
      (∑' k : ℕ, ((Nat.factorial (k + 1 + ell) : ℂ)⁻¹) • B ^ (k + 1)) =
        p27Phi (ell + 1) B * B := by
    rw [p27Phi, ← (p27Phi_summable (ell + 1) B).tsum_mul_right B]
    apply tsum_congr
    intro k
    rw [pow_succ, smul_mul_assoc]
    simp only [Nat.add_assoc, Nat.add_comm 1 ell]
  change (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) = _
  calc
    _ = (∑ i ∈ Finset.range 1, ((Nat.factorial (i + ell) : ℂ)⁻¹) • B ^ i) +
          ∑' i : ℕ, ((Nat.factorial (i + 1 + ell) : ℂ)⁻¹) • B ^ (i + 1) := h.symm
    _ = ((Nat.factorial ell : ℂ)⁻¹) • 1 + p27Phi (ell + 1) B * B := by
      simpa only [Finset.sum_range_one, Nat.zero_add, pow_zero] using
        congrArg (fun x : Matrix ι ι ℂ => ((Nat.factorial ell : ℂ)⁻¹) • 1 + x) htail

private lemma p27_block_pow {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (J : Matrix (Fin p) (Fin p) ℂ) (k : ℕ) :
    ∃ M : Matrix (Fin n) (Fin p) ℂ, ∃ N : Matrix (Fin p) (Fin p) ℂ,
      (Matrix.fromBlocks A W 0 J) ^ k = Matrix.fromBlocks (A ^ k) M 0 N := by
  induction k with
  | zero =>
      refine ⟨0, 1, ?_⟩
      simp only [pow_zero, Matrix.fromBlocks_one]
  | succ k ih =>
      obtain ⟨M, N, h⟩ := ih
      refine ⟨A ^ k * W + M * J, N * J, ?_⟩
      rw [pow_succ, h, Matrix.fromBlocks_multiply]
      simp [Matrix.mul_zero, Matrix.zero_mul, pow_succ]

private lemma p27_scaled_augmented {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) :
    τ • p27Augmented A W =
      Matrix.fromBlocks (τ • A) (τ • W) 0 (τ • p27Shift p) := by
  simp [p27Augmented, Matrix.fromBlocks_smul]

private lemma p27Phi_block_topleft {n p : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin p) ℂ)
    (D : Matrix (Fin p) (Fin p) ℂ) (ell : ℕ) (i h : Fin n) :
    p27Phi ell (Matrix.fromBlocks C V 0 D) (Sum.inl i) (Sum.inl h) =
      p27Phi ell C i h := by
  let B := Matrix.fromBlocks C V 0 D
  have hsB := p27Phi_summable ell B
  have hsC := p27Phi_summable ell C
  dsimp [B] at hsB
  have hL1 : (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) •
      (Matrix.fromBlocks C V 0 D) ^ k) (Sum.inl i) =
      ∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) •
      (Matrix.fromBlocks C V 0 D) ^ k) (Sum.inl i) := tsum_apply hsB
  have hR1 : (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • C ^ k) i =
      ∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) • C ^ k) i := tsum_apply hsC
  rw [p27Phi, p27Phi]
  rw [hL1, tsum_apply ((Pi.summable.mp hsB) (Sum.inl i))]
  rw [hR1, tsum_apply ((Pi.summable.mp hsC) i)]
  apply tsum_congr
  intro k
  obtain ⟨M, N, hk⟩ := p27_block_pow C V D k
  simp only [Matrix.smul_apply]
  rw [hk, Matrix.fromBlocks_apply₁₁]

private lemma p27Phi_column_step {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (j : Fin p) (i : Fin n) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A)) (fun h => W h j)) i +
        τ * ∑ b : Fin p, if j.val = b.val + 1 then
          p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr b)
        else 0 := by
  let B := τ • p27Augmented A W
  have h := congrArg (fun M : Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℂ =>
      M (Sum.inl i) (Sum.inr j)) (p27Phi_step ell B)
  dsimp [B] at h
  rw [p27_scaled_augmented] at h
  simp only [Matrix.smul_apply, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂, p27Shift] at h
  simp only [p27_scaled_augmented]
  rw [h]
  simp only [Matrix.one_apply, Sum.inl_ne_inr,
    if_false, mul_zero, zero_add]
  simp only [Matrix.mulVec, dotProduct, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [p27Phi_block_topleft]
    ring
  · apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> ring

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
  cases p with
  | zero => exact j.elim0
  | succ p =>
      induction j using Fin.induction generalizing ell with
      | zero =>
          have hs := p27Phi_column_step A W τ ell (0 : Fin (p + 1)) i
          simp at hs
          simpa [Fin.sum_univ_succ, p27ReverseColumn] using hs
      | succ b ih =>
          have hs := p27Phi_column_step A W τ ell b.succ i
          have hshift :
              (∑ x : Fin (p + 1), if b.succ.val = x.val + 1 then
                  p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr x)
                else 0) =
                  p27Phi (ell + 1) (τ • p27Augmented A W)
                    (Sum.inl i) (Sum.inr b.castSucc) := by
            calc
              _ = (if b.succ.val = b.castSucc.val + 1 then
                    p27Phi (ell + 1) (τ • p27Augmented A W)
                      (Sum.inl i) (Sum.inr b.castSucc) else 0) := by
                apply Finset.sum_eq_single b.castSucc
                · intro x hx hne
                  split_ifs with hh
                  · exfalso
                    apply hne
                    apply Fin.ext
                    simp only [Fin.val_succ, Fin.val_castSucc] at hh ⊢
                    omega
                  · rfl
                · simp
              _ = _ := by simp
          rw [hshift, ih (ell + 1)] at hs
          rw [Fin.sum_univ_succ]
          rw [hs]
          congr 1
          · have hrev0 : p27ReverseColumn W b.succ 0 = fun h => W h b.succ := by
              funext h
              apply congrArg (W h)
              apply Fin.ext
              simp
            simp [hrev0]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            have hrev : p27ReverseColumn W b.succ r.succ =
                p27ReverseColumn W b.castSucc r := by
              funext h
              apply congrArg (W h)
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_castSucc]
              omega
            rw [← hrev]
            simp only [Fin.val_succ, Nat.add_assoc, pow_succ]
            ring_nf
            rfl

end VSCLReuse

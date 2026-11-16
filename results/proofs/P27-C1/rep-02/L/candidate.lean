import VSCLReuse.P27.Definitions
import Mathlib.Topology.UniformSpace.Matrix

open scoped BigOperators Topology Matrix
open Matrix

namespace VSCLReuse

set_option maxHeartbeats 1000000


private lemma p27_phi_summable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) :
    Summable (fun k : ℕ => ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) := by
  change Summable (fun k : ℕ => fun i j => ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j)
  refine Pi.summable.mpr (fun i => Pi.summable.mpr (fun j => ?_))
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖B‖)
  intro k
  have hfac : (Nat.factorial k : ℝ) ≤ (Nat.factorial (k + ell) : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right k ell)
  have hpow : ‖(B ^ k) i j‖ ≤ ‖B‖ ^ k := by
    have hentry (M : Matrix ι ι ℂ) : ‖M i j‖ ≤ ‖M‖ := by
      rw [Matrix.linfty_opNorm_def]
      have hrow : ‖M i j‖₊ ≤ ∑ b : ι, ‖M i b‖₊ :=
        Finset.single_le_sum (fun b _ => zero_le (‖M i b‖₊)) (Finset.mem_univ j)
      have hsup : (∑ b : ι, ‖M i b‖₊) ≤
          (Finset.univ : Finset ι).sup (fun a => ∑ b : ι, ‖M a b‖₊) :=
        Finset.le_sup (f := fun a : ι => ∑ b : ι, ‖M a b‖₊) (Finset.mem_univ i)
      exact_mod_cast hrow.trans hsup
    exact (hentry (B ^ k)).trans (norm_pow_le B k)
  simp only [norm_mul, norm_inv, Complex.norm_natCast]
  rw [div_eq_mul_inv, mul_comm (‖B‖ ^ k)]
  gcongr

private noncomputable def p27Upper {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) : ℕ → Matrix (Fin n) (Fin p) ℂ :=
  Nat.rec 0 (fun k M => (τ • A) ^ k * (τ • W) + M * (τ • p27Shift p))

private lemma p27_power_blocks {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) :
    (τ • p27Augmented A W) ^ k =
      Matrix.fromBlocks ((τ • A) ^ k) (p27Upper A W τ k) 0
        ((τ • p27Shift p) ^ k) := by
  have hB : τ • p27Augmented A W =
      Matrix.fromBlocks (τ • A) (τ • W) 0 (τ • p27Shift p) := by
    simp [p27Augmented, Matrix.fromBlocks_smul]
  induction k with
  | zero => simp [p27Upper, Matrix.fromBlocks_one]
  | succ k ih =>
      rw [pow_succ, ih, hB, Matrix.fromBlocks_multiply]
      simp [p27Upper, pow_succ]

private lemma p27_mul_shift_zero {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (i : Fin n) (h : 0 < p) :
    (M * (τ • p27Shift p)) i ⟨0, h⟩ = 0 := by
  simp [Matrix.mul_apply, p27Shift]

private lemma p27_mul_shift_succ {n p : ℕ} (M : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (i : Fin n) (j : Fin p) (h : j.val + 1 < p) :
    (M * (τ • p27Shift p)) i ⟨j.val + 1, h⟩ = τ * M i j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [p27Shift, mul_comm]
  · intro b _ hb
    have hne : j.val ≠ b.val := by
      intro heq
      apply hb
      exact Fin.ext heq.symm
    simp [p27Shift, hne]
  · simp

private lemma p27_phi_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (i j : ι) :
    p27Phi ell B i j =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j := by
  letI : Nonempty ι := ⟨i⟩
  have hs := p27_phi_summable ell B
  have hsi : Summable (fun k : ℕ => (((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) i) :=
    (Pi.summable.mp hs) i
  unfold p27Phi
  calc
    (∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) i j =
        (∑' k : ℕ, (((Nat.factorial (k + ell) : ℂ)⁻¹) • B ^ k) i) j := by
          exact congrArg (fun row => row j) (tsum_apply hs)
    _ = ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i j := by
      rw [tsum_apply hsi]
      rfl

private lemma p27_phi_mulvec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι) :
    (Matrix.mulVec (p27Phi ell B) v) i =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) *
        (Matrix.mulVec (B ^ k) v) i := by
  letI : Nonempty ι := ⟨i⟩
  have hs : ∀ a : ι, Summable (fun k : ℕ =>
      (((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) * v a) := by
    intro a
    have hsa := (Pi.summable.mp ((Pi.summable.mp (p27_phi_summable ell B)) i)) a
    exact (by simpa using hsa.mul_right (v a))
  calc
    (Matrix.mulVec (p27Phi ell B) v) i =
        ∑ a : ι, (p27Phi ell B i a) * v a := by rfl
    _ = ∑ a : ι, ∑' k : ℕ,
        (((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) * v a := by
          simp_rw [p27_phi_entry, tsum_mul_right]
    _ = ∑' k : ℕ, ∑ a : ι,
        (((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) * v a := by
          exact (Summable.tsum_finsetSum (s := Finset.univ)
            (fun a _ => hs a)).symm
    _ = ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) *
        (Matrix.mulVec (B ^ k) v) i := by
          congr 1
          funext k
          simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private lemma p27_upper_first {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) (i : Fin n) (j : Fin p) :
    ((τ • A) ^ k * (τ • W)) i j =
      τ * (Matrix.mulVec ((τ • A) ^ k) (fun a => W a j)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]

private lemma p27_upper_zero {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) (i : Fin n) (h : 0 < p) :
    p27Upper A W τ (k + 1) i ⟨0, h⟩ =
      τ * (Matrix.mulVec ((τ • A) ^ k) (fun a => W a ⟨0, h⟩)) i := by
  change (((τ • A) ^ k * (τ • W)) +
      p27Upper A W τ k * (τ • p27Shift p)) i ⟨0, h⟩ = _
  simp only [Matrix.add_apply, p27_upper_first, p27_mul_shift_zero, add_zero]

private lemma p27_upper_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (k : ℕ) (i : Fin n) (j : Fin p) (h : j.val + 1 < p) :
    p27Upper A W τ (k + 1) i ⟨j.val + 1, h⟩ =
      τ * (Matrix.mulVec ((τ • A) ^ k) (fun a => W a ⟨j.val + 1, h⟩)) i +
      τ * p27Upper A W τ k i j := by
  change (((τ • A) ^ k * (τ • W)) +
      p27Upper A W τ k * (τ • p27Shift p)) i ⟨j.val + 1, h⟩ = _
  simp only [Matrix.add_apply, p27_upper_first, p27_mul_shift_succ]

private lemma p27_phi_upper_entry {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (j : Fin p) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      ∑' k : ℕ, ((Nat.factorial (k + ell) : ℂ)⁻¹) * p27Upper A W τ k i j := by
  rw [p27_phi_entry]
  congr 1
  funext k
  rw [p27_power_blocks]
  rfl

private lemma p27_upper_summable {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (j : Fin p) :
    Summable (fun k : ℕ =>
      ((Nat.factorial (k + ell) : ℂ)⁻¹) * p27Upper A W τ k i j) := by
  letI : Nonempty (Fin n ⊕ Fin p) := ⟨Sum.inl i⟩
  have hs := (Pi.summable.mp
      ((Pi.summable.mp (p27_phi_summable ell (τ • p27Augmented A W)))
        (Sum.inl i))) (Sum.inr j)
  simpa only [p27_power_blocks, Matrix.fromBlocks_apply₁₂] using hs

private lemma p27_phi_upper_shift {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (j : Fin p) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) =
      ∑' k : ℕ, ((Nat.factorial (k + ell + 1) : ℂ)⁻¹) *
        p27Upper A W τ (k + 1) i j := by
  rw [p27_phi_upper_entry]
  let f : ℕ → ℂ := fun k =>
    ((Nat.factorial (k + ell) : ℂ)⁻¹) * p27Upper A W τ k i j
  have hs : Summable f := p27_upper_summable A W τ ell i j
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  change f 0 + (∑' k : ℕ, f (k + 1)) = ∑' k : ℕ, f k at hsplit
  have hf0 : f 0 = 0 := by simp [f, p27Upper]
  rw [hf0, zero_add] at hsplit
  simpa only [f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit.symm

private lemma p27_mulvec_summable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ell : ℕ) (B : Matrix ι ι ℂ) (v : ι → ℂ) (i : ι) :
    Summable (fun k : ℕ =>
      ((Nat.factorial (k + ell) : ℂ)⁻¹) * (Matrix.mulVec (B ^ k) v) i) := by
  letI : Nonempty ι := ⟨i⟩
  have hs : ∀ a : ι, Summable (fun k : ℕ =>
      (((Nat.factorial (k + ell) : ℂ)⁻¹) * (B ^ k) i a) * v a) := by
    intro a
    have hsa := (Pi.summable.mp ((Pi.summable.mp (p27_phi_summable ell B)) i)) a
    exact (by simpa using hsa.mul_right (v a))
  have hsum := summable_sum (s := Finset.univ) (fun a _ => hs a)
  simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hsum

private lemma p27_phi_zero_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (h : 0 < p) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr ⟨0, h⟩) =
      τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
        (fun a => W a ⟨0, h⟩)) i := by
  rw [p27_phi_upper_shift]
  simp_rw [p27_upper_zero]
  calc
    (∑' k : ℕ, ((Nat.factorial (k + ell + 1) : ℂ)⁻¹) *
        (τ * (Matrix.mulVec ((τ • A) ^ k) (fun a => W a ⟨0, h⟩)) i)) =
      ∑' k : ℕ, τ * (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
        (Matrix.mulVec ((τ • A) ^ k) (fun a => W a ⟨0, h⟩)) i) := by
          congr 1
          funext k
          ring
    _ = τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
        (fun a => W a ⟨0, h⟩)) i := by
          rw [tsum_mul_left, p27_phi_mulvec]

private lemma p27_phi_succ_column {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (j : Fin p) (h : j.val + 1 < p) :
    p27Phi ell (τ • p27Augmented A W) (Sum.inl i)
        (Sum.inr ⟨j.val + 1, h⟩) =
      τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
        (fun a => W a ⟨j.val + 1, h⟩)) i +
      τ * p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) := by
  have hfirst : Summable (fun k : ℕ => τ *
      (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
        (Matrix.mulVec ((τ • A) ^ k)
          (fun a => W a ⟨j.val + 1, h⟩)) i)) :=
    (p27_mulvec_summable (ell + 1) (τ • A)
      (fun a => W a ⟨j.val + 1, h⟩) i).mul_left τ
  have hsecond : Summable (fun k : ℕ => τ *
      (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
        p27Upper A W τ k i j)) :=
    (p27_upper_summable A W τ (ell + 1) i j).mul_left τ
  rw [p27_phi_upper_shift]
  simp_rw [p27_upper_succ]
  calc
    (∑' k : ℕ, ((Nat.factorial (k + ell + 1) : ℂ)⁻¹) *
      (τ * (Matrix.mulVec ((τ • A) ^ k)
        (fun a => W a ⟨j.val + 1, h⟩)) i + τ * p27Upper A W τ k i j)) =
      ∑' k : ℕ, (τ * (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
        (Matrix.mulVec ((τ • A) ^ k)
          (fun a => W a ⟨j.val + 1, h⟩)) i) +
        τ * (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
          p27Upper A W τ k i j)) := by
            congr 1
            funext k
            ring
    _ = (∑' k : ℕ, τ * (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
        (Matrix.mulVec ((τ • A) ^ k)
          (fun a => W a ⟨j.val + 1, h⟩)) i)) +
        (∑' k : ℕ, τ * (((Nat.factorial (k + (ell + 1)) : ℂ)⁻¹) *
          p27Upper A W τ k i j)) := hfirst.tsum_add hsecond
    _ = τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
        (fun a => W a ⟨j.val + 1, h⟩)) i +
        τ * p27Phi (ell + 1) (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j) := by
          rw [tsum_mul_left, tsum_mul_left, p27_phi_mulvec, p27_phi_upper_entry]

private lemma p27_reverse_zero {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (j : Fin p) :
    p27ReverseColumn W j (0 : Fin (j.val + 1)) = fun a => W a j := by
  funext a
  simp [p27ReverseColumn]

private lemma p27_reverse_succ {n p : ℕ}
    (W : Matrix (Fin n) (Fin p) ℂ) (j : Fin p)
    (h : j.val + 1 < p) (r : Fin (j.val + 1)) :
    p27ReverseColumn W ⟨j.val + 1, h⟩ r.succ = p27ReverseColumn W j r := by
  funext a
  apply congrArg (W a)
  apply Fin.ext
  simp only [Fin.val_succ]
  omega

private lemma p27_column_sum_succ {n p : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (W : Matrix (Fin n) (Fin p) ℂ)
    (τ : ℂ) (ell : ℕ) (i : Fin n) (j : Fin p) (h : j.val + 1 < p) :
    (∑ r : Fin ((j.val + 1) + 1),
      τ ^ (r.val + 1) *
        (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
          (p27ReverseColumn W ⟨j.val + 1, h⟩ r)) i) =
      τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
        (fun a => W a ⟨j.val + 1, h⟩)) i +
      τ * (∑ r : Fin (j.val + 1),
        τ ^ (r.val + 1) *
          (Matrix.mulVec (p27Phi ((ell + 1) + r.val + 1) (τ • A))
            (p27ReverseColumn W j r)) i) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, p27_reverse_zero]
  rw [Finset.mul_sum]
  apply congrArg₂ (fun x y : ℂ => x + y)
  · simp
  · apply Finset.sum_congr rfl
    intro r _
    rw [p27_reverse_succ]
    simp only [Fin.val_succ]
    have harg : ell + (r.val + 1) + 1 = (ell + 1) + r.val + 1 := by omega
    rw [harg]
    rw [pow_succ]
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
  cases p with
  | zero => exact Fin.elim0 j
  | succ p =>
      induction j using Fin.induction generalizing ell with
      | zero =>
          calc
            p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr 0) =
              τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
                (fun a => W a 0)) i := by
                  simpa using p27_phi_zero_column A W τ ell i (Nat.zero_lt_succ p)
            _ = ∑ r : Fin (0 + 1),
              τ ^ (r.val + 1) *
                (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
                  (p27ReverseColumn W 0 r)) i := by
                    rw [Fin.sum_univ_one]
                    simp only [Fin.val_zero, zero_add, pow_one]
                    exact congrArg
                      (fun v : Fin n → ℂ => τ * (Matrix.mulVec
                        (p27Phi (ell + 1) (τ • A)) v) i)
                      (p27_reverse_zero W (0 : Fin (p + 1))).symm
      | succ j ih =>
          have h : j.castSucc.val + 1 < p + 1 := by simpa using j.isLt
          calc
            p27Phi ell (τ • p27Augmented A W) (Sum.inl i) (Sum.inr j.succ) =
                τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
                  (fun a => W a j.succ)) i +
                τ * p27Phi (ell + 1) (τ • p27Augmented A W)
                  (Sum.inl i) (Sum.inr j.castSucc) := by
                    simpa using p27_phi_succ_column A W τ ell i j.castSucc h
            _ = τ * (Matrix.mulVec (p27Phi (ell + 1) (τ • A))
                  (fun a => W a j.succ)) i +
                τ * (∑ r : Fin (j.castSucc.val + 1),
                  τ ^ (r.val + 1) *
                    (Matrix.mulVec (p27Phi ((ell + 1) + r.val + 1) (τ • A))
                      (p27ReverseColumn W j.castSucc r)) i) := by
                        rw [ih (ell + 1)]
            _ = ∑ r : Fin (j.succ.val + 1),
                  τ ^ (r.val + 1) *
                    (Matrix.mulVec (p27Phi (ell + r.val + 1) (τ • A))
                      (p27ReverseColumn W j.succ r)) i := by
                        simpa using (p27_column_sum_succ A W τ ell i j.castSucc h).symm

end VSCLReuse

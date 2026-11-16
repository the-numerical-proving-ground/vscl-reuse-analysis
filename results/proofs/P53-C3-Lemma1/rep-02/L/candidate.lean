import VSCLReuse.P53.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p53LibraryModel (fp : P53FPModel) :
    NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · simp

private lemma p53LibraryDot (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) :
    p53Dot fp n a x =
      NumStability.fl_dotProduct (p53LibraryModel fp) n a x := by
  cases n <;> rfl

private lemma p53LibraryPairwise (fp : P53FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    p53PairwiseSum fp r v =
      NumStability.fl_pairwiseSum (p53LibraryModel fp) r v := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [p53PairwiseSum, NumStability.fl_pairwiseSum]
      congr 1
      · exact ih _
      · exact ih _

private lemma p53LibraryCascadeSum (fp : P53FPModel) (n : ℕ)
    (v : Fin n → ℝ) :
    p53CascadeSum fp n v =
      NumStability.fl_clog2PairwiseSum (p53LibraryModel fp) n v := by
  change p53PairwiseSum fp (Nat.clog 2 n) (p53ZeroPad n v) =
    NumStability.fl_pairwiseSum (p53LibraryModel fp) (Nat.clog 2 n)
      (NumStability.scalarFinZeroPad n (2 ^ Nat.clog 2 n) v)
  simpa only [p53ZeroPad, p53ScalarPad, NumStability.scalarFinZeroPad] using
    p53LibraryPairwise fp (Nat.clog 2 n) (p53ZeroPad n v)

private lemma p53_succ_le_pow_two (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

private lemma p53_clog_succ_le (n : ℕ) (hn : 0 < n) :
    Nat.clog 2 n + 1 ≤ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := Nat.clog_le_of_le_pow (p53_succ_le_pow_two k)
  simpa only [Nat.succ_eq_add_one] using Nat.add_le_add_right h 1

theorem p53_lemma1_whole (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ)
    (hn : 0 < n)
    (hrec : P53GammaValid fp.u n) :
    (|p53Dot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u n * ∑ i : Fin n, |a i| * |x i|) ∧
    (|p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 n + 1) *
        ∑ i : Fin n, |a i| * |x i|) := by
  -- PROOF_START P53-C3-Lemma1-H001
  let model := p53LibraryModel fp
  have hclog : Nat.clog 2 n + 1 ≤ n := p53_clog_succ_le n hn
  have hvalid : NumStability.gammaValid model (Nat.clog 2 n + 1) :=
    NumStability.gammaValid_mono model hclog hrec
  have hvalid1 : NumStability.gammaValid model 1 :=
    NumStability.gammaValid_mono model (by omega : 1 ≤ Nat.clog 2 n + 1) hvalid
  constructor
  · simpa only [← p53LibraryDot, NumStability.gamma, p53Gamma,
        model, p53LibraryModel] using
      NumStability.dotProduct_error_bound model n a x hrec
  · let v : Fin n → ℝ := fun i => fp.fl_mul (a i) (x i)
    obtain ⟨ηadd, hηadd, hsum⟩ :=
      NumStability.clog2PairwiseSum_backward_error model n v
        (NumStability.gammaValid_mono model (by omega) hvalid)
    let δ : Fin n → ℝ := fun i => Classical.choose (fp.model_mul (a i) (x i))
    have hδ : ∀ i, |δ i| ≤ fp.u ∧ v i = a i * x i * (1 + δ i) := by
      intro i
      exact Classical.choose_spec (fp.model_mul (a i) (x i))
    have hδone : ∀ i, |δ i| ≤ NumStability.gamma model 1 := by
      intro i
      exact (hδ i).1.trans (NumStability.u_le_gamma model (by omega) hvalid1)
    let η : Fin n → ℝ := fun i =>
      Classical.choose (NumStability.gamma_mul model (Nat.clog 2 n) 1
        (ηadd i) (δ i) (hηadd i) (hδone i) hvalid)
    have hη : ∀ i, |η i| ≤ NumStability.gamma model (Nat.clog 2 n + 1) := by
      intro i
      exact (Classical.choose_spec (NumStability.gamma_mul model (Nat.clog 2 n) 1
        (ηadd i) (δ i) (hηadd i) (hδone i) hvalid)).1
    have hηeq : ∀ i, (1 + ηadd i) * (1 + δ i) = 1 + η i := by
      intro i
      exact (Classical.choose_spec (NumStability.gamma_mul model (Nat.clog 2 n) 1
        (ηadd i) (δ i) (hηadd i) (hδone i) hvalid)).2
    have hfl : p53CascadeDot fp n a x =
        ∑ i : Fin n, a i * x i * (1 + η i) := by
      change p53CascadeSum fp n v = _
      rw [p53LibraryCascadeSum, hsum]
      apply Finset.sum_congr rfl
      intro i _
      rw [(hδ i).2]
      rw [← hηeq i]
      ring
    have herr : p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i =
        ∑ i : Fin n, a i * x i * η i := by
      rw [hfl, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [herr]
    calc
      |∑ i : Fin n, a i * x i * η i|
          ≤ ∑ i : Fin n, |a i * x i * η i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |a i| * |x i| * |η i| := by
            apply Finset.sum_congr rfl
            intro i _
            rw [abs_mul, abs_mul]
      _ ≤ ∑ i : Fin n, |a i| * |x i| * NumStability.gamma model (Nat.clog 2 n + 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (hη i)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = p53Gamma fp.u (Nat.clog 2 n + 1) * ∑ i : Fin n, |a i| * |x i| := by
            rw [← Finset.sum_mul, mul_comm]
            rfl

end VSCLReuse

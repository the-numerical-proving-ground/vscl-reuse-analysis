import VSCLReuse.P53.Definitions
import NumStability.Algorithms.TreeDotProduct
import NumStability.Algorithms.DotProduct

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p53FPBridge (fp : P53FPModel) : NumStability.FPModel :=
  { NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg with
    fl_add := fp.fl_add
    fl_mul := fp.fl_mul
    fl_add_zero := fp.fl_add_zero
    model_add := fp.model_add
    model_mul := fp.model_mul }

private lemma p53_dot_eq_library (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    p53Dot fp k a x =
      NumStability.fl_dotProduct (p53FPBridge fp) k a x := by
  cases k <;> rfl

private lemma p53_pairwise_eq_tree (fp : P53FPModel) :
    ∀ r (v : Fin (2 ^ r) → ℝ),
      p53PairwiseSum fp r v =
        (NumStability.SumTree.balancedTree r).eval (p53FPBridge fp) v := by
  intro r
  induction r with
  | zero =>
      intro v
      rfl
  | succ r ih =>
      intro v
      rw [p53PairwiseSum, NumStability.SumTree.balancedTree]
      rw [NumStability.SumTree.eval_cast]
      simp only [NumStability.SumTree.eval]
      congr 1
      · rw [ih]
        congr 1
      · rw [ih]
        congr 1
        funext i
        apply congrArg v
        apply Fin.ext
        simp [Fin.natAdd, Nat.add_comm]

private lemma p53_cascade_eq_library (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    p53CascadeDot fp k a x =
      NumStability.fl_clog2PairwiseDotProduct (p53FPBridge fp) k a x := by
  have hmul_zero : fp.fl_mul 0 0 = 0 := by
    obtain ⟨δ, _, hδ⟩ := fp.model_mul 0 0
    simpa using hδ
  unfold p53CascadeDot p53CascadeSum p53ZeroPad
  rw [p53_pairwise_eq_tree]
  unfold NumStability.fl_clog2PairwiseDotProduct NumStability.fl_sumTreeDotProduct
  congr 1
  funext i
  by_cases hi : i.val < k
  · simp [p53ScalarPad, NumStability.finZeroPad, p53FPBridge, hi]
  · simp [p53ScalarPad, NumStability.finZeroPad, p53FPBridge, hi, hmul_zero]

private lemma p53_clog_succ_le (l : ℕ) (hl : 2 ≤ l) :
    Nat.clog 2 l + 1 ≤ l := by
  have hpow : ∀ k : ℕ, k + 2 ≤ 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        omega
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by omega⟩
  have hclog := Nat.clog_le_of_le_pow (hpow k)
  omega

private lemma p53_gamma_eq (fp : P53FPModel) (k : ℕ) :
    NumStability.gamma (p53FPBridge fp) k = p53Gamma fp.u k := rfl

private lemma p53_gamma_valid_iff (fp : P53FPModel) (k : ℕ) :
    NumStability.gammaValid (p53FPBridge fp) k ↔ P53GammaValid fp.u k := Iff.rfl

private lemma p53_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (s : P53SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (s.count i), f (s.col i t)) = ∑ j : Fin n, f j := by
  have himage :
      Finset.univ.image (s.col i) =
        Finset.univ.filter (fun j => A i j ≠ 0) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      exact s.col_nonzero i t
    · intro hj
      exact s.covers i j hj
  calc
    (∑ t : Fin (s.count i), f (s.col i t)) =
        ∑ j ∈ Finset.univ.image (s.col i), f j := by
          rw [Finset.sum_image]
          exact (s.col_injective i).injOn
    _ = ∑ j ∈ Finset.univ.filter (fun j => A i j ≠ 0), f j := by rw [himage]
    _ = ∑ j : Fin n, f j := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro j _ hj
          apply hf j
          by_contra hne
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)

private lemma p53_abs_sign (a : ℝ) :
    |p53Sign a| = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [p53Sign, ha]
  · simp [p53Sign, ha, abs_div, abs_ne_zero.mpr ha]

private lemma p53_precomp_point {n : ℕ}
    (fp : P53FPModel) (A Ahat : Fin n → Fin n → ℝ) (η : ℝ)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i j : Fin n) :
    |Ahat i j - A i j| ≤ η * fp.u * |p53Sign (A i j)| := by
  by_cases h : A i j = 0
  · simp [h, hzero i j h, p53_abs_sign]
  · simpa [p53_abs_sign, h] using hpre i j h

private lemma p53_transfer_row {n : ℕ}
    (fp : P53FPModel) (A Ahat : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) (η g y : ℝ)
    (hη : 0 < η) (hg : 0 ≤ g)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin n)
    (hcomp : |y - ∑ j : Fin n, Ahat i j * x j| ≤
      g * ∑ j : Fin n, |Ahat i j| * |x j|) :
    |y - ∑ j : Fin n, A i j * x j| ≤
      g * (∑ j : Fin n, |A i j| * |x j|) +
      (η * fp.u + g * (η * fp.u)) *
        (∑ j : Fin n, |p53Sign (A i j)| * |x j|) := by
  have hpoint : ∀ j : Fin n,
      |Ahat i j - A i j| ≤ η * fp.u * |p53Sign (A i j)| :=
    p53_precomp_point fp A Ahat η hpre hzero i
  have habs : ∀ j : Fin n,
      |Ahat i j| ≤ |A i j| + η * fp.u * |p53Sign (A i j)| := by
    intro j
    calc
      |Ahat i j| = |(Ahat i j - A i j) + A i j| := by ring
      _ ≤ |Ahat i j - A i j| + |A i j| := abs_add_le _ _
      _ ≤ |A i j| + η * fp.u * |p53Sign (A i j)| := by
        linarith [hpoint j]
  have hsumabs :
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
        (∑ j : Fin n, |A i j| * |x j|) +
          η * fp.u * (∑ j : Fin n, |p53Sign (A i j)| * |x j|) := by
    calc
      _ ≤ ∑ j : Fin n,
          (|A i j| + η * fp.u * |p53Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (habs j) (abs_nonneg _)
      _ = ∑ j : Fin n,
          (|A i j| * |x j| + η * fp.u * (|p53Sign (A i j)| * |x j|)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = (∑ j : Fin n, |A i j| * |x j|) +
          ∑ j : Fin n, η * fp.u * (|p53Sign (A i j)| * |x j|) :=
            Finset.sum_add_distrib
      _ = _ := by rw [Finset.mul_sum]
  have hdiff :
      |(∑ j : Fin n, Ahat i j * x j) -
        (∑ j : Fin n, A i j * x j)| ≤
        η * fp.u * (∑ j : Fin n, |p53Sign (A i j)| * |x j|) := by
    have heq :
        (∑ j : Fin n, Ahat i j * x j) -
          (∑ j : Fin n, A i j * x j) =
          ∑ j : Fin n, (Ahat i j - A i j) * x j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    calc
      |∑ j : Fin n, (Ahat i j - A i j) * x j| ≤
          ∑ j : Fin n, |(Ahat i j - A i j) * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n,
          (η * fp.u * |p53Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hpoint j) (abs_nonneg _)
      _ = _ := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
  have htri :
      |y - ∑ j : Fin n, A i j * x j| ≤
        |y - ∑ j : Fin n, Ahat i j * x j| +
          |(∑ j : Fin n, Ahat i j * x j) -
            (∑ j : Fin n, A i j * x j)| := by
    convert abs_add_le
      (y - ∑ j : Fin n, Ahat i j * x j)
      ((∑ j : Fin n, Ahat i j * x j) -
        (∑ j : Fin n, A i j * x j)) using 1 <;> ring
  calc
    _ ≤ |y - ∑ j : Fin n, Ahat i j * x j| +
        |(∑ j : Fin n, Ahat i j * x j) -
          (∑ j : Fin n, A i j * x j)| := htri
    _ ≤ g * (∑ j : Fin n, |Ahat i j| * |x j|) +
        η * fp.u * (∑ j : Fin n, |p53Sign (A i j)| * |x j|) :=
          add_le_add hcomp hdiff
    _ ≤ g * ((∑ j : Fin n, |A i j| * |x j|) +
          η * fp.u * (∑ j : Fin n, |p53Sign (A i j)| * |x j|)) +
          η * fp.u * (∑ j : Fin n, |p53Sign (A i j)| * |x j|) :=
            add_le_add (mul_le_mul_of_nonneg_left hsumabs hg) le_rfl
    _ = _ := by ring

theorem p53_theorem2_all_schedules {n l : ℕ} (fp : P53FPModel)
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (η : ℝ)
    (hcard : ∀ i, (Finset.univ.filter (fun j => A i j ≠ 0)).card ≤ l)
    (hln : 2 ≤ l ∧ l ≤ n) (hvalid : P53GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0) :
    ∀ schedule : P53SparseSchedule A l,
      (∀ i : Fin n,
        |p53SparseMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, A i j * x j| ≤
          p53Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
          (η * fp.u + p53Gamma fp.u l * (η * fp.u)) *
            (∑ j : Fin n, |p53Sign (A i j)| * |x j|)) ∧
      (∀ i : Fin n,
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
            ∑ j : Fin n, A i j * x j| ≤
          p53Gamma fp.u (Nat.clog 2 l + 1) *
            (∑ j : Fin n, |A i j| * |x j|) +
          (η * fp.u +
            p53Gamma fp.u (Nat.clog 2 l + 1) * (η * fp.u)) *
            (∑ j : Fin n, |p53Sign (A i j)| * |x j|)) := by
  -- PROOF_START P53-C3-H001
  intro schedule
  let bridge := p53FPBridge fp
  have hvalidl : NumStability.gammaValid bridge l :=
    (p53_gamma_valid_iff fp l).2 hvalid
  have hvalidcl : NumStability.gammaValid bridge (Nat.clog 2 l + 1) :=
    NumStability.gammaValid_mono bridge (p53_clog_succ_le l hln.1) hvalidl
  constructor
  · intro i
    let k := schedule.count i
    let a : Fin k → ℝ := fun t => Ahat i (schedule.col i t)
    let b : Fin k → ℝ := fun t => x (schedule.col i t)
    have hk : k ≤ l := schedule.count_le i
    have hvalidk : NumStability.gammaValid bridge k :=
      NumStability.gammaValid_mono bridge hk hvalidl
    have hsumhat : (∑ t : Fin k, a t * b t) =
        ∑ j : Fin n, Ahat i j * x j := by
      simpa [a, b, k] using
        p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
          (by intro j hj; simp [hzero i j hj])
    have hsumabs : (∑ t : Fin k, |a t| * |b t|) =
        ∑ j : Fin n, |Ahat i j| * |x j| := by
      simpa [a, b, k] using
        p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
          (by intro j hj; simp [hzero i j hj])
    have hdot := NumStability.dotProduct_error_bound bridge k a b hvalidk
    have hcomp_small :
        |p53SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
          p53Gamma fp.u k *
            (∑ j : Fin n, |Ahat i j| * |x j|) := by
      change |p53Dot fp k a b - _| ≤ _
      rw [← hsumhat, ← hsumabs, p53_dot_eq_library]
      simpa only [p53_gamma_eq] using hdot
    have hgm : p53Gamma fp.u k ≤ p53Gamma fp.u l := by
      simpa only [← p53_gamma_eq] using
        (NumStability.gamma_mono bridge hk hvalidl)
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcomp :
        |p53SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
          p53Gamma fp.u l *
            (∑ j : Fin n, |Ahat i j| * |x j|) :=
      hcomp_small.trans (mul_le_mul_of_nonneg_right hgm hsum_nonneg)
    have hg : 0 ≤ p53Gamma fp.u l := by
      rw [← p53_gamma_eq]
      exact NumStability.gamma_nonneg bridge hvalidl
    exact p53_transfer_row fp A Ahat x η (p53Gamma fp.u l)
      (p53SparseMatVec fp A Ahat x schedule i) hη hg hpre hzero i hcomp
  · intro i
    let k := schedule.count i
    let a : Fin k → ℝ := fun t => Ahat i (schedule.col i t)
    let b : Fin k → ℝ := fun t => x (schedule.col i t)
    have hk : k ≤ l := schedule.count_le i
    have hck : Nat.clog 2 k + 1 ≤ Nat.clog 2 l + 1 :=
      Nat.add_le_add_right (Nat.clog_mono_right 2 hk) 1
    have hvalidk : NumStability.gammaValid bridge (Nat.clog 2 k + 1) :=
      NumStability.gammaValid_mono bridge hck hvalidcl
    have hsumhat : (∑ t : Fin k, a t * b t) =
        ∑ j : Fin n, Ahat i j * x j := by
      simpa [a, b, k] using
        p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
          (by intro j hj; simp [hzero i j hj])
    have hsumabs : (∑ t : Fin k, |a t| * |b t|) =
        ∑ j : Fin n, |Ahat i j| * |x j| := by
      simpa [a, b, k] using
        p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
          (by intro j hj; simp [hzero i j hj])
    have hdot := NumStability.clog2PairwiseDotProduct_error_bound bridge k a b hvalidk
    have hcomp_small :
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
          p53Gamma fp.u (Nat.clog 2 k + 1) *
            (∑ j : Fin n, |Ahat i j| * |x j|) := by
      change |p53CascadeDot fp k a b - _| ≤ _
      rw [← hsumhat, ← hsumabs, p53_cascade_eq_library]
      simpa only [p53_gamma_eq] using hdot
    have hgm : p53Gamma fp.u (Nat.clog 2 k + 1) ≤
        p53Gamma fp.u (Nat.clog 2 l + 1) := by
      simpa only [← p53_gamma_eq] using
        (NumStability.gamma_mono bridge hck hvalidcl)
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have hcomp :
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
          p53Gamma fp.u (Nat.clog 2 l + 1) *
            (∑ j : Fin n, |Ahat i j| * |x j|) :=
      hcomp_small.trans (mul_le_mul_of_nonneg_right hgm hsum_nonneg)
    have hg : 0 ≤ p53Gamma fp.u (Nat.clog 2 l + 1) := by
      rw [← p53_gamma_eq]
      exact NumStability.gamma_nonneg bridge hvalidcl
    exact p53_transfer_row fp A Ahat x η (p53Gamma fp.u (Nat.clog 2 l + 1))
      (p53SparseCascadeMatVec fp A Ahat x schedule i) hη hg hpre hzero i hcomp

end VSCLReuse

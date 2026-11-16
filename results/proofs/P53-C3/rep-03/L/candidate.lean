import VSCLReuse.P53.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.TreeDotProduct
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p53AsFP (fp : P53FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun x y => x - y
  fl_mul := fp.fl_mul
  fl_div := fun x y => x / y
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩
  model_sqrt := by
    intro x _
    exact ⟨0, by simpa using fp.u_nonneg, by simp⟩

private lemma p53_dot_bridge (fp : P53FPModel) (k : ℕ) (a x : Fin k → ℝ) :
    p53Dot fp k a x = NumStability.fl_dotProduct (p53AsFP fp) k a x := by
  cases k <;> rfl

private lemma p53_pairwise_tree_bridge (fp : P53FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    p53PairwiseSum fp r v =
      (NumStability.SumTree.balancedTree r).eval (p53AsFP fp) v := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [p53PairwiseSum, NumStability.SumTree.balancedTree]
    rw [NumStability.SumTree.eval_cast]
    simp only [NumStability.SumTree.eval]
    congr 1
    · apply ih
    · rw [ih]
      congr 1
      funext i
      congr 1
      apply Fin.ext
      simp [Fin.natAdd, add_comm]

private lemma p53_mul_zero (fp : P53FPModel) : fp.fl_mul 0 0 = 0 := by
  obtain ⟨δ, _, hδ⟩ := fp.model_mul 0 0
  simpa using hδ

private lemma p53_cascade_bridge (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    p53CascadeDot fp k a x =
      NumStability.fl_clog2PairwiseDotProduct (p53AsFP fp) k a x := by
  unfold p53CascadeDot p53CascadeSum
    NumStability.fl_clog2PairwiseDotProduct
    NumStability.fl_sumTreeDotProduct
  rw [p53_pairwise_tree_bridge]
  congr 1
  funext i
  by_cases hi : i.val < k
  · simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi, p53AsFP]
  · simp [p53ZeroPad, p53ScalarPad, NumStability.finZeroPad, hi,
      p53AsFP, p53_mul_zero]

private lemma p53_dot_bound (fp : P53FPModel) {k l : ℕ}
    (a x : Fin k → ℝ) (hkl : k ≤ l) (hvalid : P53GammaValid fp.u l) :
    |p53Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p53Gamma fp.u l * ∑ t : Fin k, |a t| * |x t| := by
  have hv : NumStability.gammaValid (p53AsFP fp) l := hvalid
  have hk := NumStability.gammaValid_mono (p53AsFP fp) hkl hv
  have hb := NumStability.dotProduct_error_bound (p53AsFP fp) k a x hk
  rw [← p53_dot_bridge] at hb
  have hm := NumStability.gamma_mono (p53AsFP fp) hkl hv
  have hs : 0 ≤ ∑ t : Fin k, |a t| * |x t| :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    _ ≤ NumStability.gamma (p53AsFP fp) k *
        ∑ t : Fin k, |a t| * |x t| := hb
    _ ≤ NumStability.gamma (p53AsFP fp) l *
        ∑ t : Fin k, |a t| * |x t| := mul_le_mul_of_nonneg_right hm hs
    _ = _ := by rfl

private lemma p53_cascade_bound (fp : P53FPModel) {k l : ℕ}
    (a x : Fin k → ℝ) (hkl : k ≤ l) (hl : 2 ≤ l)
    (hvalid : P53GammaValid fp.u l) :
    |p53CascadeDot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p53Gamma fp.u (Nat.clog 2 l + 1) *
        ∑ t : Fin k, |a t| * |x t| := by
  have hcl : Nat.clog 2 k ≤ Nat.clog 2 l := by
    exact Nat.clog_mono_right 2 hkl
  have htarget : Nat.clog 2 l + 1 ≤ l := by
    have hp : 0 < l := by omega
    have hcp := NumStability.clog2_le_pred l hp
    omega
  have hv : NumStability.gammaValid (p53AsFP fp) l := hvalid
  have hvtarget := NumStability.gammaValid_mono (p53AsFP fp) htarget hv
  have hvk := NumStability.gammaValid_mono (p53AsFP fp)
    (Nat.add_le_add_right hcl 1) hvtarget
  have hb := NumStability.clog2PairwiseDotProduct_error_bound
    (p53AsFP fp) k a x hvk
  rw [← p53_cascade_bridge] at hb
  have hm := NumStability.gamma_mono (p53AsFP fp)
    (Nat.add_le_add_right hcl 1) hvtarget
  have hs : 0 ≤ ∑ t : Fin k, |a t| * |x t| :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc
    _ ≤ NumStability.gamma (p53AsFP fp) (Nat.clog 2 k + 1) *
        ∑ t : Fin k, |a t| * |x t| := hb
    _ ≤ NumStability.gamma (p53AsFP fp) (Nat.clog 2 l + 1) *
        ∑ t : Fin k, |a t| * |x t| := mul_le_mul_of_nonneg_right hm hs
    _ = _ := by rfl

private lemma p53_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin m)
    (f : Fin n → ℝ) (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.univ.filter (fun j => A i j ≠ 0)
  have hset : Finset.univ.image (schedule.col i) = s := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, s,
      Finset.mem_filter]
    constructor
    · rintro ⟨t, ht⟩
      rw [← ht]
      exact schedule.col_nonzero i t
    · intro hj
      obtain ⟨t, ht⟩ := schedule.covers i j hj
      exact ⟨t, ht⟩
  have hsum : (∑ j ∈ s, f j) = ∑ j : Fin n, f j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hjnot
    have hz : A i j = 0 := by
      by_contra hn
      exact hjnot (Finset.mem_filter.mpr ⟨hj, hn⟩)
    exact hf j hz
  calc
    _ = ∑ j ∈ Finset.univ.image (schedule.col i), f j := by
      rw [Finset.sum_image (fun _ _ _ _ h => schedule.col_injective i h)]
    _ = ∑ j ∈ s, f j := by rw [hset]
    _ = _ := hsum

private lemma p53_row_finish {n : ℕ} (a ah x : Fin n → ℝ)
    (computed e g : ℝ) (hg : 0 ≤ g)
    (hcoeff : ∀ j, |ah j - a j| ≤ e * |p53Sign (a j)|)
    (heval : |computed - ∑ j : Fin n, ah j * x j| ≤
      g * ∑ j : Fin n, |ah j| * |x j|) :
    |computed - ∑ j : Fin n, a j * x j| ≤
      g * (∑ j : Fin n, |a j| * |x j|) +
      (e + g * e) * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by
  have hdiff :
      |(∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j| ≤
        e * ∑ j : Fin n, |p53Sign (a j)| * |x j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin n, (ah j * x j - a j * x j)| ≤
          ∑ j : Fin n, |ah j * x j - a j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, e * |p53Sign (a j)| * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoeff j) (abs_nonneg _)
      _ = e * ∑ j : Fin n, |p53Sign (a j)| * |x j| := by
        simp only [mul_assoc, Finset.mul_sum]
  have hnorm :
      (∑ j : Fin n, |ah j| * |x j|) ≤
        (∑ j : Fin n, |a j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by
    calc
      _ ≤ ∑ j : Fin n,
          (|a j| * |x j| + e * |p53Sign (a j)| * |x j|) := by
        apply Finset.sum_le_sum
        intro j _
        have htri : |ah j| ≤ |a j| + |ah j - a j| := by
          calc
            |ah j| = |a j + (ah j - a j)| := by congr 1; ring
            _ ≤ |a j| + |ah j - a j| := abs_add_le _ _
        calc
          |ah j| * |x j| ≤ (|a j| + |ah j - a j|) * |x j| :=
            mul_le_mul_of_nonneg_right htri (abs_nonneg _)
          _ ≤ (|a j| + e * |p53Sign (a j)|) * |x j| :=
            mul_le_mul_of_nonneg_right
              (add_le_add le_rfl (hcoeff j)) (abs_nonneg _)
          _ = _ := by ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  calc
    |computed - ∑ j : Fin n, a j * x j| =
        |(computed - ∑ j : Fin n, ah j * x j) +
          ((∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j)| := by
            congr 1
            ring
    _ ≤ |computed - ∑ j : Fin n, ah j * x j| +
          |(∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j| :=
        abs_add_le _ _
    _ ≤ g * (∑ j : Fin n, |ah j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) :=
        add_le_add heval hdiff
    _ ≤ g * ((∑ j : Fin n, |a j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|)) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) :=
        add_le_add (mul_le_mul_of_nonneg_left hnorm hg) le_rfl
    _ = _ := by ring

private lemma p53_coefficient_bound (fp : P53FPModel) {n : ℕ}
    (A Ahat : Fin n → Fin n → ℝ) (η : ℝ)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0) :
    ∀ i j, |Ahat i j - A i j| ≤
      (η * fp.u) * |p53Sign (A i j)| := by
  intro i j
  by_cases hA : A i j = 0
  · simp [hA, hzero i j hA, p53Sign]
  · have hs : |p53Sign (A i j)| = 1 := by
      simp [p53Sign, hA, abs_div, abs_abs]
    simpa [hs] using hpre i j hA

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
  have hcoeff := p53_coefficient_bound fp A Ahat η hpre hzero
  have hvl : NumStability.gammaValid (p53AsFP fp) l := hvalid
  have hgl : 0 ≤ p53Gamma fp.u l := by
    simpa only [p53Gamma, NumStability.gamma, p53AsFP] using
      NumStability.gamma_nonneg (p53AsFP fp) hvl
  have htarget : Nat.clog 2 l + 1 ≤ l := by
    have hp : 0 < l := by omega
    have hcp := NumStability.clog2_le_pred l hp
    omega
  have hvc := NumStability.gammaValid_mono (p53AsFP fp) htarget hvl
  have hgc : 0 ≤ p53Gamma fp.u (Nat.clog 2 l + 1) := by
    simpa only [p53Gamma, NumStability.gamma, p53AsFP] using
      NumStability.gamma_nonneg (p53AsFP fp) hvc
  have hsumprod (i : Fin n) :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) =
      ∑ j : Fin n, Ahat i j * x j := by
    apply p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
    intro j hj
    simp [hzero i j hj]
  have hsumnorm (i : Fin n) :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
      ∑ j : Fin n, |Ahat i j| * |x j| := by
    apply p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
    intro j hj
    simp [hzero i j hj]
  constructor
  · intro i
    have hb := p53_dot_bound fp
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t))
      (schedule.count_le i) hvalid
    rw [hsumprod i, hsumnorm i] at hb
    have heval :
        |p53SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
        p53Gamma fp.u l * ∑ j : Fin n, |Ahat i j| * |x j| := by
      simpa only [p53SparseMatVec] using hb
    exact p53_row_finish (A i) (Ahat i) x
      (p53SparseMatVec fp A Ahat x schedule i)
      (η * fp.u) (p53Gamma fp.u l) hgl (hcoeff i) heval
  · intro i
    have hb := p53_cascade_bound fp
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t))
      (schedule.count_le i) hln.1 hvalid
    rw [hsumprod i, hsumnorm i] at hb
    have heval :
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
        p53Gamma fp.u (Nat.clog 2 l + 1) *
          ∑ j : Fin n, |Ahat i j| * |x j| := by
      simpa only [p53SparseCascadeMatVec] using hb
    exact p53_row_finish (A i) (Ahat i) x
      (p53SparseCascadeMatVec fp A Ahat x schedule i)
      (η * fp.u) (p53Gamma fp.u (Nat.clog 2 l + 1))
      hgc (hcoeff i) heval

end VSCLReuse

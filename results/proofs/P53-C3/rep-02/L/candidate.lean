import VSCLReuse.P53.Definitions
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.Summation.Pairwise.Core

namespace VSCLReuse

open scoped BigOperators

private noncomputable def p53Proxy (fp : P53FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := fun a b => a - b
  fl_mul := fp.fl_mul
  fl_div := fun a b => a / b
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro a b
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_mul := fp.model_mul
  model_div := by
    intro a b _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩
  model_sqrt := by
    intro a _
    exact ⟨0, by simpa using fp.u_nonneg, by ring⟩

private lemma p53_proxy_dot (fp : P53FPModel) (k : ℕ) (a x : Fin k → ℝ) :
    p53Dot fp k a x = NumStability.fl_dotProduct (p53Proxy fp) k a x := by
  rfl

private lemma p53_proxy_pairwise (fp : P53FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    p53PairwiseSum fp r v = NumStability.fl_pairwiseSum (p53Proxy fp) r v := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [p53PairwiseSum, NumStability.fl_pairwiseSum] using
      congrArg₂ fp.fl_add
        (ih (fun i => v ⟨i.val, p53_left_lt r i⟩))
        (ih (fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩))

private lemma p53_proxy_cascade (fp : P53FPModel) (k : ℕ) (v : Fin k → ℝ) :
    p53CascadeSum fp k v =
      NumStability.fl_clog2PairwiseSum (p53Proxy fp) k v := by
  unfold p53CascadeSum NumStability.fl_clog2PairwiseSum
  rw [p53_proxy_pairwise]
  rfl

private lemma p53_dot_error (fp : P53FPModel) (k : ℕ) (a x : Fin k → ℝ)
    (hk : P53GammaValid fp.u k) :
    |p53Dot fp k a x - ∑ i : Fin k, a i * x i| ≤
      p53Gamma fp.u k * ∑ i : Fin k, |a i| * |x i| := by
  simpa only [p53_proxy_dot, p53Gamma, NumStability.gamma,
    NumStability.gammaValid, P53GammaValid, p53Proxy] using
    NumStability.dotProduct_error_bound (p53Proxy fp) k a x hk

private lemma p53_cascade_error (fp : P53FPModel) (k : ℕ) (a x : Fin k → ℝ)
    (hk : P53GammaValid fp.u (Nat.clog 2 k + 1)) :
    |p53CascadeDot fp k a x - ∑ i : Fin k, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 k + 1) *
        ∑ i : Fin k, |a i| * |x i| := by
  let F := p53Proxy fp
  have hγ : NumStability.gammaValid F (Nat.clog 2 k + 1) := hk
  have hc : NumStability.gammaValid F (Nat.clog 2 k) :=
    NumStability.gammaValid_mono F (Nat.le_succ _) hγ
  have h1 : NumStability.gammaValid F 1 :=
    NumStability.gammaValid_mono F (by omega) hγ
  let v : Fin k → ℝ := fun i => fp.fl_mul (a i) (x i)
  obtain ⟨θ, hθ, hsum⟩ :=
    NumStability.clog2PairwiseSum_backward_error F k v hc
  let δ : Fin k → ℝ := fun i => Classical.choose (fp.model_mul (a i) (x i))
  have hδ (i : Fin k) :
      |δ i| ≤ fp.u ∧ v i = a i * x i * (1 + δ i) :=
    Classical.choose_spec (fp.model_mul (a i) (x i))
  let ε : Fin k → ℝ := fun i =>
    Classical.choose (NumStability.gamma_mul F (Nat.clog 2 k) 1
      (θ i) (δ i) (hθ i)
      (le_trans (hδ i).1 (NumStability.u_le_gamma F one_pos h1)) hγ)
  have hε (i : Fin k) : |ε i| ≤ NumStability.gamma F (Nat.clog 2 k + 1) :=
    (Classical.choose_spec (NumStability.gamma_mul F (Nat.clog 2 k) 1
      (θ i) (δ i) (hθ i)
      (le_trans (hδ i).1 (NumStability.u_le_gamma F one_pos h1)) hγ)).1
  have heq (i : Fin k) :
      (1 + δ i) * (1 + θ i) = 1 + ε i := by
    have hh := (Classical.choose_spec (NumStability.gamma_mul F (Nat.clog 2 k) 1
      (θ i) (δ i) (hθ i)
      (le_trans (hδ i).1 (NumStability.u_le_gamma F one_pos h1)) hγ)).2
    simpa only [mul_comm] using hh
  have hback : p53CascadeDot fp k a x =
      ∑ i : Fin k, a i * x i * (1 + ε i) := by
    rw [p53CascadeDot, p53_proxy_cascade]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hδ i).2]
    calc
      a i * x i * (1 + δ i) * (1 + θ i) =
          (a i * x i) * ((1 + δ i) * (1 + θ i)) := by ring
      _ = a i * x i * (1 + ε i) := by rw [heq i]
  have herr : p53CascadeDot fp k a x - ∑ i : Fin k, a i * x i =
      ∑ i : Fin k, a i * x i * ε i := by
    rw [hback, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |∑ i : Fin k, a i * x i * ε i| ≤
        ∑ i : Fin k, |a i * x i * ε i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin k, |a i| * |x i| * |ε i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_mul]
    _ ≤ ∑ i : Fin k, |a i| * |x i| * NumStability.gamma F (Nat.clog 2 k + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hε i)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = p53Gamma fp.u (Nat.clog 2 k + 1) *
        ∑ i : Fin k, |a i| * |x i| := by
      rw [← Finset.sum_mul, mul_comm]
      rfl

private lemma p53_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.univ.filter (fun j => A i j ≠ 0)
  have himage : Finset.univ.image (schedule.col i) = s := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, s, Finset.mem_filter]
    constructor
    · rintro ⟨t, ht⟩
      subst j
      exact schedule.col_nonzero i t
    · intro hj
      exact schedule.covers i j hj
  calc
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
        ∑ j ∈ Finset.univ.image (schedule.col i), f j := by
          rw [Finset.sum_image (schedule.col_injective i).injOn]
    _ = ∑ j ∈ s, f j := by rw [himage]
    _ = ∑ j : Fin n, f j := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hzero : A i j = 0 := by
        by_contra hn
        exact hj (by simp [hn])
      exact hf j hzero

private lemma p53_abs_sign (a : ℝ) :
    |p53Sign a| = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [p53Sign, ha]
  · have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
    simp [p53Sign, ha, abs_div, habs]

private lemma p53_combine_row {n : ℕ} (a ah x : Fin n → ℝ)
    (computed γ e : ℝ) (hγ : 0 ≤ γ) (he : 0 ≤ e)
    (hpre : ∀ j, |ah j - a j| ≤ e * |p53Sign (a j)|)
    (heval : |computed - ∑ j : Fin n, ah j * x j| ≤
      γ * ∑ j : Fin n, |ah j| * |x j|) :
    |computed - ∑ j : Fin n, a j * x j| ≤
      γ * (∑ j : Fin n, |a j| * |x j|) +
        (e + γ * e) * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by
  have hpert :
      |(∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j| ≤
        e * ∑ j : Fin n, |p53Sign (a j)| * |x j| := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ j : Fin n, (ah j * x j - a j * x j)| ≤
          ∑ j : Fin n, |ah j * x j - a j * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, e * (|p53Sign (a j)| * |x j|) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← sub_mul, abs_mul]
        calc
          |ah j - a j| * |x j| ≤
              (e * |p53Sign (a j)|) * |x j| :=
                mul_le_mul_of_nonneg_right (hpre j) (abs_nonneg _)
          _ = e * (|p53Sign (a j)| * |x j|) := by ring
      _ = e * ∑ j : Fin n, |p53Sign (a j)| * |x j| := by
        rw [Finset.mul_sum]
  have hmag (j : Fin n) : |ah j| ≤ |a j| + e * |p53Sign (a j)| := by
    calc
      |ah j| = |a j + (ah j - a j)| := by ring
      _ ≤ |a j| + |ah j - a j| := abs_add_le _ _
      _ ≤ |a j| + e * |p53Sign (a j)| := by
        simpa only [add_comm] using add_le_add_left (hpre j) (|a j|)
  have hsum :
      (∑ j : Fin n, |ah j| * |x j|) ≤
        (∑ j : Fin n, |a j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by
    calc
      (∑ j : Fin n, |ah j| * |x j|) ≤
          ∑ j : Fin n, (|a j| + e * |p53Sign (a j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hmag j) (abs_nonneg _)
      _ = (∑ j : Fin n, |a j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by
            simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  calc
    |computed - ∑ j : Fin n, a j * x j| ≤
        |computed - ∑ j : Fin n, ah j * x j| +
          |(∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j| := by
            convert abs_add_le (computed - ∑ j : Fin n, ah j * x j)
              ((∑ j : Fin n, ah j * x j) - ∑ j : Fin n, a j * x j) using 1
            ring
    _ ≤ γ * (∑ j : Fin n, |ah j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) :=
            add_le_add heval hpert
    _ ≤ γ * ((∑ j : Fin n, |a j| * |x j|) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|)) +
          e * (∑ j : Fin n, |p53Sign (a j)| * |x j|) :=
            add_le_add_left (mul_le_mul_of_nonneg_left hsum hγ) _
    _ = γ * (∑ j : Fin n, |a j| * |x j|) +
          (e + γ * e) * (∑ j : Fin n, |p53Sign (a j)| * |x j|) := by ring

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
  let F := p53Proxy fp
  have hlvalid : NumStability.gammaValid F l := hvalid
  have hcl : Nat.clog 2 l + 1 ≤ l := by
    have hc := NumStability.clog2_le_pred l (by omega : 0 < l)
    omega
  have hclvalid : NumStability.gammaValid F (Nat.clog 2 l + 1) :=
    NumStability.gammaValid_mono F hcl hlvalid
  have hγl : 0 ≤ p53Gamma fp.u l :=
    NumStability.gamma_nonneg F hlvalid
  have hγcl : 0 ≤ p53Gamma fp.u (Nat.clog 2 l + 1) :=
    NumStability.gamma_nonneg F hclvalid
  let e := η * fp.u
  have he : 0 ≤ e := mul_nonneg (le_of_lt hη) fp.u_nonneg
  have hpreall (i j : Fin n) :
      |Ahat i j - A i j| ≤ e * |p53Sign (A i j)| := by
    by_cases haj : A i j = 0
    · simp [e, haj, hzero i j haj, p53Sign]
    · rw [p53_abs_sign]
      simp only [if_neg haj, mul_one]
      exact hpre i j haj
  have hrow (i : Fin n) :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) =
        ∑ j : Fin n, Ahat i j * x j := by
    apply p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
    intro j haj
    simp [hzero i j haj]
  have hrowabs (i : Fin n) :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
        ∑ j : Fin n, |Ahat i j| * |x j| := by
    apply p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
    intro j haj
    simp [hzero i j haj]
  constructor
  · intro i
    let k := schedule.count i
    have hkl : k ≤ l := schedule.count_le i
    have hkvalid : NumStability.gammaValid F k :=
      NumStability.gammaValid_mono F hkl hlvalid
    have hγkl : p53Gamma fp.u k ≤ p53Gamma fp.u l :=
      NumStability.gamma_mono F hkl hlvalid
    have hb := p53_dot_error fp k
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hkvalid
    have heval :
        |p53SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
            p53Gamma fp.u l *
              ∑ j : Fin n, |Ahat i j| * |x j| := by
      change |p53SparseMatVec fp A Ahat x schedule i -
        ∑ t : Fin k, Ahat i (schedule.col i t) * x (schedule.col i t)| ≤
          p53Gamma fp.u k *
            ∑ t : Fin k, |Ahat i (schedule.col i t)| *
              |x (schedule.col i t)| at hb
      rw [hrow i, hrowabs i] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hγkl
        (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
    exact p53_combine_row (A i) (Ahat i) x
      (p53SparseMatVec fp A Ahat x schedule i) (p53Gamma fp.u l) e
      hγl he (hpreall i) heval
  · intro i
    let k := schedule.count i
    have hkl : k ≤ l := schedule.count_le i
    have hckl : Nat.clog 2 k + 1 ≤ Nat.clog 2 l + 1 := by
      exact Nat.add_le_add_right (Nat.clog_mono_right 2 hkl) 1
    have hkvalid : NumStability.gammaValid F (Nat.clog 2 k + 1) :=
      NumStability.gammaValid_mono F hckl hclvalid
    have hγkl : p53Gamma fp.u (Nat.clog 2 k + 1) ≤
        p53Gamma fp.u (Nat.clog 2 l + 1) :=
      NumStability.gamma_mono F hckl hclvalid
    have hb := p53_cascade_error fp k
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hkvalid
    have heval :
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| ≤
            p53Gamma fp.u (Nat.clog 2 l + 1) *
              ∑ j : Fin n, |Ahat i j| * |x j| := by
      change |p53SparseCascadeMatVec fp A Ahat x schedule i -
        ∑ t : Fin k, Ahat i (schedule.col i t) * x (schedule.col i t)| ≤
          p53Gamma fp.u (Nat.clog 2 k + 1) *
            ∑ t : Fin k, |Ahat i (schedule.col i t)| *
              |x (schedule.col i t)| at hb
      rw [hrow i, hrowabs i] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right hγkl
        (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))
    exact p53_combine_row (A i) (Ahat i) x
      (p53SparseCascadeMatVec fp A Ahat x schedule i)
      (p53Gamma fp.u (Nat.clog 2 l + 1)) e
      hγcl he (hpreall i) heval

end VSCLReuse

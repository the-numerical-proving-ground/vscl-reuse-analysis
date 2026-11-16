import VSCLReuse.P51.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p51_mul_error (fp : P51FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  rw [hfl]
  have heq : a * b * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p51_add_error (fp : P51FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * (|a| + |b|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  calc
    |a + b| * |δ| ≤ |a + b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|a| + |b|) * fp.u :=
      mul_le_mul_of_nonneg_right (abs_add_le a b) fp.u_nonneg
    _ = _ := by ring

private lemma p51_fold_eq_dot (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    p51Dot fp k a x =
      Fin.foldl k (fun acc t => fp.fl_add acc (fp.fl_mul (a t) (x t))) 0 := by
  cases k with
  | zero => simp [p51Dot]
  | succ k =>
      simp only [p51Dot, Fin.foldl_succ]
      simp [fp.fl_add_zero]

private lemma p51_step_error (fp : P51FPModel) (c s a b : ℝ) :
    |fp.fl_add c (fp.fl_mul a b) - (s + a * b)| ≤
      (1 + fp.u) * |c - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |a * b| := by
  let r := fp.fl_mul a b
  have hm : |r - a * b| ≤ fp.u * |a * b| := p51_mul_error fp a b
  have ha : |fp.fl_add c r - (c + r)| ≤ fp.u * (|c| + |r|) :=
    p51_add_error fp c r
  have hc : |c| ≤ |s| + |c - s| := by
    have h := abs_add_le s (c - s)
    convert h using 1
    · congr 1; ring
  have hr : |r| ≤ |a * b| + |r - a * b| := by
    have h := abs_add_le (a * b) (r - a * b)
    convert h using 1
    · congr 1; ring
  have ht : |fp.fl_add c r - (s + a * b)| ≤
      |fp.fl_add c r - (c + r)| + |c - s| + |r - a * b| := by
    calc
      |fp.fl_add c r - (s + a * b)| =
          |(fp.fl_add c r - (c + r)) + ((c - s) + (r - a * b))| := by
            congr 1; ring
      _ ≤ |fp.fl_add c r - (c + r)| + |(c - s) + (r - a * b)| :=
        abs_add_le _ _
      _ ≤ _ := by linarith [abs_add_le (c - s) (r - a * b)]
  have hu : 0 ≤ fp.u := fp.u_nonneg
  calc
    |fp.fl_add c r - (s + a * b)| ≤
        |fp.fl_add c r - (c + r)| + |c - s| + |r - a * b| := ht
    _ ≤ fp.u * (|c| + |r|) + |c - s| + |r - a * b| := by linarith
    _ ≤ (1 + fp.u) * |c - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |a * b| := by
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hc),
        mul_nonneg hu (sub_nonneg.mpr hr),
        mul_nonneg hu (sub_nonneg.mpr hm)]

private noncomputable def p51Theta (u : ℝ) (l k : ℕ) : ℝ :=
  (k : ℝ) * u / (1 - (l : ℝ) * u)

private lemma p51_theta_nonneg (u : ℝ) (l k : ℕ) (hu : 0 ≤ u)
    (hv : P51GammaValid u l) : 0 ≤ p51Theta u l k := by
  unfold p51Theta
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (show 0 < 1 - (l : ℝ) * u by
      dsimp [P51GammaValid] at hv
      linarith))

private lemma p51_theta_prefix (u : ℝ) (l k : ℕ) (hu : 0 ≤ u)
    (hv : P51GammaValid u l) (hk : k ≤ l) :
    (1 + u) * p51Theta u l k + u ≤ p51Theta u l (k + 1) := by
  have hD : 0 < 1 - (l : ℝ) * u := by
    dsimp [P51GammaValid] at hv
    linarith
  have hkl : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hk
  unfold p51Theta
  calc
    (1 + u) * ((k : ℝ) * u / (1 - (l : ℝ) * u)) + u =
        ((1 + u) * ((k : ℝ) * u) + u * (1 - (l : ℝ) * u)) /
          (1 - (l : ℝ) * u) := by
            apply (eq_div_iff (ne_of_gt hD)).2
            calc
              ((1 + u) * ((k : ℝ) * u / (1 - (l : ℝ) * u)) + u) *
                  (1 - (l : ℝ) * u) =
                (1 + u) * (((k : ℝ) * u / (1 - (l : ℝ) * u)) *
                  (1 - (l : ℝ) * u)) + u * (1 - (l : ℝ) * u) := by ring
              _ = _ := by rw [div_mul_cancel₀ _ (ne_of_gt hD)]
    _ ≤ ((k + 1 : ℕ) : ℝ) * u / (1 - (l : ℝ) * u) := by
      apply (div_le_div_iff₀ hD hD).2
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hkl) (sq_nonneg u)]

private lemma p51_theta_last (u : ℝ) (l k : ℕ) (hu : 0 ≤ u)
    (hv : P51GammaValid u l) (hl : 2 ≤ l) (hk : 1 ≤ k) :
    2 * u + u ^ 2 ≤ p51Theta u l (k + 1) := by
  have hD : 0 < 1 - (l : ℝ) * u := by
    dsimp [P51GammaValid] at hv
    linarith
  have hl' : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  unfold p51Theta
  apply (le_div_iff₀ hD).2
  have h₁ : 0 ≤ ((k : ℝ) - 1) * u :=
    mul_nonneg (by linarith) hu
  have h₂ : 0 ≤ (2 * (l : ℝ) - 1) * u ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg u)
  have h₃ : 0 ≤ (l : ℝ) * u ^ 3 :=
    mul_nonneg (Nat.cast_nonneg l) (pow_nonneg hu _)
  have heq : (2 * u + u ^ 2) * (1 - (l : ℝ) * u) +
      (((k : ℝ) - 1) * u + (2 * (l : ℝ) - 1) * u ^ 2 + (l : ℝ) * u ^ 3) =
      ((k + 1 : ℕ) : ℝ) * u := by push_cast; ring
  linarith

private lemma p51_theta_one (u : ℝ) (l : ℕ) (hu : 0 ≤ u)
    (hv : P51GammaValid u l) : u ≤ p51Theta u l 1 := by
  have hD : 0 < 1 - (l : ℝ) * u := by
    dsimp [P51GammaValid] at hv
    linarith
  unfold p51Theta
  norm_num
  apply (le_div_iff₀ hD).2
  nlinarith [mul_nonneg (Nat.cast_nonneg l : 0 ≤ (l : ℝ)) (sq_nonneg u)]

private lemma p51_fold_bound (fp : P51FPModel) (l : ℕ)
    (hl : 2 ≤ l) (hv : P51GammaValid fp.u l) :
    ∀ (k : ℕ) (a x : Fin k → ℝ), k ≤ l →
      |Fin.foldl k (fun acc t => fp.fl_add acc (fp.fl_mul (a t) (x t))) 0 -
        ∑ t : Fin k, a t * x t| ≤
        p51Theta fp.u l k * (∑ t : Fin k, |a t| * |x t|) := by
  intro k
  induction k with
  | zero =>
      intro a x hk
      simp [p51Theta]
  | succ k ih =>
      intro a x hk
      let a' : Fin k → ℝ := fun t => a t.castSucc
      let x' : Fin k → ℝ := fun t => x t.castSucc
      have hih := ih a' x' (Nat.le_of_succ_le hk)
      rw [Fin.foldl_succ_last]
      rw [Fin.sum_univ_castSucc (fun t : Fin (k+1) => a t * x t)]
      rw [Fin.sum_univ_castSucc (fun t : Fin (k+1) => |a t| * |x t|)]
      change |fp.fl_add
          (Fin.foldl k (fun acc t => fp.fl_add acc (fp.fl_mul (a' t) (x' t))) 0)
          (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) -
          ((∑ t : Fin k, a' t * x' t) + a (Fin.last k) * x (Fin.last k))| ≤
        p51Theta fp.u l (k + 1) *
          ((∑ t : Fin k, |a' t| * |x' t|) +
            |a (Fin.last k)| * |x (Fin.last k)|)
      by_cases hk0 : k = 0
      · subst k
        have hm := p51_mul_error fp (a (Fin.last 0)) (x (Fin.last 0))
        have hθ := p51_theta_one fp.u l fp.u_nonneg hv
        have hh := le_trans hm (mul_le_mul_of_nonneg_right hθ (abs_nonneg _))
        simpa [a', x', fp.fl_add_zero, abs_mul] using hh
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        let c := Fin.foldl k
          (fun acc t => fp.fl_add acc (fp.fl_mul (a' t) (x' t))) 0
        let s := ∑ t : Fin k, a' t * x' t
        let T := ∑ t : Fin k, |a' t| * |x' t|
        let V := |a (Fin.last k)| * |x (Fin.last k)|
        have hT : 0 ≤ T := Finset.sum_nonneg (fun t _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))
        have hV : 0 ≤ V := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hs : |s| ≤ T := by
          simpa only [T, s, abs_mul] using
            (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun t : Fin k => a' t * x' t))
        have hstep := p51_step_error fp c s (a (Fin.last k)) (x (Fin.last k))
        rw [abs_mul] at hstep
        have hprefix := p51_theta_prefix fp.u l k fp.u_nonneg hv
          (Nat.le_of_succ_le hk)
        have hlast := p51_theta_last fp.u l k fp.u_nonneg hv hl hk1
        have h1 : (1 + fp.u) * |c - s| ≤
            (1 + fp.u) * (p51Theta fp.u l k * T) :=
          mul_le_mul_of_nonneg_left hih (by linarith [fp.u_nonneg])
        have h2 : fp.u * |s| ≤ fp.u * T :=
          mul_le_mul_of_nonneg_left hs fp.u_nonneg
        have h3 : ((1 + fp.u) * p51Theta fp.u l k + fp.u) * T ≤
            p51Theta fp.u l (k + 1) * T :=
          mul_le_mul_of_nonneg_right hprefix hT
        have h4 : (2 * fp.u + fp.u ^ 2) * V ≤
            p51Theta fp.u l (k + 1) * V :=
          mul_le_mul_of_nonneg_right hlast hV
        dsimp [c, s, T, V] at *
        nlinarith [hstep, h1, h2, h3, h4]

private lemma p51_dot_bound (fp : P51FPModel) (l k : ℕ)
    (hl : 2 ≤ l) (hv : P51GammaValid fp.u l) (hk : k ≤ l)
    (a x : Fin k → ℝ) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p51Gamma fp.u l * (∑ t : Fin k, |a t| * |x t|) := by
  have hD : 0 ≤ 1 - (l : ℝ) * fp.u := by
    dsimp [P51GammaValid] at hv
    linarith
  have hkl : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hk
  have htheta : p51Theta fp.u l k ≤ p51Gamma fp.u l := by
    unfold p51Theta p51Gamma
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hkl fp.u_nonneg) hD
  have hsum : 0 ≤ ∑ t : Fin k, |a t| * |x t| :=
    Finset.sum_nonneg (fun t _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [p51_fold_eq_dot]
  exact (p51_fold_bound fp l hl hv k a x hk).trans
    (mul_le_mul_of_nonneg_right htheta hsum)

private lemma p51_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.image (schedule.col i) Finset.univ
  calc
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
        ∑ j ∈ s, f j := by
          symm
          exact Finset.sum_image (fun _ _ _ _ h => schedule.col_injective i h)
    _ = ∑ j : Fin n, f j := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro j hj hnot
      apply hf
      by_contra hA
      apply hnot
      obtain ⟨t, ht⟩ := schedule.covers i j hA
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht⟩

private lemma p51_sign_abs (a : ℝ) : |p51Sign a| = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [p51Sign, ha]
  · have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
    simp [p51Sign, ha, abs_div, habs]

/-- Complete componentwise sparse matrix-vector result of Lemma 3.2. -/
theorem p51_c2_lemma32 {m n l : ℕ} (fp : P51FPModel)
    (A Ahat : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P51SparseSchedule A l) (η : ℝ)
    (hln : 2 ≤ l ∧ l < n) (hvalid : P51GammaValid fp.u l)
    (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin m) :
    |p51SparseMatVec fp A Ahat x schedule i - ∑ j : Fin n, A i j * x j| ≤
      p51Gamma fp.u l * (∑ j : Fin n, |A i j| * |x j|) +
      (η * fp.u + p51Gamma fp.u l * (η * fp.u)) *
        (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
  -- PROOF_START P51-C2-H001
  have hcoeff : ∀ j : Fin n,
      |Ahat i j - A i j| ≤ η * fp.u * |p51Sign (A i j)| := by
    intro j
    by_cases ha : A i j = 0
    · simp [ha, hzero i j ha, p51Sign]
    · simpa [p51_sign_abs, ha] using hpre i j ha
  have hhat : ∀ j : Fin n,
      |Ahat i j| ≤ |A i j| + η * fp.u * |p51Sign (A i j)| := by
    intro j
    have h := abs_add_le (A i j) (Ahat i j - A i j)
    have heq : A i j + (Ahat i j - A i j) = Ahat i j := by ring
    rw [heq] at h
    linarith [hcoeff j]
  have hsumhat :
      (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) =
      ∑ j : Fin n, Ahat i j * x j := by
    exact p51_schedule_sum A schedule i (fun j => Ahat i j * x j)
      (by intro j hj; simp [hzero i j hj])
  have hsumhatabs :
      (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
      ∑ j : Fin n, |Ahat i j| * |x j| := by
    exact p51_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
      (by intro j hj; simp [hzero i j hj])
  have hround :
      |p51SparseMatVec fp A Ahat x schedule i -
        ∑ j : Fin n, Ahat i j * x j| ≤
      p51Gamma fp.u l * (∑ j : Fin n, |Ahat i j| * |x j|) := by
    have h := p51_dot_bound fp l (schedule.count i) hln.1 hvalid
      (schedule.count_le i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t))
    rw [hsumhat, hsumhatabs] at h
    simpa only [p51SparseMatVec] using h
  have hhat_sum :
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
      (∑ j : Fin n, |A i j| * |x j|) +
        η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
    calc
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
          ∑ j : Fin n,
            (|A i j| + η * fp.u * |p51Sign (A i j)|) * |x j| := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_mul_of_nonneg_right (hhat j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A i j| * |x j|) +
          η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
            simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  have hdiff_eq :
      (∑ j : Fin n, Ahat i j * x j) -
        (∑ j : Fin n, A i j * x j) =
      ∑ j : Fin n, (Ahat i j - A i j) * x j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiff :
      |(∑ j : Fin n, Ahat i j * x j) -
        (∑ j : Fin n, A i j * x j)| ≤
      η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
    rw [hdiff_eq]
    calc
      |∑ j : Fin n, (Ahat i j - A i j) * x j| ≤
          ∑ j : Fin n, |(Ahat i j - A i j) * x j| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n,
          (η * fp.u * |p51Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hcoeff j) (abs_nonneg _)
      _ = η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
  have hgamma : 0 ≤ p51Gamma fp.u l := by
    simpa only [p51Theta, p51Gamma] using
      p51_theta_nonneg fp.u l l fp.u_nonneg hvalid
  calc
    |p51SparseMatVec fp A Ahat x schedule i -
        ∑ j : Fin n, A i j * x j| =
      |(p51SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j) +
        ((∑ j : Fin n, Ahat i j * x j) -
          (∑ j : Fin n, A i j * x j))| := by congr 1; ring
    _ ≤ |p51SparseMatVec fp A Ahat x schedule i -
          ∑ j : Fin n, Ahat i j * x j| +
        |(∑ j : Fin n, Ahat i j * x j) -
          (∑ j : Fin n, A i j * x j)| := abs_add_le _ _
    _ ≤ p51Gamma fp.u l * (∑ j : Fin n, |Ahat i j| * |x j|) +
        η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) :=
          add_le_add hround hdiff
    _ ≤ p51Gamma fp.u l *
          ((∑ j : Fin n, |A i j| * |x j|) +
            η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|)) +
        η * fp.u * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hhat_sum hgamma) le_rfl
    _ = _ := by ring

end VSCLReuse

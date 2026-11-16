import VSCLReuse.P51.Definitions

namespace VSCLReuse

open scoped BigOperators


private theorem p51_mul_error (fp : P51FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * (|a| * |x|) := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a x
  rw [hmul]
  have h : a * x * (1 + δ) - a * x = (a * x) * δ := by ring
  rw [h, abs_mul, abs_mul]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg a) (abs_nonneg x))

private theorem p51_mul_abs (fp : P51FPModel) (a x : ℝ) :
    |fp.fl_mul a x| ≤ (1 + fp.u) * (|a| * |x|) := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a x
  rw [hmul, abs_mul, abs_mul]
  have hδ' : |1 + δ| ≤ 1 + fp.u := by
    have := abs_add_le (1 : ℝ) δ
    rw [abs_one] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hδ' (mul_nonneg (abs_nonneg a) (abs_nonneg x))]

private theorem p51_add_error (fp : P51FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * (|a| + |b|) := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  rw [hadd]
  have h : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [h, abs_mul]
  calc
    |a + b| * |δ| ≤ |a + b| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|a| + |b|) * fp.u :=
      mul_le_mul_of_nonneg_right (abs_add_le a b) fp.u_nonneg
    _ = fp.u * (|a| + |b|) := by ring

private theorem p51_step_error (fp : P51FPModel) (v s a x : ℝ) :
    |fp.fl_add v (fp.fl_mul a x) - (s + a * x)| ≤
      (1 + fp.u) * |v - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * (|a| * |x|) := by
  have hm := p51_mul_error fp a x
  have hma := p51_mul_abs fp a x
  have ha := p51_add_error fp v (fp.fl_mul a x)
  have hv : |v| ≤ |v - s| + |s| := by
    convert abs_add_le (v - s) s using 1 <;> ring
  have htri :
      |fp.fl_add v (fp.fl_mul a x) - (s + a * x)| ≤
        |fp.fl_add v (fp.fl_mul a x) - (v + fp.fl_mul a x)| +
        |fp.fl_mul a x - a * x| + |v - s| := by
    have heq : fp.fl_add v (fp.fl_mul a x) - (s + a * x) =
        (fp.fl_add v (fp.fl_mul a x) - (v + fp.fl_mul a x)) +
          ((fp.fl_mul a x - a * x) + (v - s)) := by ring
    rw [heq]
    have h := abs_add_le
      (fp.fl_add v (fp.fl_mul a x) - (v + fp.fl_mul a x))
      ((fp.fl_mul a x - a * x) + (v - s))
    have h' := abs_add_le (fp.fl_mul a x - a * x) (v - s)
    linarith
  have huabs : 0 ≤ |a| * |x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hv fp.u_nonneg,
    mul_le_mul_of_nonneg_left hma fp.u_nonneg]

private theorem p51_fold_error (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (b v : ℝ)
    (hinit : |v - b| ≤ fp.u * |b|) :
    |Fin.foldl k (fun acc t => fp.fl_add acc (fp.fl_mul (a t) (x t))) v -
        (b + ∑ t : Fin k, a t * x t)| ≤
      ((1 + fp.u) ^ (k + 1) - 1) *
        (|b| + ∑ t : Fin k, |a t| * |x t|) := by
  induction k with
  | zero =>
      simpa [Fin.foldl_zero] using hinit
  | succ k ih =>
      let aa : Fin k → ℝ := fun t => a t.castSucc
      let xx : Fin k → ℝ := fun t => x t.castSucc
      let w : ℝ := Fin.foldl k
        (fun acc t => fp.fl_add acc (fp.fl_mul (aa t) (xx t))) v
      let s : ℝ := b + ∑ t : Fin k, aa t * xx t
      let B : ℝ := |b| + ∑ t : Fin k, |aa t| * |xx t|
      let q : ℝ := |a (Fin.last k)| * |x (Fin.last k)|
      let C : ℝ := (1 + fp.u) ^ (k + 1) - 1
      let D : ℝ := (1 + fp.u) ^ (k + 1 + 1) - 1
      have hprev : |w - s| ≤ C * B := ih aa xx
      have hs : |s| ≤ B := by
        dsimp [s, B]
        calc
          |b + ∑ t : Fin k, aa t * xx t| ≤
              |b| + |∑ t : Fin k, aa t * xx t| := abs_add_le _ _
          _ ≤ |b| + ∑ t : Fin k, |aa t| * |xx t| := by
            gcongr
            calc
              |∑ t : Fin k, aa t * xx t| ≤
                  ∑ t : Fin k, |aa t * xx t| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ t : Fin k, |aa t| * |xx t| := by simp [abs_mul]
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have hC : fp.u ≤ C := by
        have hpow : 1 ≤ (1 + fp.u) ^ k :=
          one_le_pow₀ (by linarith [fp.u_nonneg])
        have hh := mul_nonneg (show 0 ≤ (1 + fp.u) ^ k - 1 by linarith)
          (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
        dsimp [C]
        rw [pow_succ]
        nlinarith
      have hD : D = (1 + fp.u) * C + fp.u := by
        dsimp [D, C]
        rw [pow_succ]
        ring
      have hstep := p51_step_error fp w s (a (Fin.last k)) (x (Fin.last k))
      have hcoef : 2 * fp.u + fp.u ^ 2 ≤ (1 + fp.u) * C + fp.u := by
        nlinarith [mul_nonneg (show 0 ≤ C - fp.u by linarith) fp.u_nonneg]
      have hgoal :
          |fp.fl_add w (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) -
              (s + a (Fin.last k) * x (Fin.last k))| ≤ D * (B + q) := by
        rw [hD]
        have h1 := mul_le_mul_of_nonneg_left hprev
          (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
        have h2 := mul_le_mul_of_nonneg_left hs fp.u_nonneg
        have h3 := mul_le_mul_of_nonneg_right hcoef hq
        dsimp [q] at h3
        calc
          _ ≤ (1 + fp.u) * |w - s| + fp.u * |s| +
              (2 * fp.u + fp.u ^ 2) * q := hstep
          _ ≤ (1 + fp.u) * (C * B) + fp.u * B +
              (2 * fp.u + fp.u ^ 2) * q := by linarith
          _ ≤ ((1 + fp.u) * C + fp.u) * (B + q) := by nlinarith [h3]
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc, aa, xx,
        w, s, B, q, D, add_assoc] using hgoal

private theorem p51_dot_pow_error (fp : P51FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      ((1 + fp.u) ^ k - 1) * (∑ t : Fin k, |a t| * |x t|) := by
  cases k with
  | zero => simp [p51Dot]
  | succ k =>
      have h := p51_fold_error fp k
        (fun t : Fin k => a t.succ) (fun t : Fin k => x t.succ)
        (a 0 * x 0) (fp.fl_mul (a 0) (x 0))
        (by simpa only [abs_mul] using p51_mul_error fp (a 0) (x 0))
      simpa only [p51Dot, Fin.sum_univ_succ, abs_mul] using h

private theorem p51_pow_recip_bound (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hfactor :
          (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤
            1 - (k : ℝ) * u := by
        have hh : 0 ≤ ((k : ℝ) + 1) * u ^ 2 := by positivity
        push_cast
        nlinarith
      calc
        (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ k * ((1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hfactor (pow_nonneg (by linarith) _)
        _ ≤ 1 := ih

private theorem p51_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P51GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p51Gamma u k := by
  have hden : 0 < 1 - (k : ℝ) * u := by
    dsimp [P51GammaValid] at hk
    linarith
  have hp := p51_pow_recip_bound u hu k
  unfold p51Gamma
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem p51_dot_gamma_error (fp : P51FPModel) (k l : ℕ)
    (hkl : k ≤ l) (hl : P51GammaValid fp.u l)
    (a x : Fin k → ℝ) :
    |p51Dot fp k a x - ∑ t : Fin k, a t * x t| ≤
      p51Gamma fp.u l * (∑ t : Fin k, |a t| * |x t|) := by
  have hbase := p51_dot_pow_error fp k a x
  have hpow : (1 + fp.u) ^ k ≤ (1 + fp.u) ^ l :=
    pow_le_pow_right₀ (by linarith [fp.u_nonneg]) hkl
  have hgam := p51_pow_le_gamma fp.u fp.u_nonneg l hl
  have hs : 0 ≤ ∑ t : Fin k, |a t| * |x t| := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_right (by linarith) hs)

private theorem p51_sparse_sum {m n l : ℕ}
    (A : Fin m → Fin n → ℝ) (schedule : P51SparseSchedule A l)
    (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  classical
  let s : Finset (Fin n) := Finset.univ.image (schedule.col i)
  have hinj : Set.InjOn (schedule.col i) (Finset.univ : Finset (Fin (schedule.count i))) := by
    intro t _ t' _ h
    exact schedule.col_injective i h
  have hzero : ∀ j : Fin n, j ∉ s → A i j = 0 := by
    intro j hj
    by_contra hA
    obtain ⟨t, ht⟩ := schedule.covers i j hA
    have hmem : j ∈ s := by
      simp only [s, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨t, ht⟩
    exact hj hmem
  calc
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
        ∑ j ∈ s, f j := by
          simpa only [s] using (Finset.sum_image (f := f) hinj).symm
    _ = ∑ j : Fin n, f j := by
      exact Finset.sum_subset (by simp [s]) (by
        intro j _ hj
        exact hf j (hzero j hj))

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
  let e : ℝ := η * fp.u
  let g : ℝ := p51Gamma fp.u l
  let S : ℝ := ∑ j : Fin n, |p51Sign (A i j)| * |x j|
  let T : ℝ := ∑ j : Fin n, |A i j| * |x j|
  let H : ℝ := ∑ j : Fin n, |Ahat i j| * |x j|
  let y : ℝ := ∑ j : Fin n, A i j * x j
  let yh : ℝ := ∑ j : Fin n, Ahat i j * x j
  let v : ℝ := p51SparseMatVec fp A Ahat x schedule i
  have he : 0 ≤ e := mul_nonneg hη.le fp.u_nonneg
  have hg : 0 ≤ g := by
    have hd : 0 < 1 - (l : ℝ) * fp.u := by
      dsimp [P51GammaValid] at hvalid
      linarith
    dsimp [g, p51Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg l) fp.u_nonneg) hd.le
  have hsign (j : Fin n) (hj : A i j ≠ 0) :
      |p51Sign (A i j)| = 1 := by
    have habs : |A i j| ≠ 0 := abs_ne_zero.mpr hj
    simp [p51Sign, hj, abs_div, habs]
  have hcoef (j : Fin n) :
      |Ahat i j - A i j| ≤ e * |p51Sign (A i j)| := by
    by_cases hj : A i j = 0
    · simp [hj, hzero i j hj, p51Sign, e]
    · rw [hsign j hj, mul_one]
      exact hpre i j hj
  have hhat (j : Fin n) :
      |Ahat i j| ≤ |A i j| + e * |p51Sign (A i j)| := by
    have ht : |Ahat i j| ≤ |Ahat i j - A i j| + |A i j| := by
      have h := abs_add_le (Ahat i j - A i j) (A i j)
      convert h using 1 <;> ring
    linarith [hcoef j]
  have hH : H ≤ T + e * S := by
    dsimp [H, T, S]
    calc
      (∑ j : Fin n, |Ahat i j| * |x j|) ≤
          ∑ j : Fin n, (|A i j| + e * |p51Sign (A i j)|) * |x j| := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_right (hhat j) (abs_nonneg _)
      _ = (∑ j : Fin n, |A i j| * |x j|) +
          e * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
            simp_rw [add_mul, mul_assoc]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdiff : |yh - y| ≤ e * S := by
    dsimp [yh, y, S]
    calc
      |(∑ j : Fin n, Ahat i j * x j) - ∑ j : Fin n, A i j * x j| =
          |∑ j : Fin n, (Ahat i j - A i j) * x j| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            congr 1
            ext j
            ring
      _ ≤ ∑ j : Fin n, |(Ahat i j - A i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |Ahat i j - A i j| * |x j| := by simp [abs_mul]
      _ ≤ ∑ j : Fin n, (e * |p51Sign (A i j)|) * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcoef j) (abs_nonneg _)
      _ = e * (∑ j : Fin n, |p51Sign (A i j)| * |x j|) := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
  have hround : |v - yh| ≤ g * H := by
    have hdot := p51_dot_gamma_error fp (schedule.count i) l
      (schedule.count_le i) hvalid
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t))
    have hsum : (∑ t : Fin (schedule.count i),
        Ahat i (schedule.col i t) * x (schedule.col i t)) = yh := by
      exact p51_sparse_sum A schedule i (fun j => Ahat i j * x j)
        (by intro j hj; simp [hzero i j hj])
    have hsumabs : (∑ t : Fin (schedule.count i),
        |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) = H := by
      exact p51_sparse_sum A schedule i (fun j => |Ahat i j| * |x j|)
        (by intro j hj; simp [hzero i j hj])
    simpa only [v, yh, H, g, p51SparseMatVec, hsum, hsumabs] using hdot
  have htri : |v - y| ≤ |v - yh| + |yh - y| := by
    have h := abs_add_le (v - yh) (yh - y)
    convert h using 1 <;> ring
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hfinal : |v - y| ≤ g * T + (e + g * e) * S := by
    have hmul := mul_le_mul_of_nonneg_left hH hg
    nlinarith [hround, hdiff, htri, hmul]
  simpa only [v, y, g, T, S, e] using hfinal

end VSCLReuse

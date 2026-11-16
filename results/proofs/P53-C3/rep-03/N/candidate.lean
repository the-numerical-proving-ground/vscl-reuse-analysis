import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p53_u_nonneg (fp : P53FPModel) : 0 ≤ fp.u := fp.u_nonneg

private lemma p53_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hv : P53GammaValid u k) : 0 ≤ p53Gamma u k := by
  unfold p53Gamma P53GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private lemma p53_gamma_mono (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hv : P53GammaValid u b) :
    p53Gamma u a ≤ p53Gamma u b := by
  unfold p53Gamma P53GammaValid at *
  have hca : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have ha : 0 < 1 - (a : ℝ) * u := by nlinarith
  have hb : 0 < 1 - (b : ℝ) * u := by linarith
  apply (div_le_div_iff₀ ha hb).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hca) hu]

private lemma p53_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hv : P53GammaValid u (k + 1)) :
    (1 + u) * p53Gamma u k + u ≤ p53Gamma u (k + 1) := by
  unfold p53Gamma P53GammaValid at *
  push_cast at hv ⊢
  have hk : 0 < 1 - (k : ℝ) * u := by
    nlinarith
  have hks : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
  have heq : (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
      (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
    have hne : 1 - u * (k : ℝ) ≠ 0 := by nlinarith
    field_simp [hne]
    ring
  rw [heq]
  apply (div_le_div_iff₀ hk hks).2
  nlinarith [mul_nonneg (Nat.cast_nonneg k) hu, sq_nonneg u]

private lemma p53_add_error (fp : P53FPModel)
    (a b A B S T g : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hA : |A| ≤ S) (hB : |B| ≤ T) (hg : 0 ≤ g)
    (ha : |a - A| ≤ g * S) (hb : |b - B| ≤ g * T) :
    |fp.fl_add a b - (A + B)| ≤
      ((1 + fp.u) * g + fp.u) * (S + T) := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add a b
  have hδ' : |δ| ≤ fp.u := hδ
  have h0 : |fp.fl_add a b - (A + B)| ≤
      |a - A| + |b - B| + fp.u * (|a| + |b|) := by
    rw [heq]
    have he : (a + b) * (1 + δ) - (A + B) =
        ((a - A) + (b - B)) + δ * (a + b) := by ring
    rw [he]
    calc
      |(a - A) + (b - B) + δ * (a + b)| ≤
          |a - A| + |b - B| + |δ| * (|a| + |b|) := by
            calc
              _ ≤ |(a - A) + (b - B)| + |δ * (a + b)| := abs_add_le _ _
              _ ≤ |a - A| + |b - B| + |δ| * (|a| + |b|) := by
                rw [abs_mul]
                have h1 := abs_add_le (a - A) (b - B)
                have h2 := abs_add_le a b
                gcongr
      _ ≤ _ := by gcongr
  have haa : |a| ≤ S + |a - A| := by
    calc
      |a| = |(a - A) + A| := by ring
      _ ≤ |a - A| + |A| := abs_add_le _ _
      _ ≤ S + |a - A| := by linarith
  have hbb : |b| ≤ T + |b - B| := by
    calc
      |b| = |(b - B) + B| := by ring
      _ ≤ |b - B| + |B| := abs_add_le _ _
      _ ≤ T + |b - B| := by linarith
  have hu1 := mul_le_mul_of_nonneg_left (add_le_add haa hbb) fp.u_nonneg
  have hu2 := mul_le_mul_of_nonneg_left (add_le_add ha hb) fp.u_nonneg
  nlinarith

private lemma p53_mul_error (fp : P53FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * (|a| * |x|) := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul a x
  rw [heq]
  have he : a * x * (1 + δ) - a * x = (a * x) * δ := by ring
  rw [he, abs_mul, abs_mul]
  have := mul_le_mul_of_nonneg_left hδ
    (mul_nonneg (abs_nonneg a) (abs_nonneg x))
  nlinarith

private lemma p53_valid_of_le (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hv : P53GammaValid u b) : P53GammaValid u a := by
  unfold P53GammaValid at *
  have h : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hu]

private lemma p53_gamma_one_ge_u (u : ℝ) (hu : 0 ≤ u)
    (hv : P53GammaValid u 1) : u ≤ p53Gamma u 1 := by
  have h := p53_gamma_step u hu 0 hv
  simpa [p53Gamma] using h

private lemma p53_pairwise_split (r : ℕ)
    (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, f i) =
      (∑ i : Fin (2 ^ r), f ⟨i.val, p53_left_lt r i⟩) +
      (∑ i : Fin (2 ^ r), f ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have he : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by simp [pow_succ, mul_two]
  let g : Fin (2 ^ r + 2 ^ r) → ℝ := fun i => f (Fin.cast he.symm i)
  calc
    (∑ i, f i) = ∑ i, g i := by
      exact (Equiv.sum_comp (finCongr he.symm) f).symm
    _ = (∑ i : Fin (2 ^ r), g (Fin.castAdd (2 ^ r) i)) +
        (∑ i : Fin (2 ^ r), g (Fin.natAdd (2 ^ r) i)) := Fin.sum_univ_add g
    _ = _ := by
      simp only [g, Fin.cast, Fin.castAdd, Fin.natAdd, Fin.val_castLE]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      exact Fin.ext (by simp [add_comm])

private lemma p53_pairwise_error (fp : P53FPModel) (r : ℕ)
    (v w : Fin (2 ^ r) → ℝ)
    (hv : P53GammaValid fp.u (r + 1))
    (hleaf : ∀ i, |v i - w i| ≤ fp.u * |w i|) :
    |p53PairwiseSum fp r v - ∑ i, w i| ≤
      p53Gamma fp.u (r + 1) * ∑ i, |w i| := by
  induction r with
  | zero =>
      have hu := p53_gamma_one_ge_u fp.u fp.u_nonneg hv
      simpa [p53PairwiseSum, Fin.sum_univ_one] using
        (le_trans (hleaf (0 : Fin 1))
          (mul_le_mul_of_nonneg_right hu (abs_nonneg (w 0))))
  | succ r ih =>
      let vL : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
      let vR : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      let wL : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val, p53_left_lt r i⟩
      let wR : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      have hc : P53GammaValid fp.u (r + 1) :=
        p53_valid_of_le fp.u fp.u_nonneg (by omega) hv
      have hL := ih vL wL hc (by intro i; exact hleaf _)
      have hR := ih vR wR hc (by intro i; exact hleaf _)
      have hSL : 0 ≤ ∑ i, |wL i| := Finset.sum_nonneg (by intros; positivity)
      have hSR : 0 ≤ ∑ i, |wR i| := Finset.sum_nonneg (by intros; positivity)
      have hAL : |∑ i, wL i| ≤ ∑ i, |wL i| :=
        Finset.abs_sum_le_sum_abs wL Finset.univ
      have hAR : |∑ i, wR i| ≤ ∑ i, |wR i| :=
        Finset.abs_sum_le_sum_abs wR Finset.univ
      have hg : 0 ≤ p53Gamma fp.u (r + 1) :=
        p53_gamma_nonneg fp.u fp.u_nonneg (r + 1) hc
      have hadd := p53_add_error fp
        (p53PairwiseSum fp r vL) (p53PairwiseSum fp r vR)
        (∑ i, wL i) (∑ i, wR i)
        (∑ i, |wL i|) (∑ i, |wR i|)
        (p53Gamma fp.u (r + 1)) hSL hSR hAL hAR hg hL hR
      have hstep := p53_gamma_step fp.u fp.u_nonneg (r + 1) hv
      have hS : 0 ≤ (∑ i, |wL i|) + (∑ i, |wR i|) := add_nonneg hSL hSR
      simpa only [p53PairwiseSum, p53_pairwise_split r w,
        p53_pairwise_split r (fun i => |w i|)] using
        (le_trans hadd (mul_le_mul_of_nonneg_right hstep hS))

private noncomputable def p53FoldDot (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) : ℝ :=
  Fin.foldl k (fun acc i => fp.fl_add acc (fp.fl_mul (a i) (x i))) 0

private lemma p53_fold_dot_error (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (hv : P53GammaValid fp.u k) :
    |p53FoldDot fp k a x - ∑ i, a i * x i| ≤
      p53Gamma fp.u k * ∑ i, |a i| * |x i| := by
  induction k with
  | zero => simp [p53FoldDot, p53Gamma, Fin.foldl_zero]
  | succ k ih =>
      let a' : Fin k → ℝ := fun i => a i.castSucc
      let x' : Fin k → ℝ := fun i => x i.castSucc
      let al : ℝ := a (Fin.last k)
      let xl : ℝ := x (Fin.last k)
      have hprev_valid : P53GammaValid fp.u k :=
        p53_valid_of_le fp.u fp.u_nonneg (by omega) hv
      have hprev := ih a' x' hprev_valid
      have hmul := p53_mul_error fp al xl
      have hfold : p53FoldDot fp (k + 1) a x =
          fp.fl_add (p53FoldDot fp k a' x') (fp.fl_mul al xl) := by
        simp only [p53FoldDot, Fin.foldl_succ_last]
        rfl
      have hsum : (∑ i, a i * x i) = (∑ i, a' i * x' i) + al * xl := by
        simpa only [a', x', al, xl] using
          (Fin.sum_univ_castSucc (fun i : Fin (k + 1) => a i * x i))
      have hsumabs : (∑ i, |a i| * |x i|) =
          (∑ i, |a' i| * |x' i|) + |al| * |xl| := by
        simpa only [a', x', al, xl] using
          (Fin.sum_univ_castSucc (fun i : Fin (k + 1) => |a i| * |x i|))
      cases k with
      | zero =>
          have hu := p53_gamma_one_ge_u fp.u fp.u_nonneg hv
          rw [hfold, hsum, hsumabs]
          simp only [p53FoldDot, Fin.foldl_zero, fp.fl_add_zero,
            Fin.sum_univ_zero, zero_add]
          exact le_trans hmul (mul_le_mul_of_nonneg_right hu
            (mul_nonneg (abs_nonneg al) (abs_nonneg xl)))
      | succ k =>
          have hvalid_one : P53GammaValid fp.u 1 :=
            p53_valid_of_le fp.u fp.u_nonneg (by omega) hv
          have hule : fp.u ≤ p53Gamma fp.u (k + 1) :=
            (p53_gamma_one_ge_u fp.u fp.u_nonneg hvalid_one).trans
              (p53_gamma_mono fp.u fp.u_nonneg (by omega) hprev_valid)
          have hmul' : |fp.fl_mul al xl - al * xl| ≤
              p53Gamma fp.u (k + 1) * (|al| * |xl|) :=
            hmul.trans (mul_le_mul_of_nonneg_right hule
              (mul_nonneg (abs_nonneg al) (abs_nonneg xl)))
          have hS : 0 ≤ ∑ i, |a' i| * |x' i| :=
            Finset.sum_nonneg (by intros; positivity)
          have hT : 0 ≤ |al| * |xl| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have hA : |∑ i, a' i * x' i| ≤ ∑ i, |a' i| * |x' i| := by
            simpa only [abs_mul] using
              (Finset.abs_sum_le_sum_abs (fun i : Fin (k + 1) => a' i * x' i)
                Finset.univ)
          have hB : |al * xl| ≤ |al| * |xl| := by rw [abs_mul]
          have hg := p53_gamma_nonneg fp.u fp.u_nonneg (k + 1) hprev_valid
          have hadd := p53_add_error fp
            (p53FoldDot fp (k + 1) a' x') (fp.fl_mul al xl)
            (∑ i, a' i * x' i) (al * xl)
            (∑ i, |a' i| * |x' i|) (|al| * |xl|)
            (p53Gamma fp.u (k + 1)) hS hT hA hB hg hprev hmul'
          have hstep := p53_gamma_step fp.u fp.u_nonneg (k + 1) hv
          rw [hfold, hsum, hsumabs]
          exact hadd.trans (mul_le_mul_of_nonneg_right hstep (add_nonneg hS hT))

private lemma p53_dot_eq_fold (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) : p53Dot fp k a x = p53FoldDot fp k a x := by
  cases k with
  | zero => simp [p53Dot, p53FoldDot, Fin.foldl_zero]
  | succ k =>
      simp only [p53Dot, p53FoldDot, Fin.foldl_succ, fp.fl_add_zero]

private lemma p53_clog_succ_le (l : ℕ) (hl : 2 ≤ l) :
    Nat.clog 2 l + 1 ≤ l := by
  have h : l ≤ 2 ^ (l - 1) := by
    have hc := Nat.choose_succ_le_two_pow (l - 1) 1
    simpa [Nat.choose_one_right, Nat.sub_add_cancel (by omega : 1 ≤ l)] using hc
  have hc := Nat.clog_le_of_le_pow h
  omega

private lemma p53_pad_sum (n m : ℕ) (hnm : n ≤ m) (v : Fin n → ℝ) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i, v i := by
  let f : ℕ → ℝ := fun k => if h : k < n then v ⟨k, h⟩ else 0
  have hleft : (∑ i : Fin m, p53ScalarPad n m v i) =
      ∑ k ∈ Finset.range m, f k := by
    rw [← Fin.sum_univ_eq_sum_range f m]
    rfl
  have hright : (∑ i : Fin n, v i) = ∑ k ∈ Finset.range n, f k := by
    rw [← Fin.sum_univ_eq_sum_range f n]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, i.isLt]
  rw [hleft, hright]
  have hm : m = n + (m - n) := by omega
  rw [hm, Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range (m - n), f (n + k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [f]
  rw [hz, add_zero]

private lemma p53_cascade_dot_error (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ)
    (hv : P53GammaValid fp.u (Nat.clog 2 k + 1)) :
    |p53CascadeDot fp k a x - ∑ i, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 k + 1) *
        ∑ i, |a i| * |x i| := by
  let w : Fin (2 ^ Nat.clog 2 k) → ℝ :=
    p53ZeroPad k (fun i => a i * x i)
  let v : Fin (2 ^ Nat.clog 2 k) → ℝ :=
    p53ZeroPad k (fun i => fp.fl_mul (a i) (x i))
  have hleaf : ∀ i, |v i - w i| ≤ fp.u * |w i| := by
    intro i
    by_cases hi : i.val < k
    · simpa [v, w, p53ZeroPad, p53ScalarPad, hi, abs_mul] using
        (p53_mul_error fp (a ⟨i.val, hi⟩) (x ⟨i.val, hi⟩))
    · simp [v, w, p53ZeroPad, p53ScalarPad, hi]
  have hpad : k ≤ 2 ^ Nat.clog 2 k := Nat.le_pow_clog (by omega) k
  have hsum : (∑ i, w i) = ∑ i, a i * x i := by
    simpa only [w, p53ZeroPad] using
      (p53_pad_sum k (2 ^ Nat.clog 2 k) hpad (fun i => a i * x i))
  have habsum : (∑ i, |w i|) = ∑ i, |a i| * |x i| := by
    calc
      (∑ i, |w i|) =
          ∑ i : Fin (2 ^ Nat.clog 2 k),
            p53ZeroPad k (fun j => |a j| * |x j|) i := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hik : i.val < k <;>
                simp [w, p53ZeroPad, p53ScalarPad, hik, abs_mul]
      _ = _ := by
        simpa only [p53ZeroPad] using
          (p53_pad_sum k (2 ^ Nat.clog 2 k) hpad
            (fun i => |a i| * |x i|))
  have hp := p53_pairwise_error fp (Nat.clog 2 k) v w hv hleaf
  simpa only [p53CascadeDot, p53CascadeSum, v, hsum, habsum] using hp

private lemma p53_schedule_sum {m n l : ℕ}
    (A : Fin m → Fin n → ℝ) (schedule : P53SparseSchedule A l)
    (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) = ∑ j, f j := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j => A i j ≠ 0)
  have hbij : (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j ∈ s, f j := by
    apply Finset.sum_bij (fun t _ => schedule.col i t)
    · intro t ht
      simp [s, schedule.col_nonzero i t]
    · intro t₁ ht₁ t₂ ht₂ he
      exact schedule.col_injective i he
    · intro j hj
      obtain ⟨t, ht⟩ := schedule.covers i j (Finset.mem_filter.mp hj).2
      exact ⟨t, Finset.mem_univ _, ht⟩
    · intro t ht
      rfl
  rw [hbij]
  rw [show (∑ j ∈ s, f j) = ∑ j ∈ Finset.univ with A i j ≠ 0, f j by rfl]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : A i j = 0
  · simp [hz, hf j hz]
  · simp [hz]

private lemma p53_abs_sign (a : ℝ) :
    |p53Sign a| = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [p53Sign, ha]
  · have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
    simp [p53Sign, ha, abs_div, habs]

private lemma p53_row_transfer {n : ℕ} (fp : P53FPModel)
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (η g z : ℝ) (i : Fin n) (hg : 0 ≤ g) (hη : 0 < η)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (heval : |z - ∑ j, Ahat i j * x j| ≤
      g * ∑ j, |Ahat i j| * |x j|) :
    |z - ∑ j, A i j * x j| ≤
      g * (∑ j, |A i j| * |x j|) +
      (η * fp.u + g * (η * fp.u)) *
        (∑ j, |p53Sign (A i j)| * |x j|) := by
  have hcoef (j : Fin n) :
      |Ahat i j - A i j| ≤ η * fp.u * |p53Sign (A i j)| := by
    by_cases hz : A i j = 0
    · simp [hz, hzero i j hz, p53Sign]
    · simpa [p53_abs_sign, hz] using hpre i j hz
  have hpoint (j : Fin n) :
      |Ahat i j| * |x j| ≤
      |A i j| * |x j| + η * fp.u * (|p53Sign (A i j)| * |x j|) := by
    have ha : |Ahat i j| ≤ |A i j| + |Ahat i j - A i j| := by
      calc
        |Ahat i j| = |A i j + (Ahat i j - A i j)| := by ring
        _ ≤ |A i j| + |Ahat i j - A i j| := abs_add_le _ _
    have hb := mul_le_mul_of_nonneg_right ha (abs_nonneg (x j))
    have hc := mul_le_mul_of_nonneg_right (hcoef j) (abs_nonneg (x j))
    nlinarith
  have hsumhat :
      (∑ j, |Ahat i j| * |x j|) ≤
      (∑ j, |A i j| * |x j|) +
        η * fp.u * (∑ j, |p53Sign (A i j)| * |x j|) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpoint j)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs
  have hprepoint (j : Fin n) :
      |(Ahat i j - A i j) * x j| ≤
        η * fp.u * (|p53Sign (A i j)| * |x j|) := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right (hcoef j) (abs_nonneg (x j))
    nlinarith
  have hprecomp :
      |(∑ j, Ahat i j * x j) - ∑ j, A i j * x j| ≤
        η * fp.u * (∑ j, |p53Sign (A i j)| * |x j|) := by
    have habs := Finset.abs_sum_le_sum_abs
      (fun j : Fin n => (Ahat i j - A i j) * x j) Finset.univ
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hprepoint j)
    calc
      |(∑ j, Ahat i j * x j) - ∑ j, A i j * x j| =
          |∑ j, (Ahat i j - A i j) * x j| := by
            rw [← Finset.sum_sub_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ ∑ j, |(Ahat i j - A i j) * x j| := habs
      _ ≤ _ := by simpa only [← Finset.mul_sum] using hle
  have htriangle : |z - ∑ j, A i j * x j| ≤
      |z - ∑ j, Ahat i j * x j| +
        |(∑ j, Ahat i j * x j) - ∑ j, A i j * x j| := by
    have h := abs_add_le
      (z - ∑ j, Ahat i j * x j)
      ((∑ j, Ahat i j * x j) - ∑ j, A i j * x j)
    convert h using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hsumhat hg
  nlinarith [htriangle, heval, hprecomp]

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
  constructor
  · intro i
    have hc : P53GammaValid fp.u (schedule.count i) :=
      p53_valid_of_le fp.u fp.u_nonneg (schedule.count_le i) hvalid
    have hsum :
        (∑ t : Fin (schedule.count i),
          Ahat i (schedule.col i t) * x (schedule.col i t)) =
          ∑ j, Ahat i j * x j :=
      p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
        (by intro j hz; simp [hzero i j hz])
    have hsumabs :
        (∑ t : Fin (schedule.count i),
          |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
          ∑ j, |Ahat i j| * |x j| :=
      p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
        (by intro j hz; simp [hzero i j hz])
    have hdot := p53_fold_dot_error fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hc
    rw [← p53_dot_eq_fold] at hdot
    rw [hsum, hsumabs] at hdot
    have hgmono := p53_gamma_mono fp.u fp.u_nonneg (schedule.count_le i) hvalid
    have hsnonneg : 0 ≤ ∑ j, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (by intros; positivity)
    have heval :
        |p53SparseMatVec fp A Ahat x schedule i - ∑ j, Ahat i j * x j| ≤
          p53Gamma fp.u l * (∑ j, |Ahat i j| * |x j|) := by
      change |p53Dot fp (schedule.count i)
        (fun t => Ahat i (schedule.col i t))
        (fun t => x (schedule.col i t)) - ∑ j, Ahat i j * x j| ≤ _
      exact hdot.trans (mul_le_mul_of_nonneg_right hgmono hsnonneg)
    exact p53_row_transfer fp A Ahat x η (p53Gamma fp.u l)
      (p53SparseMatVec fp A Ahat x schedule i) i
      (p53_gamma_nonneg fp.u fp.u_nonneg l hvalid) hη hpre hzero heval
  · intro i
    have hdl : Nat.clog 2 l + 1 ≤ l := p53_clog_succ_le l hln.1
    have hvalidl : P53GammaValid fp.u (Nat.clog 2 l + 1) :=
      p53_valid_of_le fp.u fp.u_nonneg hdl hvalid
    have hdepth : Nat.clog 2 (schedule.count i) + 1 ≤ Nat.clog 2 l + 1 :=
      Nat.add_le_add_right (Nat.clog_mono_right 2 (schedule.count_le i)) 1
    have hc : P53GammaValid fp.u (Nat.clog 2 (schedule.count i) + 1) :=
      p53_valid_of_le fp.u fp.u_nonneg hdepth hvalidl
    have hsum :
        (∑ t : Fin (schedule.count i),
          Ahat i (schedule.col i t) * x (schedule.col i t)) =
          ∑ j, Ahat i j * x j :=
      p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
        (by intro j hz; simp [hzero i j hz])
    have hsumabs :
        (∑ t : Fin (schedule.count i),
          |Ahat i (schedule.col i t)| * |x (schedule.col i t)|) =
          ∑ j, |Ahat i j| * |x j| :=
      p53_schedule_sum A schedule i (fun j => |Ahat i j| * |x j|)
        (by intro j hz; simp [hzero i j hz])
    have hdot := p53_cascade_dot_error fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hc
    rw [hsum, hsumabs] at hdot
    have hgmono := p53_gamma_mono fp.u fp.u_nonneg hdepth hvalidl
    have hsnonneg : 0 ≤ ∑ j, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (by intros; positivity)
    have heval :
        |p53SparseCascadeMatVec fp A Ahat x schedule i -
            ∑ j, Ahat i j * x j| ≤
          p53Gamma fp.u (Nat.clog 2 l + 1) *
            (∑ j, |Ahat i j| * |x j|) := by
      change |p53CascadeDot fp (schedule.count i)
        (fun t => Ahat i (schedule.col i t))
        (fun t => x (schedule.col i t)) - ∑ j, Ahat i j * x j| ≤ _
      exact hdot.trans (mul_le_mul_of_nonneg_right hgmono hsnonneg)
    exact p53_row_transfer fp A Ahat x η
      (p53Gamma fp.u (Nat.clog 2 l + 1))
      (p53SparseCascadeMatVec fp A Ahat x schedule i) i
      (p53_gamma_nonneg fp.u fp.u_nonneg (Nat.clog 2 l + 1) hvalidl)
      hη hpre hzero heval

end VSCLReuse

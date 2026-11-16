import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p53_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P53GammaValid u k) : 0 ≤ p53Gamma u k := by
  unfold p53Gamma P53GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hk))

private lemma p53_gamma_mono (u : ℝ) (hu : 0 ≤ u) {m k : ℕ}
    (hmk : m ≤ k) (hk : P53GammaValid u k) :
    p53Gamma u m ≤ p53Gamma u k := by
  have hmu : (m : ℝ) * u ≤ (k : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmk) hu
  have hm : (m : ℝ) * u < 1 := lt_of_le_of_lt hmu hk
  unfold p53Gamma
  apply (div_le_div_iff₀ (sub_pos.mpr hm) (sub_pos.mpr hk)).2
  nlinarith

private lemma p53_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P53GammaValid u (k + 1)) :
    u + p53Gamma u k * (1 + u) ≤ p53Gamma u (k + 1) := by
  have ha : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hkn : (k : ℝ) * u < 1 := by
    have hcast : ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by push_cast; ring
    unfold P53GammaValid at hk
    rw [hcast] at hk
    linarith
  have hkn' : ((k + 1 : ℕ) : ℝ) * u = (k : ℝ) * u + u := by
    push_cast; ring
  have heq : u + p53Gamma u k * (1 + u) =
      ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
    unfold p53Gamma
    have hden : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hkn]
    field_simp [hden]
    ring
  rw [heq, p53Gamma, hkn']
  have hk' : (k : ℝ) * u + u < 1 := by
    simpa only [P53GammaValid, hkn'] using hk
  exact div_le_div_of_nonneg_left (by positivity)
    (sub_pos.mpr hk') (by linarith)

private lemma p53_add_bound (fp : P53FPModel) (k : ℕ)
    (hk : P53GammaValid fp.u (k + 1))
    {z₁ z₂ s₁ s₂ w₁ w₂ : ℝ}
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hs₁ : |s₁| ≤ w₁) (hs₂ : |s₂| ≤ w₂)
    (he₁ : |z₁ - s₁| ≤ p53Gamma fp.u k * w₁)
    (he₂ : |z₂ - s₂| ≤ p53Gamma fp.u k * w₂) :
    |fp.fl_add z₁ z₂ - (s₁ + s₂)| ≤
      p53Gamma fp.u (k + 1) * (w₁ + w₂) := by
  rcases fp.model_add z₁ z₂ with ⟨δ, hδ, hfl⟩
  have hδ₁ : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by norm_num at *; linarith
  have hδ₀ : 0 ≤ |1 + δ| := abs_nonneg _
  have hu₁ : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have he : |(z₁ - s₁) + (z₂ - s₂)| ≤
      p53Gamma fp.u k * (w₁ + w₂) := by
    calc
      |(z₁ - s₁) + (z₂ - s₂)| ≤ |z₁ - s₁| + |z₂ - s₂| := abs_add_le _ _
      _ ≤ p53Gamma fp.u k * w₁ + p53Gamma fp.u k * w₂ := add_le_add he₁ he₂
      _ = _ := by ring
  have hs : |s₁ + s₂| ≤ w₁ + w₂ :=
    (abs_add_le _ _).trans (add_le_add hs₁ hs₂)
  have hkv : P53GammaValid fp.u k := by
    have hle : (k : ℝ) * fp.u ≤ ((k + 1 : ℕ) : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) fp.u_nonneg
    exact lt_of_le_of_lt hle hk
  have hg : 0 ≤ p53Gamma fp.u k :=
    p53_gamma_nonneg fp.u fp.u_nonneg k hkv
  have hw : 0 ≤ w₁ + w₂ := add_nonneg hw₁ hw₂
  have hstep := p53_gamma_step fp.u fp.u_nonneg k hk
  calc
    |fp.fl_add z₁ z₂ - (s₁ + s₂)| =
        |((z₁ - s₁) + (z₂ - s₂)) * (1 + δ) + (s₁ + s₂) * δ| := by
          rw [hfl]; congr 1; ring
    _ ≤ |((z₁ - s₁) + (z₂ - s₂)) * (1 + δ)| + |(s₁ + s₂) * δ| :=
      abs_add_le _ _
    _ = |(z₁ - s₁) + (z₂ - s₂)| * |1 + δ| + |s₁ + s₂| * |δ| := by
      rw [abs_mul, abs_mul]
    _ ≤ (p53Gamma fp.u k * (w₁ + w₂)) * (1 + fp.u) +
        (w₁ + w₂) * fp.u := by
      apply add_le_add
      · exact (mul_le_mul he hδ₁ hδ₀ (mul_nonneg hg hw))
      · exact (mul_le_mul hs hδ (abs_nonneg _) hw)
    _ ≤ p53Gamma fp.u (k + 1) * (w₁ + w₂) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hstep) hw]

private lemma p53_u_le_gamma (fp : P53FPModel) {k : ℕ}
    (hk₁ : 1 ≤ k) (hk : P53GammaValid fp.u k) :
    fp.u ≤ p53Gamma fp.u k := by
  have hvone : P53GammaValid fp.u (0 + 1) := by
    have hle : fp.u ≤ (k : ℝ) * fp.u := by
      calc
        fp.u = (1 : ℝ) * fp.u := by ring
        _ ≤ (k : ℝ) * fp.u := mul_le_mul_of_nonneg_right
          (by exact_mod_cast hk₁) fp.u_nonneg
    have h : fp.u < 1 := lt_of_le_of_lt hle hk
    simpa [P53GammaValid] using h
  have hstep := p53_gamma_step fp.u fp.u_nonneg 0
    hvone
  have hmono := p53_gamma_mono fp.u fp.u_nonneg hk₁ hk
  simp [p53Gamma] at hstep
  have hmono' : fp.u / (1 - fp.u) ≤ p53Gamma fp.u k := by
    simpa [p53Gamma] using hmono
  linarith

private lemma p53_mul_error (fp : P53FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * (|a| * |x|) := by
  rcases fp.model_mul a x with ⟨δ, hδ, hfl⟩
  rw [hfl]
  have h : a * x * (1 + δ) - a * x = (a * x) * δ := by ring
  rw [h, abs_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
    (by ring)

private lemma p53_fold_bound (fp : P53FPModel) :
    ∀ (k m : ℕ) (v z w : Fin k → ℝ) (z₀ s₀ w₀ : ℝ),
      1 ≤ m → P53GammaValid fp.u (m + k) →
      0 ≤ w₀ → |s₀| ≤ w₀ →
      |z₀ - s₀| ≤ p53Gamma fp.u m * w₀ →
      (∀ i, 0 ≤ w i ∧ |v i| ≤ w i ∧ |z i - v i| ≤ fp.u * w i) →
      |Fin.foldl k (fun acc i => fp.fl_add acc (z i)) z₀ -
        (s₀ + ∑ i, v i)| ≤
        p53Gamma fp.u (m + k) * (w₀ + ∑ i, w i) := by
  intro k
  induction k with
  | zero =>
      intro m v z w z₀ s₀ w₀ hm hv hw₀ hs₀ he₀ hterms
      simpa using he₀
  | succ k ih =>
      intro m v z w z₀ s₀ w₀ hm hv hw₀ hs₀ he₀ hterms
      have hmvalid : P53GammaValid fp.u m := by
        have hle : (m : ℝ) * fp.u ≤ ((m + (k + 1) : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right m (k + 1)) fp.u_nonneg
        exact lt_of_le_of_lt hle hv
      have hmnext : P53GammaValid fp.u (m + 1) := by
        have hle : ((m + 1 : ℕ) : ℝ) * fp.u ≤ ((m + (k + 1) : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show m + 1 ≤ m + (k + 1) by omega)) fp.u_nonneg
        exact lt_of_le_of_lt hle hv
      have ht := hterms (0 : Fin (k + 1))
      have hleaf : |z 0 - v 0| ≤ p53Gamma fp.u m * w 0 :=
        ht.2.2.trans (mul_le_mul_of_nonneg_right
          (p53_u_le_gamma fp hm hmvalid) ht.1)
      have hfirst : |fp.fl_add z₀ (z 0) - (s₀ + v 0)| ≤
          p53Gamma fp.u (m + 1) * (w₀ + w 0) :=
        p53_add_bound fp m hmnext hw₀ ht.1 hs₀ ht.2.1 he₀ hleaf
      have hrest := ih (m + 1) (fun i => v i.succ) (fun i => z i.succ)
        (fun i => w i.succ) (fp.fl_add z₀ (z 0)) (s₀ + v 0) (w₀ + w 0)
        (by omega) (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv)
        (add_nonneg hw₀ ht.1) ((abs_add_le _ _).trans (add_le_add hs₀ ht.2.1))
        hfirst (fun i => hterms i.succ)
      have hnat : m + 1 + k = m + (k + 1) := by omega
      rw [hnat] at hrest
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, Nat.add_assoc,
        add_assoc] using hrest

private lemma p53_dot_error (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (hk : P53GammaValid fp.u k) :
    |p53Dot fp k a x - ∑ i, a i * x i| ≤
      p53Gamma fp.u k * (∑ i, |a i| * |x i|) := by
  cases k with
  | zero => simp [p53Dot]
  | succ k =>
      have hone : P53GammaValid fp.u 1 := by
        have hle : (1 : ℝ) * fp.u ≤ ((k + 1 : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show 1 ≤ k + 1 by omega)) fp.u_nonneg
        exact lt_of_le_of_lt (by simpa using hle) hk
      have hfirst : |fp.fl_mul (a 0) (x 0) - a 0 * x 0| ≤
          p53Gamma fp.u 1 * (|a 0| * |x 0|) :=
        (p53_mul_error fp (a 0) (x 0)).trans
          (mul_le_mul_of_nonneg_right
            (p53_u_le_gamma fp (by omega) hone)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      have hfold := p53_fold_bound fp k 1
        (fun i => a i.succ * x i.succ)
        (fun i => fp.fl_mul (a i.succ) (x i.succ))
        (fun i => |a i.succ| * |x i.succ|)
        (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) (|a 0| * |x 0|)
        (by omega) (by simpa only [Nat.add_comm 1 k] using hk)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (by rw [abs_mul]) hfirst
        (fun i => ⟨mul_nonneg (abs_nonneg _) (abs_nonneg _),
          by rw [abs_mul], p53_mul_error fp (a i.succ) (x i.succ)⟩)
      simpa only [p53Dot, Fin.sum_univ_succ, Nat.add_comm 1 k] using hfold

private lemma p53_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, v i) =
      (∑ i : Fin (2 ^ r), v ⟨i.val, p53_left_lt r i⟩) +
      (∑ i : Fin (2 ^ r), v ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; omega
  calc
    (∑ i, v i) = ∑ i : Fin (2 ^ r + 2 ^ r), v (Fin.cast hp.symm i) := by
      apply Fintype.sum_equiv (Fin.castOrderIso hp).toEquiv
      intro i
      congr 1
    _ = _ := by
      rw [Fin.sum_univ_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        congr 1 <;> apply Fin.ext <;> simp [Fin.val_natAdd, Fin.val_castAdd]

private lemma p53_pairwise_error (fp : P53FPModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      P53GammaValid fp.u r →
      |p53PairwiseSum fp r v - ∑ i, v i| ≤
        p53Gamma fp.u r * (∑ i, |v i|) := by
  intro r
  induction r with
  | zero =>
      intro v hv
      simp [p53PairwiseSum, p53Gamma]
  | succ r ih =>
      intro v hv
      let vl : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
      let vr : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      have hvr : P53GammaValid fp.u r := by
        have hle : (r : ℝ) * fp.u ≤ ((r + 1 : ℕ) : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ r) fp.u_nonneg
        exact lt_of_le_of_lt hle hv
      have hl := ih vl hvr
      have hr := ih vr hvr
      have hwl : 0 ≤ ∑ i, |vl i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hwr : 0 ≤ ∑ i, |vr i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hsl : |∑ i, vl i| ≤ ∑ i, |vl i| := Finset.abs_sum_le_sum_abs _ _
      have hsr : |∑ i, vr i| ≤ ∑ i, |vr i| := Finset.abs_sum_le_sum_abs _ _
      have hadd := p53_add_bound fp r hv hwl hwr hsl hsr hl hr
      change |p53PairwiseSum fp (r + 1) v - ∑ i, v i| ≤
        p53Gamma fp.u (r + 1) * (∑ i, |v i|)
      simp only [p53PairwiseSum]
      rw [p53_pairwise_split r v,
        p53_pairwise_split r (fun i => |v i|)]
      exact hadd

private lemma p53_scalar_pad_sum {n m : ℕ} (hnm : n ≤ m)
    (v : Fin n → ℝ) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i : Fin n, v i := by
  have hm : m = n + (m - n) := by omega
  calc
    (∑ i : Fin m, p53ScalarPad n m v i) =
        ∑ i : Fin (n + (m - n)), p53ScalarPad n m v (Fin.cast hm.symm i) := by
      apply Fintype.sum_equiv (Fin.castOrderIso hm).toEquiv
      intro i
      congr 1
    _ = _ := by
      rw [Fin.sum_univ_add]
      have hleft : ∀ i : Fin n,
          p53ScalarPad n m v (Fin.cast hm.symm (Fin.castAdd (m - n) i)) = v i := by
        intro i
        simp [p53ScalarPad, Fin.ext_iff]
      have hright : ∀ i : Fin (m - n),
          p53ScalarPad n m v (Fin.cast hm.symm (Fin.natAdd n i)) = 0 := by
        intro i
        simp [p53ScalarPad, Fin.val_natAdd, Nat.not_lt.mpr (Nat.le_add_right n i.val)]
      simp only [hleft, hright, Finset.sum_const_zero, add_zero]

private lemma p53_cascade_dot_error (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ)
    (hk : P53GammaValid fp.u (Nat.clog 2 k + 1)) :
    |p53CascadeDot fp k a x - ∑ i, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 k + 1) *
        (∑ i, |a i| * |x i|) := by
  let r := Nat.clog 2 k
  let m := 2 ^ r
  have hkm : k ≤ m := Nat.le_pow_clog (by omega) k
  let v : Fin m → ℝ := p53ZeroPad k (fun i => fp.fl_mul (a i) (x i))
  let s : Fin m → ℝ := p53ZeroPad k (fun i => a i * x i)
  let w : Fin m → ℝ := p53ZeroPad k (fun i => |a i| * |x i|)
  have hpoint (i : Fin m) :
      0 ≤ w i ∧ |s i| ≤ w i ∧ |v i - s i| ≤ fp.u * w i := by
    by_cases hi : i.val < k
    · simp only [v, s, w, p53ZeroPad, p53ScalarPad, dif_pos hi]
      refine ⟨mul_nonneg (abs_nonneg _) (abs_nonneg _), ?_, ?_⟩
      · rw [abs_mul]
      · exact p53_mul_error fp _ _
    · simp [v, s, w, p53ZeroPad, p53ScalarPad, hi]
  have hvalr : P53GammaValid fp.u r := by
    have hle : (r : ℝ) * fp.u ≤ ((r + 1 : ℕ) : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ r) fp.u_nonneg
    exact lt_of_le_of_lt hle hk
  have hpair := p53_pairwise_error fp r v hvalr
  have herr : |(∑ i, v i) - (∑ i, s i)| ≤ fp.u * (∑ i, w i) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |(∑ i, (v i - s i))| ≤ ∑ i, |v i - s i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, fp.u * w i := Finset.sum_le_sum (fun i hi => (hpoint i).2.2)
      _ = fp.u * ∑ i, w i := by rw [Finset.mul_sum]
  have hround (i : Fin m) : |v i| ≤ (1 + fp.u) * w i := by
    have h := abs_sub_le (v i) (s i) 0
    have hs := (hpoint i).2.1
    have he := (hpoint i).2.2
    simp only [sub_zero] at h
    nlinarith
  have hroundsum : (∑ i, |v i|) ≤ (1 + fp.u) * (∑ i, w i) := by
    calc
      (∑ i, |v i|) ≤ ∑ i, (1 + fp.u) * w i :=
        Finset.sum_le_sum (fun i hi => hround i)
      _ = _ := by rw [Finset.mul_sum]
  have hw : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i hi => (hpoint i).1)
  have hg : 0 ≤ p53Gamma fp.u r := p53_gamma_nonneg fp.u fp.u_nonneg r hvalr
  have hstep := p53_gamma_step fp.u fp.u_nonneg r hk
  have hmain : |p53PairwiseSum fp r v - ∑ i, s i| ≤
      p53Gamma fp.u (r + 1) * (∑ i, w i) := by
    calc
      |p53PairwiseSum fp r v - ∑ i, s i| ≤
          |p53PairwiseSum fp r v - ∑ i, v i| + |(∑ i, v i) - (∑ i, s i)| :=
        abs_sub_le _ _ _
      _ ≤ p53Gamma fp.u r * (∑ i, |v i|) + fp.u * (∑ i, w i) :=
        add_le_add hpair herr
      _ ≤ p53Gamma fp.u r * ((1 + fp.u) * (∑ i, w i)) +
          fp.u * (∑ i, w i) :=
        add_le_add (mul_le_mul_of_nonneg_left hroundsum hg) le_rfl
      _ ≤ p53Gamma fp.u (r + 1) * (∑ i, w i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hstep) hw]
  have hsumpad : (∑ i, s i) = ∑ i, a i * x i :=
    p53_scalar_pad_sum hkm (fun i => a i * x i)
  have hwpad : (∑ i, w i) = ∑ i, |a i| * |x i| :=
    p53_scalar_pad_sum hkm (fun i => |a i| * |x i|)
  simpa only [p53CascadeDot, p53CascadeSum, r, m, v,
    hsumpad, hwpad] using hmain

private lemma p53_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin m)
    (f : Fin n → ℝ) (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j : Fin n, f j := by
  calc
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => A i j ≠ 0), f j := by
      apply Finset.sum_bij (fun t _ => schedule.col i t)
      · intro t ht
        simp [schedule.col_nonzero i t]
      · intro t ht t' ht' h
        exact schedule.col_injective i h
      · intro j hj
        obtain ⟨t, ht⟩ := schedule.covers i j (Finset.mem_filter.mp hj).2
        exact ⟨t, Finset.mem_univ _, ht⟩
      · intro t ht
        rfl
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hj hjnot
      apply hf
      by_contra h
      exact hjnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

private lemma p53_abs_sign (a : ℝ) :
    |p53Sign a| = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · simp [p53Sign, ha]
  · have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
    simp [p53Sign, ha, abs_div, habs]

private lemma p53_row_error {n : ℕ} (fp : P53FPModel)
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (η G z : ℝ) (i : Fin n)
    (hη : 0 < η) (hG : 0 ≤ G)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (heval : |z - ∑ j, Ahat i j * x j| ≤
      G * (∑ j, |Ahat i j| * |x j|)) :
    |z - ∑ j, A i j * x j| ≤
      G * (∑ j, |A i j| * |x j|) +
      (η * fp.u + G * (η * fp.u)) *
        (∑ j, |p53Sign (A i j)| * |x j|) := by
  have hentry (j : Fin n) :
      |Ahat i j - A i j| ≤ η * fp.u * |p53Sign (A i j)| := by
    by_cases ha : A i j = 0
    · have hh := hzero i j ha
      simp [ha, hh, p53Sign]
    · rw [p53_abs_sign, if_neg ha, mul_one]
      exact hpre i j ha
  have hcoef : |(∑ j, Ahat i j * x j) - (∑ j, A i j * x j)| ≤
      (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |(∑ j, (Ahat i j * x j - A i j * x j))| ≤
          ∑ j, |Ahat i j * x j - A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (η * fp.u) * (|p53Sign (A i j)| * |x j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← sub_mul, abs_mul]
        calc
          |Ahat i j - A i j| * |x j| ≤
              (η * fp.u * |p53Sign (A i j)|) * |x j| :=
            mul_le_mul_of_nonneg_right (hentry j) (abs_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  have hhat : (∑ j, |Ahat i j| * |x j|) ≤
      (∑ j, |A i j| * |x j|) +
        (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) := by
    calc
      (∑ j, |Ahat i j| * |x j|) ≤
          ∑ j, (|A i j| * |x j| +
            (η * fp.u) * (|p53Sign (A i j)| * |x j|)) := by
        apply Finset.sum_le_sum
        intro j hj
        have habs : |Ahat i j| ≤ |A i j| + |Ahat i j - A i j| := by
          have h := abs_sub_le (Ahat i j) (A i j) 0
          simpa only [sub_zero, abs_sub_comm, add_comm] using h
        nlinarith [mul_le_mul_of_nonneg_right habs (abs_nonneg (x j)),
          mul_le_mul_of_nonneg_right (hentry j) (abs_nonneg (x j))]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    |z - ∑ j, A i j * x j| ≤
        |z - ∑ j, Ahat i j * x j| +
          |(∑ j, Ahat i j * x j) - (∑ j, A i j * x j)| :=
      abs_sub_le _ _ _
    _ ≤ G * (∑ j, |Ahat i j| * |x j|) +
          (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) :=
      add_le_add heval hcoef
    _ ≤ G * ((∑ j, |A i j| * |x j|) +
          (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|)) +
          (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) :=
      add_le_add (mul_le_mul_of_nonneg_left hhat hG) le_rfl
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
  have hclog : Nat.clog 2 l + 1 ≤ l := by
    have hp : l - 1 < 2 ^ (l - 1) :=
      Nat.lt_pow_self (by omega)
    have hpow : l ≤ 2 ^ (l - 1) := by omega
    have hc : Nat.clog 2 l ≤ l - 1 := Nat.clog_le_of_le_pow hpow
    omega
  have hvalidCascade : P53GammaValid fp.u (Nat.clog 2 l + 1) := by
    have hle : ((Nat.clog 2 l + 1 : ℕ) : ℝ) * fp.u ≤ (l : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hclog) fp.u_nonneg
    exact lt_of_le_of_lt hle hvalid
  constructor
  · intro i
    apply p53_row_error fp A Ahat x η (p53Gamma fp.u l)
      (p53SparseMatVec fp A Ahat x schedule i) i hη
      (p53_gamma_nonneg fp.u fp.u_nonneg l hvalid) hpre hzero
    have hcount : P53GammaValid fp.u (schedule.count i) := by
      have hle : ((schedule.count i : ℕ) : ℝ) * fp.u ≤ (l : ℝ) * fp.u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast schedule.count_le i) fp.u_nonneg
      exact lt_of_le_of_lt hle hvalid
    have hdot := p53_dot_error fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hcount
    have hsum := p53_schedule_sum A schedule i
      (fun j => Ahat i j * x j) (by
        intro j hj
        simp [hzero i j hj])
    have hweight := p53_schedule_sum A schedule i
      (fun j => |Ahat i j| * |x j|) (by
        intro j hj
        simp [hzero i j hj])
    rw [hsum, hweight] at hdot
    have hg := p53_gamma_mono fp.u fp.u_nonneg (schedule.count_le i) hvalid
    have hw : 0 ≤ ∑ j : Fin n, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact hdot.trans (mul_le_mul_of_nonneg_right hg hw)
  · intro i
    apply p53_row_error fp A Ahat x η
      (p53Gamma fp.u (Nat.clog 2 l + 1))
      (p53SparseCascadeMatVec fp A Ahat x schedule i) i hη
      (p53_gamma_nonneg fp.u fp.u_nonneg _ hvalidCascade) hpre hzero
    have hclogRow : Nat.clog 2 (schedule.count i) + 1 ≤
        Nat.clog 2 l + 1 := by
      have h := Nat.clog_mono (by omega : 1 < 2) (by omega : 2 ≤ 2)
        (schedule.count_le i)
      omega
    have hvalidRow : P53GammaValid fp.u
        (Nat.clog 2 (schedule.count i) + 1) := by
      have hle : ((Nat.clog 2 (schedule.count i) + 1 : ℕ) : ℝ) * fp.u ≤
          ((Nat.clog 2 l + 1 : ℕ) : ℝ) * fp.u :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hclogRow) fp.u_nonneg
      exact lt_of_le_of_lt hle hvalidCascade
    have hdot := p53_cascade_dot_error fp (schedule.count i)
      (fun t => Ahat i (schedule.col i t))
      (fun t => x (schedule.col i t)) hvalidRow
    have hsum := p53_schedule_sum A schedule i
      (fun j => Ahat i j * x j) (by
        intro j hj
        simp [hzero i j hj])
    have hweight := p53_schedule_sum A schedule i
      (fun j => |Ahat i j| * |x j|) (by
        intro j hj
        simp [hzero i j hj])
    rw [hsum, hweight] at hdot
    have hg := p53_gamma_mono fp.u fp.u_nonneg hclogRow hvalidCascade
    have hw : 0 ≤ ∑ j : Fin n, |Ahat i j| * |x j| :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact hdot.trans (mul_le_mul_of_nonneg_right hg hw)

end VSCLReuse

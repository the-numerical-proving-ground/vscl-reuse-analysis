import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p53_gamma_mono (u : ℝ) {j k : ℕ} (hu : 0 ≤ u)
    (hjk : j ≤ k) (hk : P53GammaValid u k) :
    p53Gamma u j ≤ p53Gamma u k := by
  have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hprod : (j : ℝ) * u ≤ (k : ℝ) * u := mul_le_mul_of_nonneg_right hcast hu
  unfold P53GammaValid at hk
  unfold p53Gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

private lemma p53_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P53GammaValid u (k + 1)) :
    (1 + u) * p53Gamma u k + u ≤ p53Gamma u (k + 1) := by
  have hkp : ((k : ℝ) + 1) * u < 1 := by
    simpa only [P53GammaValid, Nat.cast_add, Nat.cast_one] using hk
  have hku : (k : ℝ) * u < 1 := by
    nlinarith
  have hden : 1 - (k : ℝ) * u ≠ 0 := ne_of_gt (by linarith)
  have hden' : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hden]
  have hnum : 0 ≤ ((k : ℝ) + 1) * u := mul_nonneg (by positivity) hu
  have hid : (1 + u) * p53Gamma u k + u =
      (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
    unfold p53Gamma
    field_simp [hden, hden']
    ring
  rw [hid]
  unfold p53Gamma
  simp only [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

private lemma p53_round_add_bound (fp : P53FPModel) (k : ℕ)
    (hk : P53GammaValid fp.u (k + 1))
    {v w s t A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : |s| ≤ A) (ht : |t| ≤ B)
    (hv : |v - s| ≤ p53Gamma fp.u k * A)
    (hw : |w - t| ≤ p53Gamma fp.u k * B) :
    |fp.fl_add v w - (s + t)| ≤ p53Gamma fp.u (k + 1) * (A + B) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add v w
  have hfac : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have heq : fp.fl_add v w - (s + t) =
      ((v - s) + (w - t)) * (1 + δ) + δ * (s + t) := by
    rw [hfl]
    ring
  have hlocal : |fp.fl_add v w - (s + t)| ≤
      (|v - s| + |w - t|) * (1 + fp.u) + fp.u * (|s| + |t|) := by
    rw [heq]
    calc
      |((v - s) + (w - t)) * (1 + δ) + δ * (s + t)| ≤
          |((v - s) + (w - t)) * (1 + δ)| + |δ * (s + t)| := abs_add_le _ _
      _ = |(v - s) + (w - t)| * |1 + δ| + |δ| * |s + t| := by rw [abs_mul, abs_mul]
      _ ≤ (|v - s| + |w - t|) * (1 + fp.u) + fp.u * (|s| + |t|) := by
        gcongr
        · exact abs_add_le _ _
        · exact fp.u_nonneg
        · exact abs_add_le _ _
  have herrors : |v - s| + |w - t| ≤ p53Gamma fp.u k * (A + B) := by
    nlinarith [hv, hw]
  have hsums : |s| + |t| ≤ A + B := add_le_add hs ht
  have hmiddle : |fp.fl_add v w - (s + t)| ≤
      ((1 + fp.u) * p53Gamma fp.u k + fp.u) * (A + B) := by
    calc
      _ ≤ (|v - s| + |w - t|) * (1 + fp.u) + fp.u * (|s| + |t|) := hlocal
      _ ≤ p53Gamma fp.u k * (A + B) * (1 + fp.u) + fp.u * (A + B) := by
        gcongr
        · linarith [fp.u_nonneg]
        · exact fp.u_nonneg
      _ = ((1 + fp.u) * p53Gamma fp.u k + fp.u) * (A + B) := by ring
  exact hmiddle.trans (mul_le_mul_of_nonneg_right (p53_gamma_step fp.u k fp.u_nonneg hk)
    (add_nonneg hA hB))

private lemma p53_gamma_valid_mono (u : ℝ) {j k : ℕ} (hu : 0 ≤ u)
    (hjk : j ≤ k) (hk : P53GammaValid u k) : P53GammaValid u j := by
  have hcast : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  unfold P53GammaValid at *
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hk

private lemma p53_mul_bound (fp : P53FPModel) {k : ℕ} (hkpos : 1 ≤ k)
    (hk : P53GammaValid fp.u k) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ p53Gamma fp.u k * (|a| * |b|) := by
  have hvalid1 := p53_gamma_valid_mono fp.u fp.u_nonneg hkpos hk
  have hγ1 : fp.u ≤ p53Gamma fp.u 1 := by
    have h := p53_gamma_step fp.u 0 fp.u_nonneg hvalid1
    simpa [p53Gamma] using h
  have hγ : fp.u ≤ p53Gamma fp.u k :=
    hγ1.trans (p53_gamma_mono fp.u fp.u_nonneg hkpos hk)
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  calc
    |fp.fl_mul a b - a * b| = |a * b * δ| := by rw [hfl]; congr 1; ring
    _ = (|a| * |b|) * |δ| := by rw [abs_mul, abs_mul]
    _ ≤ (|a| * |b|) * fp.u := mul_le_mul_of_nonneg_left hδ (by positivity)
    _ ≤ p53Gamma fp.u k * (|a| * |b|) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hγ (by positivity)

private lemma p53_sum_abs {n : ℕ} (a x : Fin n → ℝ) :
    |∑ i : Fin n, a i * x i| ≤ ∑ i : Fin n, |a i| * |x i| := by
  calc
    _ ≤ ∑ i : Fin n, |a i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |a i| * |x i| := by simp_rw [abs_mul]

private lemma p53_dot_succ (fp : P53FPModel) (k : ℕ) (hk : 0 < k)
    (a x : Fin (k + 1) → ℝ) :
    p53Dot fp (k + 1) a x =
      fp.fl_add (p53Dot fp k (fun i => a i.castSucc) (fun i => x i.castSucc))
        (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) := by
  cases k with
  | zero => omega
  | succ m =>
      simp only [p53Dot, Fin.foldl_succ_last]
      congr 1

private lemma p53_dot_error (fp : P53FPModel) :
    ∀ (n : ℕ) (a x : Fin n → ℝ), 0 < n → P53GammaValid fp.u n →
      |p53Dot fp n a x - ∑ i : Fin n, a i * x i| ≤
        p53Gamma fp.u n * ∑ i : Fin n, |a i| * |x i| := by
  intro n
  induction n with
  | zero =>
      intro a x hn _
      omega
  | succ k ih =>
      intro a x hn hvalid
      by_cases hk : k = 0
      · subst k
        simpa [p53Dot, Fin.sum_univ_one] using
          p53_mul_bound fp (k := 1) (by omega) hvalid (a 0) (x 0)
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hprefixvalid : P53GammaValid fp.u k :=
          p53_gamma_valid_mono fp.u fp.u_nonneg (Nat.le_succ k) hvalid
        have hprefix := ih (fun i => a i.castSucc) (fun i => x i.castSucc)
          hkpos hprefixvalid
        have hleaf := p53_mul_bound fp (k := k) (by omega) hprefixvalid
          (a (Fin.last k)) (x (Fin.last k))
        have hA : 0 ≤ ∑ i : Fin k, |a i.castSucc| * |x i.castSucc| := by
          apply Finset.sum_nonneg
          intro i hi
          positivity
        have hB : 0 ≤ |a (Fin.last k)| * |x (Fin.last k)| := by positivity
        have hround := p53_round_add_bound fp k hvalid hA hB
          (p53_sum_abs (fun i => a i.castSucc) (fun i => x i.castSucc))
          (by rw [abs_mul]) hprefix hleaf
        simpa only [p53_dot_succ fp k hkpos, Fin.sum_univ_castSucc] using hround

private lemma p53_clog_succ_le (n : ℕ) (hn : 0 < n) : Nat.clog 2 n + 1 ≤ n := by
  cases n with
  | zero => omega
  | succ k =>
      have hpow : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self.succ_le
      have hclog : Nat.clog 2 (k + 1) ≤ k := Nat.clog_le_of_le_pow hpow
      omega

private lemma p53_pairwise_split (r : ℕ) (w : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), w i) =
      (∑ i : Fin (2 ^ r), w ⟨i.val, p53_left_lt r i⟩) +
      (∑ i : Fin (2 ^ r), w ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ, mul_two]
  calc
    _ = ∑ i : Fin (2 ^ r + 2 ^ r), w ((finCongr hpow).symm i) :=
      Fintype.sum_equiv (finCongr hpow) _ _ (by intro i; simp)
    _ = _ := by
      rw [Fin.sum_univ_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Fin.ext
      simp

private lemma p53_pad_sum (n d : ℕ) (v : Fin n → ℝ) :
    (∑ i : Fin (n + d), p53ScalarPad n (n + d) v i) = ∑ i : Fin n, v i := by
  rw [Fin.sum_univ_add]
  simp [p53ScalarPad, Fin.val_castAdd, Fin.val_natAdd]

private lemma p53_pairwise_error (fp : P53FPModel) :
    ∀ (r : ℕ) (v w : Fin (2 ^ r) → ℝ),
      P53GammaValid fp.u (r + 1) →
      (∀ i, |v i - w i| ≤ p53Gamma fp.u 1 * |w i|) →
      |p53PairwiseSum fp r v - ∑ i : Fin (2 ^ r), w i| ≤
        p53Gamma fp.u (r + 1) * ∑ i : Fin (2 ^ r), |w i| := by
  intro r
  induction r with
  | zero =>
      intro v w hvalid hleaf
      simpa [p53PairwiseSum, Fin.sum_univ_one] using hleaf (0 : Fin (2 ^ 0))
  | succ r ih =>
      intro v w hvalid hleaf
      have hchild : P53GammaValid fp.u (r + 1) :=
        p53_gamma_valid_mono fp.u fp.u_nonneg (by omega) hvalid
      let wl : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val, p53_left_lt r i⟩
      let wr : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      let vl : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
      let vr : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      have hl := ih vl wl hchild (by intro i; exact hleaf _)
      have hr := ih vr wr hchild (by intro i; exact hleaf _)
      have hA : 0 ≤ ∑ i : Fin (2 ^ r), |wl i| := Finset.sum_nonneg (by intro i hi; positivity)
      have hB : 0 ≤ ∑ i : Fin (2 ^ r), |wr i| := Finset.sum_nonneg (by intro i hi; positivity)
      have hround := p53_round_add_bound fp (r + 1) hvalid hA hB
        (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _) hl hr
      simpa only [p53PairwiseSum, p53_pairwise_split, wl, wr, vl, vr] using hround

private lemma p53_pad_sum_general (n m : ℕ) (hmn : n ≤ m) (v : Fin n → ℝ) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i : Fin n, v i := by
  have heq : n + (m - n) = m := by omega
  have h := p53_pad_sum n (m - n) v
  rw [heq] at h
  exact h

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
  constructor
  · exact p53_dot_error fp n a x hn hrec
  · let r := Nat.clog 2 n
    have hrn : r + 1 ≤ n := p53_clog_succ_le n hn
    have hdepth : P53GammaValid fp.u (r + 1) :=
      p53_gamma_valid_mono fp.u fp.u_nonneg hrn hrec
    have hvalid1 : P53GammaValid fp.u 1 :=
      p53_gamma_valid_mono fp.u fp.u_nonneg (by omega) hdepth
    have hpad : n ≤ 2 ^ r := Nat.le_pow_clog (by omega) n
    let v : Fin (2 ^ r) → ℝ := p53ZeroPad n (fun i => fp.fl_mul (a i) (x i))
    let w : Fin (2 ^ r) → ℝ := p53ZeroPad n (fun i => a i * x i)
    have hleaf (i : Fin (2 ^ r)) :
        |v i - w i| ≤ p53Gamma fp.u 1 * |w i| := by
      simp only [v, w, p53ZeroPad, p53ScalarPad]
      split_ifs with h
      · simpa only [abs_mul] using
          p53_mul_bound fp (by omega) hvalid1 (a ⟨i.val, h⟩) (x ⟨i.val, h⟩)
      · simp
    have hexact : (∑ i : Fin (2 ^ r), w i) = ∑ i : Fin n, a i * x i := by
      exact p53_pad_sum_general n (2 ^ r) hpad (fun i => a i * x i)
    have habs : (∑ i : Fin (2 ^ r), |w i|) =
        ∑ i : Fin n, |a i| * |x i| := by
      calc
        _ = ∑ i : Fin (2 ^ r), p53ZeroPad n (fun j => |a j| * |x j|) i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [w, p53ZeroPad, p53ScalarPad]
          split_ifs <;> simp [abs_mul]
        _ = _ := p53_pad_sum_general n (2 ^ r) hpad _
    have htree := p53_pairwise_error fp r v w hdepth hleaf
    rw [hexact, habs] at htree
    simpa only [p53CascadeDot, p53CascadeSum, r, v] using htree

end VSCLReuse

import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators


private lemma p53_mul_error (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  rw [hfl]
  have heq : a * b * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p53_add_error (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma p53_add_combine (fp : P53FPModel)
    (v w s t S T c : ℝ)
    (hs : |s| ≤ S) (ht : |t| ≤ T)
    (hv : |v - s| ≤ (c - 1) * S)
    (hw : |w - t| ≤ (c - 1) * T) :
    |fp.fl_add v w - (s + t)| ≤ ((1 + fp.u) * c - 1) * (S + T) := by
  have hsumerr : |(v + w) - (s + t)| ≤ |v - s| + |w - t| := by
    calc
      _ = |(v - s) + (w - t)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hE : |v - s| + |w - t| ≤ (c - 1) * (S + T) := by
    nlinarith [hv, hw]
  have hmag : |v + w| ≤ c * (S + T) := by
    have h1 : |v + w| ≤ |v - s| + |w - t| + |s| + |t| := by
      have heq : v + w = (v - s) + (w - t) + s + t := by ring
      rw [heq]
      calc
        _ ≤ |(v - s) + (w - t) + s| + |t| := abs_add_le _ _
        _ ≤ |(v - s) + (w - t)| + |s| + |t| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ |v - s| + |w - t| + |s| + |t| := by
          gcongr
          exact abs_add_le _ _
    nlinarith [hE, hs, ht]
  have hround := p53_add_error fp v w
  have hround' := mul_le_mul_of_nonneg_left hmag fp.u_nonneg
  have htri : |fp.fl_add v w - (s + t)| ≤
      |fp.fl_add v w - (v + w)| + |(v + w) - (s + t)| := by
    have heq : fp.fl_add v w - (s + t) =
        (fp.fl_add v w - (v + w)) + ((v + w) - (s + t)) := by ring
    rw [heq]
    exact abs_add_le _ _
  nlinarith [htri, hround, hround', hsumerr, hE]

private lemma p53_pow_nonneg (fp : P53FPModel) (k : ℕ) :
    0 ≤ (1 + fp.u) ^ k := pow_nonneg (by linarith [fp.u_nonneg]) _

private lemma p53_pow_one_le (fp : P53FPModel) (k : ℕ) :
    1 ≤ (1 + fp.u) ^ k := one_le_pow₀ (by linarith [fp.u_nonneg])

private lemma p53_pow_ge_base (fp : P53FPModel) (k : ℕ) (hk : 0 < k) :
    1 + fp.u ≤ (1 + fp.u) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ]
  exact (by simpa [mul_comm] using
    mul_le_mul_of_nonneg_right (p53_pow_one_le fp j) (by linarith [fp.u_nonneg]))

private lemma p53_pow_gamma (fp : P53FPModel) (k : ℕ)
    (hk : P53GammaValid fp.u k) :
    (1 + fp.u) ^ k - 1 ≤ p53Gamma fp.u k := by
  have hcore : ∀ j : ℕ, (j : ℝ) * fp.u < 1 →
      (1 + fp.u) ^ j * (1 - (j : ℝ) * fp.u) ≤ 1 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hj' : (j : ℝ) * fp.u < 1 := by
          have hcast : (j : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_succ j
          nlinarith [mul_le_mul_of_nonneg_right hcast fp.u_nonneg]
        have hstep : (1 + fp.u) * (1 - (↑(j + 1) : ℝ) * fp.u) ≤
            1 - (j : ℝ) * fp.u := by
          push_cast
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ j by positivity) (sq_nonneg fp.u),
            sq_nonneg fp.u]
        have hmul := mul_le_mul_of_nonneg_left hstep (p53_pow_nonneg fp j)
        rw [pow_succ]
        calc
          (1 + fp.u) ^ j * (1 + fp.u) * (1 - (↑(j + 1) : ℝ) * fp.u) ≤
              (1 + fp.u) ^ j * (1 - (j : ℝ) * fp.u) := by
                nlinarith [hmul]
          _ ≤ 1 := ih hj'
  have hden : 0 < 1 - (k : ℝ) * fp.u := by
    dsimp [P53GammaValid] at hk
    linarith
  apply (le_div_iff₀ hden).2
  dsimp [p53Gamma]
  nlinarith [hcore k hk]

private lemma p53Dot_succ (fp : P53FPModel) (n : ℕ) (hn : 0 < n)
    (a x : Fin (n + 1) → ℝ) :
    p53Dot fp (n + 1) a x =
      fp.fl_add
        (p53Dot fp n (fun i => a i.castSucc) (fun i => x i.castSucc))
        (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) := by
  cases n with
  | zero => omega
  | succ k =>
      simp only [p53Dot, Fin.foldl_succ_last]
      simp

private lemma p53_dot_pow (fp : P53FPModel) :
    ∀ k : ℕ, ∀ a x : Fin (k + 1) → ℝ,
      |p53Dot fp (k + 1) a x - ∑ i : Fin (k + 1), a i * x i| ≤
        ((1 + fp.u) ^ (k + 1) - 1) *
          ∑ i : Fin (k + 1), |a i| * |x i| := by
  intro k
  induction k with
  | zero =>
      intro a x
      simpa [p53Dot, pow_one, abs_mul] using p53_mul_error fp (a 0) (x 0)
  | succ k ih =>
      intro a x
      let ap : Fin (k + 1) → ℝ := fun i => a i.castSucc
      let xp : Fin (k + 1) → ℝ := fun i => x i.castSucc
      let s : ℝ := ∑ i : Fin (k + 1), ap i * xp i
      let S : ℝ := ∑ i : Fin (k + 1), |ap i| * |xp i|
      let t : ℝ := a (Fin.last (k + 1)) * x (Fin.last (k + 1))
      let T : ℝ := |a (Fin.last (k + 1))| * |x (Fin.last (k + 1))|
      have hT : 0 ≤ T := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have hs : |s| ≤ S := by
        calc
          _ ≤ ∑ i : Fin (k + 1), |ap i * xp i| := Finset.abs_sum_le_sum_abs _ _
          _ = S := by simp [S, abs_mul]
      have ht : |t| ≤ T := by simp [t, T, abs_mul]
      have hv : |p53Dot fp (k + 1) ap xp - s| ≤
          ((1 + fp.u) ^ (k + 1) - 1) * S := ih ap xp
      have hbase : fp.u ≤ (1 + fp.u) ^ (k + 1) - 1 := by
        have := p53_pow_ge_base fp (k + 1) (by omega)
        linarith
      have hw : |fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1))) - t| ≤
          ((1 + fp.u) ^ (k + 1) - 1) * T := by
        calc
          _ ≤ fp.u * T := by
            simpa [t, T, abs_mul] using
              (p53_mul_error fp (a (Fin.last (k + 1))) (x (Fin.last (k + 1))))
          _ ≤ _ := mul_le_mul_of_nonneg_right hbase hT
      have hres := p53_add_combine fp
        (p53Dot fp (k + 1) ap xp)
        (fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1))))
        s t S T ((1 + fp.u) ^ (k + 1))
        hs ht hv hw
      simpa [p53Dot_succ, Fin.sum_univ_castSucc, ap, xp, s, S, t, T,
        pow_succ, mul_comm] using hres

private lemma p53_sum_pow_split (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, f i) =
      (∑ i : Fin (2 ^ r), f ⟨i.val, p53_left_lt r i⟩) +
      (∑ i : Fin (2 ^ r), f ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ, two_mul, mul_comm]
  let g : Fin (2 ^ r + 2 ^ r) → ℝ := fun i => f (Fin.cast hpow.symm i)
  calc
    (∑ i, f i) = ∑ i, g i := (Fin.sum_congr' f hpow.symm).symm
    _ = (∑ i, g (Fin.castAdd (2 ^ r) i)) +
        (∑ i, g (Fin.natAdd (2 ^ r) i)) := Fin.sum_univ_add g
    _ = _ := by
      simp [g, Fin.castAdd, Fin.natAdd, Nat.add_comm]
      apply Finset.sum_congr rfl
      intro i _
      congr 1

private lemma p53_pairwise_pow (fp : P53FPModel) :
    ∀ r : ℕ, ∀ v w : Fin (2 ^ r) → ℝ,
      (∀ i, |v i - w i| ≤ fp.u * |w i|) →
      |p53PairwiseSum fp r v - ∑ i, w i| ≤
        ((1 + fp.u) ^ (r + 1) - 1) * ∑ i, |w i| := by
  intro r
  induction r with
  | zero =>
      intro v w hv
      simpa [p53PairwiseSum, pow_one] using hv (⟨0, by norm_num⟩ : Fin (2 ^ 0))
  | succ r ih =>
      intro v w hv
      let vL : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
      let wL : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val, p53_left_lt r i⟩
      let vR : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      let wR : Fin (2 ^ r) → ℝ := fun i => w ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      let s : ℝ := ∑ i, wL i
      let t : ℝ := ∑ i, wR i
      let S : ℝ := ∑ i, |wL i|
      let T : ℝ := ∑ i, |wR i|
      have hs : |s| ≤ S := Finset.abs_sum_le_sum_abs _ _
      have ht : |t| ≤ T := Finset.abs_sum_le_sum_abs _ _
      have hvL : |p53PairwiseSum fp r vL - s| ≤
          ((1 + fp.u) ^ (r + 1) - 1) * S :=
        ih vL wL (fun i => hv ⟨i.val, p53_left_lt r i⟩)
      have hvR : |p53PairwiseSum fp r vR - t| ≤
          ((1 + fp.u) ^ (r + 1) - 1) * T :=
        ih vR wR (fun i => hv ⟨i.val + 2 ^ r, p53_right_lt r i⟩)
      have hres := p53_add_combine fp
        (p53PairwiseSum fp r vL) (p53PairwiseSum fp r vR)
        s t S T ((1 + fp.u) ^ (r + 1))
        hs ht hvL hvR
      simpa [p53PairwiseSum, p53_sum_pow_split, vL, vR, wL, wR,
        s, t, S, T, pow_succ, mul_comm] using hres

private lemma p53_scalarPad_sum (n m : ℕ) (h : n ≤ m) (v : Fin n → ℝ) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i : Fin n, v i := by
  have he : n + (m - n) = m := Nat.add_sub_of_le h
  let g : Fin (n + (m - n)) → ℝ := fun i => p53ScalarPad n m v (Fin.cast he i)
  have hgL : ∀ i : Fin n, g (Fin.castAdd (m - n) i) = v i := by
    intro i
    simp [g, p53ScalarPad, Fin.castAdd, i.isLt]
  have hgR : ∀ i : Fin (m - n), g (Fin.natAdd n i) = 0 := by
    intro i
    simp [g, p53ScalarPad, Fin.natAdd, show ¬ n + i.val < n by omega]
  calc
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i, g i :=
      (Fin.sum_congr' (p53ScalarPad n m v) he).symm
    _ = (∑ i, g (Fin.castAdd (m - n) i)) +
        (∑ i, g (Fin.natAdd n i)) := Fin.sum_univ_add g
    _ = ∑ i : Fin n, v i := by simp [hgL, hgR]

private lemma p53_cascade_pow (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) :
    |p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i| ≤
      ((1 + fp.u) ^ (Nat.clog 2 n + 1) - 1) *
        ∑ i : Fin n, |a i| * |x i| := by
  let r := Nat.clog 2 n
  let m := 2 ^ r
  let v : Fin m → ℝ := p53ZeroPad n (fun i => fp.fl_mul (a i) (x i))
  let w : Fin m → ℝ := p53ZeroPad n (fun i => a i * x i)
  have hnm : n ≤ m := Nat.le_pow_clog (by omega) n
  have hv : ∀ i : Fin m, |v i - w i| ≤ fp.u * |w i| := by
    intro i
    dsimp [v, w, p53ZeroPad, p53ScalarPad]
    split_ifs with hi
    · exact p53_mul_error fp (a ⟨i.val, hi⟩) (x ⟨i.val, hi⟩)
    · simp
  have hsum : (∑ i : Fin m, w i) = ∑ i : Fin n, a i * x i := by
    simpa [w, p53ZeroPad] using
      (p53_scalarPad_sum n m hnm (fun i => a i * x i))
  have habs : (∑ i : Fin m, |w i|) = ∑ i : Fin n, |a i| * |x i| := by
    have hpoint : ∀ i : Fin m,
        |w i| = p53ScalarPad n m (fun j => |a j| * |x j|) i := by
      intro i
      dsimp [w, p53ZeroPad, p53ScalarPad]
      split_ifs <;> simp [abs_mul]
    simp_rw [hpoint]
    exact p53_scalarPad_sum n m hnm (fun i => |a i| * |x i|)
  have hcore := p53_pairwise_pow fp r v w hv
  rw [hsum, habs] at hcore
  simpa [p53CascadeDot, p53CascadeSum, v, r, m] using hcore

private lemma p53_clog_succ_le (n : ℕ) (hn : 0 < n) :
    Nat.clog 2 n + 1 ≤ n := by
  have hpow : ∀ j : ℕ, j + 1 ≤ 2 ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
        rw [pow_succ]
        omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hlog : Nat.clog 2 (j + 1) ≤ j := Nat.clog_le_of_le_pow (hpow j)
  simpa only [Nat.succ_eq_add_one] using Nat.succ_le_succ hlog

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
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |a i| * |x i| :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hvalid (k : ℕ) (hkn : k ≤ n) : P53GammaValid fp.u k := by
    dsimp [P53GammaValid] at *
    have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    nlinarith [mul_le_mul_of_nonneg_right hcast fp.u_nonneg]
  constructor
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact (p53_dot_pow fp k a x).trans
      (mul_le_mul_of_nonneg_right (p53_pow_gamma fp (k + 1) hrec) hsum_nonneg)
  · have hd : Nat.clog 2 n + 1 ≤ n := p53_clog_succ_le n hn
    exact (p53_cascade_pow fp n a x).trans
      (mul_le_mul_of_nonneg_right
        (p53_pow_gamma fp (Nat.clog 2 n + 1) (hvalid _ hd)) hsum_nonneg)

end VSCLReuse

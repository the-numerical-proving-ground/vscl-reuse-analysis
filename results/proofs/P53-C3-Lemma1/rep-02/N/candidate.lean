import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p53_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P53GammaValid u (k + 1)) :
    p53Gamma u k * (1 + u) + u ≤ p53Gamma u (k + 1) := by
  have hk0 : 0 < 1 - (k : ℝ) * u := by
    unfold P53GammaValid at hk
    push_cast at hk
    nlinarith
  have hk1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by
    unfold P53GammaValid at hk
    linarith
  unfold p53Gamma
  push_cast
  have heq : (k : ℝ) * u / (1 - (k : ℝ) * u) * (1 + u) + u =
      ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
    field_simp
    ring
  rw [heq]
  norm_cast
  apply (div_le_div_iff₀ hk0 hk1).2
  have hden : 1 - ((k + 1 : ℕ) : ℝ) * u ≤ 1 - (k : ℝ) * u := by
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_left hden (mul_nonneg (by positivity) hu)

private lemma p53_gamma_mono (u : ℝ) (hu : 0 ≤ u) {j k : ℕ}
    (hjk : j ≤ k) (hk : P53GammaValid u k) :
    p53Gamma u j ≤ p53Gamma u k := by
  have hj0 : 0 < 1 - (j : ℝ) * u := by
    unfold P53GammaValid at hk
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith
  have hk0 : 0 < 1 - (k : ℝ) * u := by
    unfold P53GammaValid at hk
    linarith
  unfold p53Gamma
  apply (div_le_div_iff₀ hj0 hk0).2
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith [mul_nonneg (show 0 ≤ (j : ℝ) by positivity) hu,
    mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hu]

private lemma p53_mul_error (fp : P53FPModel) (a x : ℝ) :
    |fp.fl_mul a x - a * x| ≤ fp.u * (|a| * |x|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a x
  rw [hfl]
  have heq : a * x * (1 + δ) - a * x = a * x * δ := by ring
  rw [heq, abs_mul, abs_mul]
  calc
    |a| * |x| * |δ| ≤ |a| * |x| * fp.u :=
      mul_le_mul_of_nonneg_left hδ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = fp.u * (|a| * |x|) := by ring

private lemma p53_add_error (fp : P53FPModel)
    (s t S T m₁ m₂ g G : ℝ)
    (hm₁ : 0 ≤ m₁) (hm₂ : 0 ≤ m₂)
    (hS : |S| ≤ m₁) (hT : |T| ≤ m₂)
    (hs : |s - S| ≤ g * m₁) (ht : |t - T| ≤ g * m₂)
    (hstep : g * (1 + fp.u) + fp.u ≤ G) :
    |fp.fl_add s t - (S + T)| ≤ G * (m₁ + m₂) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add s t
  have hst : |s + t| ≤ (1 + g) * (m₁ + m₂) := by
    have h₁ : |s| ≤ |s - S| + |S| := by
      have := abs_add_le (s - S) S
      convert this using 1 <;> ring
    have h₂ : |t| ≤ |t - T| + |T| := by
      have := abs_add_le (t - T) T
      convert this using 1 <;> ring
    calc
      |s + t| ≤ |s| + |t| := abs_add_le _ _
      _ ≤ (1 + g) * (m₁ + m₂) := by nlinarith
  have hmain : |fp.fl_add s t - (S + T)| ≤
      |s - S| + |t - T| + fp.u * |s + t| := by
    have heq : fp.fl_add s t - (S + T) =
        (s - S) + (t - T) + δ * (s + t) := by rw [hfl]; ring
    rw [heq]
    calc
      _ ≤ |s - S| + |t - T| + |δ * (s + t)| := by
        have h := abs_add_le ((s - S) + (t - T)) (δ * (s + t))
        have h' := abs_add_le (s - S) (t - T)
        linarith
      _ = |s - S| + |t - T| + |δ| * |s + t| := by rw [abs_mul]
      _ ≤ |s - S| + |t - T| + fp.u * |s + t| := by
        gcongr
  have huprod : fp.u * |s + t| ≤ fp.u * ((1 + g) * (m₁ + m₂)) :=
    mul_le_mul_of_nonneg_left hst fp.u_nonneg
  have hgam : (g * (1 + fp.u) + fp.u) * (m₁ + m₂) ≤ G * (m₁ + m₂) :=
    mul_le_mul_of_nonneg_right hstep (add_nonneg hm₁ hm₂)
  nlinarith

private lemma p53_halves_sum (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f ⟨i.val, p53_left_lt r i⟩) +
      (∑ i : Fin (2 ^ r), f ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ]
    omega
  calc
    (∑ i : Fin (2 ^ (r + 1)), f i) =
        ∑ i : Fin (2 ^ r + 2 ^ r), f (Fin.cast hp.symm i) := by
      symm
      exact Fin.sum_congr' f hp.symm
    _ = _ := by
      rw [Fin.sum_univ_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        apply congrArg f <;> apply Fin.ext <;> simp [Fin.natAdd, Nat.add_comm]

private lemma p53_dot_succ_succ (fp : P53FPModel) (k : ℕ)
    (a x : Fin (k + 2) → ℝ) :
    p53Dot fp (k + 2) a x =
      fp.fl_add
        (p53Dot fp (k + 1) (fun i => a i.castSucc) (fun i => x i.castSucc))
        (fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))) := by
  change Fin.foldl (k + 1)
    (fun acc t => fp.fl_add acc (fp.fl_mul (a t.succ) (x t.succ)))
    (fp.fl_mul (a 0) (x 0)) = _
  rw [Fin.foldl_succ_last]
  rfl

private lemma p53_dot_bound (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hn : 0 < n) (hv : P53GammaValid fp.u n) :
    |p53Dot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u n * ∑ i : Fin n, |a i| * |x i| := by
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      have hu : fp.u ≤ p53Gamma fp.u 1 := by
        simpa [p53Gamma] using p53_gamma_step fp.u fp.u_nonneg 0 hv
      have hm : 0 ≤ |a 0| * |x 0| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      have herr := p53_mul_error fp (a 0) (x 0)
      have hmul := mul_le_mul_of_nonneg_right hu hm
      simpa [p53Dot, Fin.sum_univ_one] using herr.trans hmul
    | succ k =>
      let a' : Fin (k + 1) → ℝ := fun i => a i.castSucc
      let x' : Fin (k + 1) → ℝ := fun i => x i.castSucc
      let S : ℝ := ∑ i : Fin (k + 1), a' i * x' i
      let M : ℝ := ∑ i : Fin (k + 1), |a' i| * |x' i|
      let T : ℝ := a (Fin.last (k + 1)) * x (Fin.last (k + 1))
      let m : ℝ := |a (Fin.last (k + 1))| * |x (Fin.last (k + 1))|
      have hprev : P53GammaValid fp.u (k + 1) := by
        unfold P53GammaValid at *
        push_cast at hv ⊢
        nlinarith [fp.u_nonneg]
      have hvalid1 : P53GammaValid fp.u 1 := by
        unfold P53GammaValid at *
        push_cast at hv ⊢
        nlinarith [fp.u_nonneg]
      have hs : |p53Dot fp (k + 1) a' x' - S| ≤ p53Gamma fp.u (k + 1) * M :=
        ih a' x' (by omega) hprev
      have hM : 0 ≤ M := Finset.sum_nonneg (by intro i hi; positivity)
      have hm : 0 ≤ m := by dsimp [m]; positivity
      have hS : |S| ≤ M := by
        dsimp [S, M]
        simpa only [abs_mul] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin (k + 1) => a' i * x' i))
      have hT : |T| ≤ m := by simp [T, m, abs_mul]
      have hgam1 : fp.u ≤ p53Gamma fp.u 1 := by
        simpa [p53Gamma] using p53_gamma_step fp.u fp.u_nonneg 0 hvalid1
      have hmon : p53Gamma fp.u 1 ≤ p53Gamma fp.u (k + 1) :=
        p53_gamma_mono fp.u fp.u_nonneg (by omega) hprev
      have ht : |fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1))) - T| ≤
          p53Gamma fp.u (k + 1) * m := by
        exact (p53_mul_error fp _ _).trans
          ((mul_le_mul_of_nonneg_right (hgam1.trans hmon) hm))
      have hadd := p53_add_error fp
        (p53Dot fp (k + 1) a' x')
        (fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1))))
        S T M m (p53Gamma fp.u (k + 1)) (p53Gamma fp.u (k + 2))
        hM hm hS hT hs ht (p53_gamma_step fp.u fp.u_nonneg (k + 1) hv)
      simpa only [p53_dot_succ_succ, Fin.sum_univ_castSucc, a', x', S, T, M, m]
        using hadd

private lemma p53_pairwise_bound (fp : P53FPModel) (r : ℕ)
    (v e : Fin (2 ^ r) → ℝ) (hv : P53GammaValid fp.u (r + 1))
    (hterm : ∀ i, |v i - e i| ≤ fp.u * |e i|) :
    |p53PairwiseSum fp r v - ∑ i : Fin (2 ^ r), e i| ≤
      p53Gamma fp.u (r + 1) * ∑ i : Fin (2 ^ r), |e i| := by
  induction r with
  | zero =>
    have hu : fp.u ≤ p53Gamma fp.u 1 := by
      simpa [p53Gamma] using p53_gamma_step fp.u fp.u_nonneg 0 hv
    have hm : 0 ≤ |e 0| := abs_nonneg _
    simpa [p53PairwiseSum, Fin.sum_univ_one] using
      (hterm 0).trans (mul_le_mul_of_nonneg_right hu hm)
  | succ r ih =>
    let vL : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
    let vR : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
    let eL : Fin (2 ^ r) → ℝ := fun i => e ⟨i.val, p53_left_lt r i⟩
    let eR : Fin (2 ^ r) → ℝ := fun i => e ⟨i.val + 2 ^ r, p53_right_lt r i⟩
    let S : ℝ := ∑ i : Fin (2 ^ r), eL i
    let T : ℝ := ∑ i : Fin (2 ^ r), eR i
    let M : ℝ := ∑ i : Fin (2 ^ r), |eL i|
    let N : ℝ := ∑ i : Fin (2 ^ r), |eR i|
    have hchild : P53GammaValid fp.u (r + 1) := by
      unfold P53GammaValid at *
      push_cast at hv ⊢
      nlinarith [fp.u_nonneg]
    have hL : |p53PairwiseSum fp r vL - S| ≤ p53Gamma fp.u (r + 1) * M :=
      ih vL eL hchild (fun i => hterm _)
    have hR : |p53PairwiseSum fp r vR - T| ≤ p53Gamma fp.u (r + 1) * N :=
      ih vR eR hchild (fun i => hterm _)
    have hM : 0 ≤ M := Finset.sum_nonneg (by intro i hi; positivity)
    have hN : 0 ≤ N := Finset.sum_nonneg (by intro i hi; positivity)
    have hS : |S| ≤ M := by
      dsimp [S, M]
      exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := eL)
    have hT : |T| ≤ N := by
      dsimp [T, N]
      exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := eR)
    have hadd := p53_add_error fp
      (p53PairwiseSum fp r vL) (p53PairwiseSum fp r vR)
      S T M N (p53Gamma fp.u (r + 1)) (p53Gamma fp.u (r + 2))
      hM hN hS hT hL hR (p53_gamma_step fp.u fp.u_nonneg (r + 1) hv)
    simpa only [p53PairwiseSum, p53_halves_sum, vL, vR, eL, eR, S, T, M, N]
      using hadd

private lemma p53_clog_succ_le (n : ℕ) (hn : 0 < n) :
    Nat.clog 2 n + 1 ≤ n := by
  have hpow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      omega
  cases n with
  | zero => omega
  | succ k =>
    have hc : Nat.clog 2 (k + 1) ≤ k := Nat.clog_le_of_le_pow (hpow k)
    omega

private lemma p53_scalar_pad_sum (n m : ℕ) (v : Fin n → ℝ) (hnm : n ≤ m) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i : Fin n, v i := by
  have hp : m = n + (m - n) := by omega
  calc
    (∑ i : Fin m, p53ScalarPad n m v i) =
        ∑ i : Fin (n + (m - n)), p53ScalarPad n m v (Fin.cast hp.symm i) := by
      symm
      exact Fin.sum_congr' (p53ScalarPad n m v) hp.symm
    _ = _ := by
      rw [Fin.sum_univ_add]
      have hleft : (∑ i : Fin n,
          p53ScalarPad n m v (Fin.cast hp.symm (Fin.castAdd (m - n) i))) =
          ∑ i : Fin n, v i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [p53ScalarPad, Fin.cast, Fin.castAdd, i.isLt]
      have hright : (∑ i : Fin (m - n),
          p53ScalarPad n m v (Fin.cast hp.symm (Fin.natAdd n i))) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [p53ScalarPad, Fin.cast, Fin.natAdd]
      rw [hleft, hright, add_zero]

private lemma p53_cascade_bound (fp : P53FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hn : 0 < n) (hrec : P53GammaValid fp.u n) :
    |p53CascadeDot fp n a x - ∑ i : Fin n, a i * x i| ≤
      p53Gamma fp.u (Nat.clog 2 n + 1) *
        ∑ i : Fin n, |a i| * |x i| := by
  let r := Nat.clog 2 n
  have hrn : r + 1 ≤ n := p53_clog_succ_le n hn
  have hv : P53GammaValid fp.u (r + 1) := by
    unfold P53GammaValid at *
    have hcast : ((r + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hrec
  have hnm : n ≤ 2 ^ r := by
    dsimp [r]
    exact Nat.le_pow_clog (by norm_num) n
  let e : Fin (2 ^ r) → ℝ := p53ScalarPad n (2 ^ r) (fun i => a i * x i)
  let v : Fin (2 ^ r) → ℝ :=
    p53ScalarPad n (2 ^ r) (fun i => fp.fl_mul (a i) (x i))
  have hterm : ∀ i, |v i - e i| ≤ fp.u * |e i| := by
    intro i
    dsimp [v, e, p53ScalarPad]
    split_ifs with hi
    · simpa [abs_mul] using p53_mul_error fp (a ⟨i.val, hi⟩) (x ⟨i.val, hi⟩)
    · simp
  have hpad : (∑ i : Fin (2 ^ r), e i) = ∑ i : Fin n, a i * x i := by
    exact p53_scalar_pad_sum n (2 ^ r) (fun i => a i * x i) hnm
  have hpadAbs : (∑ i : Fin (2 ^ r), |e i|) =
      ∑ i : Fin n, |a i| * |x i| := by
    calc
      (∑ i : Fin (2 ^ r), |e i|) =
          ∑ i : Fin (2 ^ r), p53ScalarPad n (2 ^ r)
            (fun j => |a j| * |x j|) i := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [e, p53ScalarPad]
        split_ifs <;> simp [abs_mul]
      _ = _ := p53_scalar_pad_sum n (2 ^ r) (fun j => |a j| * |x j|) hnm
  have hb := p53_pairwise_bound fp r v e hv hterm
  rw [hpad, hpadAbs] at hb
  exact hb

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
  exact ⟨p53_dot_bound fp n a x hn hrec,
    p53_cascade_bound fp n a x hn hrec⟩

end VSCLReuse

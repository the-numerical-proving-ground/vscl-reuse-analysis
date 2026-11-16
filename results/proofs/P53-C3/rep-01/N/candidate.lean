import VSCLReuse.P53.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p53_mul_error (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul a b
  rw [hfl]
  have heq : a * b * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))]

private lemma p53_mul_abs (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_mul a b| ≤ (1 + fp.u) * |a * b| := by
  have h := p53_mul_error fp a b
  have htri := abs_add_le (fp.fl_mul a b - a * b) (a * b)
  have heq : fp.fl_mul a b - a * b + a * b = fp.fl_mul a b := by ring
  rw [heq] at htri
  nlinarith

private lemma p53_add_error (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * (|a| + |b|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  rw [hfl]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  calc
    |a + b| * |δ| ≤ |a + b| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ ≤ (|a| + |b|) * fp.u := mul_le_mul_of_nonneg_right (abs_add_le a b) fp.u_nonneg
    _ = _ := by ring

private lemma p53_add_abs (fp : P53FPModel) (a b : ℝ) :
    |fp.fl_add a b| ≤ (1 + fp.u) * (|a| + |b|) := by
  have h := p53_add_error fp a b
  have htri := abs_add_le (fp.fl_add a b - (a + b)) (a + b)
  have heq : fp.fl_add a b - (a + b) + (a + b) = fp.fl_add a b := by ring
  rw [heq] at htri
  have hab := abs_add_le a b
  nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hab)]

private lemma p53_pow_budget (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : (k : ℝ) * u < 1) :
    (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hk' : (k : ℝ) * u < 1 := by
        have hc : (k : ℝ) ≤ (↑(k + 1) : ℝ) := by exact_mod_cast (Nat.le_succ k)
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) hu]
      have h0 := ih hk'
      have hp : 0 ≤ (1 + u) ^ k := pow_nonneg (by positivity) _
      have hsq : 0 ≤ (k + 1 : ℝ) * u ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg u)
      have hstep : (1 + u) * (1 - (↑(k + 1) : ℝ) * u) ≤
          1 - (k : ℝ) * u := by
        push_cast
        nlinarith
      calc
        (1 + u) ^ (k + 1) * (1 - (↑(k + 1) : ℝ) * u) =
            (1 + u) ^ k * ((1 + u) * (1 - (↑(k + 1) : ℝ) * u)) := by
              rw [pow_succ]; ring
        _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hstep hp
        _ ≤ 1 := h0

private lemma p53_pow_sub_one_le_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P53GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p53Gamma u k := by
  have hd : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk
  have hb := p53_pow_budget u hu k hk
  unfold p53Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private lemma p53_pow_mono (u : ℝ) (hu : 0 ≤ u) {k l : ℕ} (hkl : k ≤ l) :
    (1 + u) ^ k ≤ (1 + u) ^ l := by
  exact pow_le_pow_right₀ (by linarith) hkl

private lemma p53_dot_succ_last (fp : P53FPModel) (k : ℕ)
    (a x : Fin (k + 2) → ℝ) :
    p53Dot fp (k + 2) a x =
      fp.fl_add
        (p53Dot fp (k + 1) (fun t => a t.castSucc) (fun t => x t.castSucc))
        (fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))) := by
  simp only [p53Dot, Fin.foldl_succ_last]
  rfl

private lemma p53_dot_pow_bound (fp : P53FPModel) (k : ℕ)
    (a x : Fin (k + 1) → ℝ) :
    |p53Dot fp (k + 1) a x - ∑ t : Fin (k + 1), a t * x t| ≤
      ((1 + fp.u) ^ (k + 1) - 1) *
        (∑ t : Fin (k + 1), |a t * x t|) := by
  induction k with
  | zero =>
      simpa [p53Dot, Fin.sum_univ_one] using p53_mul_error fp (a 0) (x 0)
  | succ k ih =>
      let a' : Fin (k + 1) → ℝ := fun t => a t.castSucc
      let x' : Fin (k + 1) → ℝ := fun t => x t.castSucc
      let z := p53Dot fp (k + 1) a' x'
      let y := fp.fl_mul (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))
      let t := a (Fin.last (k + 1)) * x (Fin.last (k + 1))
      let T := ∑ j : Fin (k + 1), a' j * x' j
      let S := ∑ j : Fin (k + 1), |a' j * x' j|
      let B := (1 + fp.u) ^ (k + 1)
      have hprev : |z - T| ≤ (B - 1) * S := ih a' x'
      have hT : |T| ≤ S := Finset.abs_sum_le_sum_abs _ _
      have hS : 0 ≤ S := Finset.sum_nonneg (by intro j hj; exact abs_nonneg _)
      have hz : |z| ≤ B * S := by
        have htri := abs_add_le (z - T) T
        have heq : z - T + T = z := by ring
        rw [heq] at htri
        nlinarith
      have hy := p53_mul_abs fp (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))
      have he := p53_mul_error fp (a (Fin.last (k + 1))) (x (Fin.last (k + 1)))
      have ha := p53_add_error fp z y
      have htri₁ := abs_add_le (fp.fl_add z y - (z + y)) ((z - T) + (y - t))
      have htri₂ := abs_add_le (z - T) (y - t)
      have hmain : |fp.fl_add z y - (T + t)| ≤
          fp.u * (|z| + |y|) + (B - 1) * S + fp.u * |t| := by
        have heq : fp.fl_add z y - (T + t) =
            (fp.fl_add z y - (z + y)) + ((z - T) + (y - t)) := by ring
        rw [heq]
        linarith
      have hpow2 : (1 + fp.u) ^ 2 ≤ (1 + fp.u) ^ (k + 2) :=
        p53_pow_mono fp.u fp.u_nonneg (by omega)
      have hstep : |fp.fl_add z y - (T + t)| ≤
          ((1 + fp.u) ^ (k + 2) - 1) * (S + |t|) := by
        have hmul1 : fp.u * |z| ≤ fp.u * (B * S) :=
          mul_le_mul_of_nonneg_left hz fp.u_nonneg
        have hmul2 : fp.u * |y| ≤ fp.u * ((1 + fp.u) * |t|) :=
          mul_le_mul_of_nonneg_left hy fp.u_nonneg
        have hterm : ((1 + fp.u) ^ 2 - 1) * |t| ≤
            ((1 + fp.u) ^ (k + 2) - 1) * |t| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        have hpow : (1 + fp.u) ^ (k + 2) = (1 + fp.u) * B := by
          simp [B, pow_succ]; ring
        rw [hpow] at hterm ⊢
        have hsq : (1 + fp.u) ^ 2 = (1 + fp.u) * (1 + fp.u) := by ring
        rw [hsq] at hterm
        nlinarith
      simpa only [p53_dot_succ_last, Fin.sum_univ_castSucc, a', x', z, y, t, T, S]
        using hstep

private lemma p53_sum_halves {α : Type*} [AddCommMonoid α] (r : ℕ)
    (v : Fin (2 ^ (r + 1)) → α) :
    (∑ i, v i) =
      (∑ i : Fin (2 ^ r), v ⟨i.val, p53_left_lt r i⟩) +
        (∑ i : Fin (2 ^ r), v ⟨i.val + 2 ^ r, p53_right_lt r i⟩) := by
  have heq : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by simp [pow_succ, mul_two]
  let f : ℕ → α := fun i => if h : i < 2 ^ (r + 1) then v ⟨i, h⟩ else 0
  have htotal : (∑ i : Fin (2 ^ (r + 1)), v i) =
      ∑ i ∈ Finset.range (2 ^ (r + 1)), f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, i.isLt]
  have hleft : (∑ i : Fin (2 ^ r), v ⟨i.val, p53_left_lt r i⟩) =
      ∑ i ∈ Finset.range (2 ^ r), f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, p53_left_lt]
  have hright : (∑ i : Fin (2 ^ r), v ⟨i.val + 2 ^ r, p53_right_lt r i⟩) =
      ∑ i ∈ Finset.range (2 ^ r), f (2 ^ r + i) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, p53_right_lt, add_comm]
  rw [htotal, hleft, hright, heq, Finset.sum_range_add]

private lemma p53_pairwise_pow_bound (fp : P53FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) :
    |p53PairwiseSum fp r v - ∑ i, v i| ≤
      ((1 + fp.u) ^ r - 1) * (∑ i, |v i|) := by
  induction r with
  | zero => simp [p53PairwiseSum]
  | succ r ih =>
      let vL : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, p53_left_lt r i⟩
      let vR : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, p53_right_lt r i⟩
      let zL := p53PairwiseSum fp r vL
      let zR := p53PairwiseSum fp r vR
      let TL := ∑ i, vL i
      let TR := ∑ i, vR i
      let SL := ∑ i, |vL i|
      let SR := ∑ i, |vR i|
      let B := (1 + fp.u) ^ r
      have hL : |zL - TL| ≤ (B - 1) * SL := ih vL
      have hR : |zR - TR| ≤ (B - 1) * SR := ih vR
      have hTL : |TL| ≤ SL := Finset.abs_sum_le_sum_abs _ _
      have hTR : |TR| ≤ SR := Finset.abs_sum_le_sum_abs _ _
      have hSL : 0 ≤ SL := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have hSR : 0 ≤ SR := Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)
      have hzL : |zL| ≤ B * SL := by
        have htri := abs_add_le (zL - TL) TL
        have heq : zL - TL + TL = zL := by ring
        rw [heq] at htri
        nlinarith
      have hzR : |zR| ≤ B * SR := by
        have htri := abs_add_le (zR - TR) TR
        have heq : zR - TR + TR = zR := by ring
        rw [heq] at htri
        nlinarith
      have ha := p53_add_error fp zL zR
      have htri₁ := abs_add_le (fp.fl_add zL zR - (zL + zR))
        ((zL - TL) + (zR - TR))
      have htri₂ := abs_add_le (zL - TL) (zR - TR)
      have hmain : |fp.fl_add zL zR - (TL + TR)| ≤
          fp.u * (|zL| + |zR|) + (B - 1) * (SL + SR) := by
        have heq : fp.fl_add zL zR - (TL + TR) =
            (fp.fl_add zL zR - (zL + zR)) + ((zL - TL) + (zR - TR)) := by ring
        rw [heq]
        nlinarith
      have hmulL : fp.u * |zL| ≤ fp.u * (B * SL) :=
        mul_le_mul_of_nonneg_left hzL fp.u_nonneg
      have hmulR : fp.u * |zR| ≤ fp.u * (B * SR) :=
        mul_le_mul_of_nonneg_left hzR fp.u_nonneg
      have hstep : |fp.fl_add zL zR - (TL + TR)| ≤
          ((1 + fp.u) ^ (r + 1) - 1) * (SL + SR) := by
        rw [pow_succ]
        nlinarith
      have hsum := p53_sum_halves r v
      have habs := p53_sum_halves r (fun i => |v i|)
      simpa only [p53PairwiseSum, vL, vR, zL, zR, TL, TR, SL, SR, hsum, habs]
        using hstep

private lemma p53_scalar_pad_sum
    (n m : ℕ) (hnm : n ≤ m) (v : Fin n → ℝ) :
    (∑ i : Fin m, p53ScalarPad n m v i) = ∑ i : Fin n, v i := by
  let f : ℕ → ℝ := fun i => if h : i < n then v ⟨i, h⟩ else 0
  have hm : (∑ i : Fin m, p53ScalarPad n m v i) =
      ∑ i ∈ Finset.range m, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [p53ScalarPad, f]
  have hn : (∑ i : Fin n, v i) = ∑ i ∈ Finset.range n, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, i.isLt]
  rw [hm, hn, show m = n + (m - n) by omega, Finset.sum_range_add]
  have htail : (∑ i ∈ Finset.range (m - n), f (n + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [f]
  simp [htail]

private lemma p53_sum_mul_error (fp : P53FPModel) {ι : Type*} [Fintype ι]
    (a x : ι → ℝ) :
    |(∑ i, fp.fl_mul (a i) (x i)) - ∑ i, a i * x i| ≤
      fp.u * (∑ i, |a i * x i|) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    |∑ i, (fp.fl_mul (a i) (x i) - a i * x i)| ≤
        ∑ i, |fp.fl_mul (a i) (x i) - a i * x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, fp.u * |a i * x i| :=
      Finset.sum_le_sum (by intro i hi; exact p53_mul_error fp (a i) (x i))

private lemma p53_sum_mul_abs (fp : P53FPModel) {ι : Type*} [Fintype ι]
    (a x : ι → ℝ) :
    (∑ i, |fp.fl_mul (a i) (x i)|) ≤
      (1 + fp.u) * (∑ i, |a i * x i|) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (by intro i hi; exact p53_mul_abs fp (a i) (x i))

private lemma p53_cascade_dot_pow_bound (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    |p53CascadeDot fp k a x - ∑ i, a i * x i| ≤
      ((1 + fp.u) ^ (Nat.clog 2 k + 1) - 1) *
        (∑ i, |a i * x i|) := by
  let r := Nat.clog 2 k
  let v : Fin k → ℝ := fun i => fp.fl_mul (a i) (x i)
  let w : Fin (2 ^ r) → ℝ := p53ZeroPad k v
  let T := ∑ i : Fin k, a i * x i
  let V := ∑ i : Fin k, v i
  let S := ∑ i : Fin k, |a i * x i|
  let W := ∑ i : Fin k, |v i|
  let B := (1 + fp.u) ^ r
  have hkm : k ≤ 2 ^ r := Nat.le_pow_clog (by norm_num) k
  have hsum : (∑ i : Fin (2 ^ r), w i) = V :=
    p53_scalar_pad_sum k (2 ^ r) hkm v
  have habs : (∑ i : Fin (2 ^ r), |w i|) = W := by
    have heq : (fun i : Fin (2 ^ r) => |w i|) =
        p53ZeroPad k (fun i => |v i|) := by
      funext i
      simp only [w, p53ZeroPad, p53ScalarPad]
      split_ifs <;> simp
    rw [heq]
    exact p53_scalar_pad_sum k (2 ^ r) hkm (fun i => |v i|)
  have hp : |p53PairwiseSum fp r w - V| ≤ (B - 1) * W := by
    simpa only [hsum, habs, B] using p53_pairwise_pow_bound fp r w
  have he : |V - T| ≤ fp.u * S := p53_sum_mul_error fp a x
  have hw : W ≤ (1 + fp.u) * S := p53_sum_mul_abs fp a x
  have hB : 0 ≤ B - 1 := by
    have h1 : 1 ≤ B := one_le_pow₀ (by linarith [fp.u_nonneg])
    linarith
  have hW := mul_le_mul_of_nonneg_left hw hB
  have htri := abs_add_le (p53PairwiseSum fp r w - V) (V - T)
  have heq : p53PairwiseSum fp r w - V + (V - T) =
      p53PairwiseSum fp r w - T := by ring
  rw [heq] at htri
  have hpow : (1 + fp.u) ^ (r + 1) = B * (1 + fp.u) := by
    simp [B, pow_succ]
  simpa only [p53CascadeDot, p53CascadeSum, r, v, w, T, S, hpow] using
    (show |p53PairwiseSum fp r w - T| ≤
        ((1 + fp.u) ^ (r + 1) - 1) * S by
      rw [hpow]
      nlinarith)

private lemma p53_pow_error_le_gamma (u : ℝ) (hu : 0 ≤ u) {k l : ℕ}
    (hkl : k ≤ l) (hl : P53GammaValid u l) :
    (1 + u) ^ k - 1 ≤ p53Gamma u l := by
  calc
    (1 + u) ^ k - 1 ≤ (1 + u) ^ l - 1 := by
      linarith [p53_pow_mono u hu hkl]
    _ ≤ p53Gamma u l := p53_pow_sub_one_le_gamma u hu l hl

private lemma p53_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P53GammaValid u k) : 0 ≤ p53Gamma u k := by
  unfold p53Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hk))

private lemma p53_schedule_sum {m n l : ℕ} (A : Fin m → Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin m) (f : Fin n → ℝ)
    (hf : ∀ j, A i j = 0 → f j = 0) :
    (∑ t : Fin (schedule.count i), f (schedule.col i t)) = ∑ j : Fin n, f j := by
  let s : Finset (Fin n) := Finset.univ.filter (fun j => A i j ≠ 0)
  have hs : (∑ t : Fin (schedule.count i), f (schedule.col i t)) =
      ∑ j ∈ s, f j := by
    apply Finset.sum_bij (fun t _ => schedule.col i t)
    · intro t ht
      simp [s, schedule.col_nonzero i t]
    · intro t ht t' ht' h
      exact schedule.col_injective i h
    · intro j hj
      obtain ⟨t, ht⟩ := schedule.covers i j (Finset.mem_filter.mp hj).2
      exact ⟨t, Finset.mem_univ _, ht⟩
    · intros
      rfl
  rw [hs]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : A i j = 0
  · simp [h, hf j h]
  · simp [h]

private lemma p53_clog_add_one_le (l : ℕ) (hl : 1 ≤ l) :
    Nat.clog 2 l + 1 ≤ l := by
  have hpow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        omega
  have h := hpow (l - 1)
  have hs : l - 1 + 1 = l := by omega
  rw [hs] at h
  have hc := Nat.clog_le_of_le_pow h
  omega

private lemma p53_sign_abs_of_ne_zero {a : ℝ} (ha : a ≠ 0) :
    |p53Sign a| = 1 := by
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  simp [p53Sign, ha, abs_div, habs]

private lemma p53_coeff_error (fp : P53FPModel) {n : ℕ}
    (A Ahat : Fin n → Fin n → ℝ) (η : ℝ)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i j : Fin n) :
    |Ahat i j - A i j| ≤ (η * fp.u) * |p53Sign (A i j)| := by
  by_cases h : A i j = 0
  · simp [h, hzero i j h, p53Sign]
  · simpa [p53_sign_abs_of_ne_zero h] using hpre i j h

private lemma p53_row_coeff_bounds (fp : P53FPModel) {n : ℕ}
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ) (η : ℝ)
    (hpre : ∀ i j, A i j ≠ 0 → |Ahat i j - A i j| ≤ η * fp.u)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0)
    (i : Fin n) :
    |(∑ j, Ahat i j * x j) - ∑ j, A i j * x j| ≤
        (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) ∧
    (∑ j, |Ahat i j| * |x j|) ≤
        (∑ j, |A i j| * |x j|) +
          (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) := by
  have hpt (j : Fin n) :
      |Ahat i j * x j - A i j * x j| ≤
        (η * fp.u) * (|p53Sign (A i j)| * |x j|) := by
    have heq : Ahat i j * x j - A i j * x j = (Ahat i j - A i j) * x j := by ring
    rw [heq, abs_mul]
    have h := p53_coeff_error fp A Ahat η hpre hzero i j
    nlinarith [mul_le_mul_of_nonneg_right h (abs_nonneg (x j))]
  have hsum :
      (∑ j, |Ahat i j * x j - A i j * x j|) ≤
        (η * fp.u) * (∑ j, |p53Sign (A i j)| * |x j|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (by intro j hj; exact hpt j)
  constructor
  · rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hsum
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have htri := abs_add_le (Ahat i j - A i j) (A i j)
    have heq : Ahat i j - A i j + A i j = Ahat i j := by ring
    rw [heq] at htri
    have h := p53_coeff_error fp A Ahat η hpre hzero i j
    have hmul := mul_le_mul_of_nonneg_right htri (abs_nonneg (x j))
    have hmul' := mul_le_mul_of_nonneg_right h (abs_nonneg (x j))
    nlinarith

private lemma p53_dot_pow_bound_all (fp : P53FPModel) (k : ℕ)
    (a x : Fin k → ℝ) :
    |p53Dot fp k a x - ∑ t, a t * x t| ≤
      ((1 + fp.u) ^ k - 1) * (∑ t, |a t * x t|) := by
  cases k with
  | zero => simp [p53Dot]
  | succ k => exact p53_dot_pow_bound fp k a x

private lemma p53_finish (y T U P H R g e : ℝ)
    (hg : 0 ≤ g) (heval : |y - U| ≤ g * H)
    (hcoeff : |U - T| ≤ e * R) (habs : H ≤ P + e * R) :
    |y - T| ≤ g * P + (e + g * e) * R := by
  have htri := abs_add_le (y - U) (U - T)
  have heq : y - U + (U - T) = y - T := by ring
  rw [heq] at htri
  have hmul := mul_le_mul_of_nonneg_left habs hg
  nlinarith

private lemma p53_recursive_row_eval (fp : P53FPModel) {n l : ℕ}
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin n)
    (hvalid : P53GammaValid fp.u l)
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0) :
    |p53SparseMatVec fp A Ahat x schedule i - ∑ j, Ahat i j * x j| ≤
      p53Gamma fp.u l * (∑ j, |Ahat i j| * |x j|) := by
  let k := schedule.count i
  let a : Fin k → ℝ := fun t => Ahat i (schedule.col i t)
  let b : Fin k → ℝ := fun t => x (schedule.col i t)
  have hsum : (∑ t : Fin k, a t * b t) = ∑ j, Ahat i j * x j := by
    exact p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
      (by intro j hj; simp [hzero i j hj])
  have habs : (∑ t : Fin k, |a t * b t|) =
      ∑ j, |Ahat i j| * |x j| := by
    calc
      (∑ t : Fin k, |a t * b t|) = ∑ j, |Ahat i j * x j| := by
        exact p53_schedule_sum A schedule i (fun j => |Ahat i j * x j|)
          (by intro j hj; simp [hzero i j hj])
      _ = _ := by simp [abs_mul]
  have hpow := p53_dot_pow_bound_all fp k a b
  rw [hsum, habs] at hpow
  have hbudget := p53_pow_error_le_gamma fp.u fp.u_nonneg
    (schedule.count_le i) hvalid
  have hH : 0 ≤ (∑ j, |Ahat i j| * |x j|) :=
    Finset.sum_nonneg (by intro j hj; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hbudget hH
  change |p53Dot fp k a b - ∑ j, Ahat i j * x j| ≤
    p53Gamma fp.u l * (∑ j, |Ahat i j| * |x j|)
  exact hpow.trans hmul

private lemma p53_cascade_row_eval (fp : P53FPModel) {n l : ℕ}
    (A Ahat : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (schedule : P53SparseSchedule A l) (i : Fin n)
    (hvalid : P53GammaValid fp.u (Nat.clog 2 l + 1))
    (hzero : ∀ i j, A i j = 0 → Ahat i j = 0) :
    |p53SparseCascadeMatVec fp A Ahat x schedule i - ∑ j, Ahat i j * x j| ≤
      p53Gamma fp.u (Nat.clog 2 l + 1) *
        (∑ j, |Ahat i j| * |x j|) := by
  let k := schedule.count i
  let a : Fin k → ℝ := fun t => Ahat i (schedule.col i t)
  let b : Fin k → ℝ := fun t => x (schedule.col i t)
  have hsum : (∑ t : Fin k, a t * b t) = ∑ j, Ahat i j * x j := by
    exact p53_schedule_sum A schedule i (fun j => Ahat i j * x j)
      (by intro j hj; simp [hzero i j hj])
  have habs : (∑ t : Fin k, |a t * b t|) =
      ∑ j, |Ahat i j| * |x j| := by
    calc
      (∑ t : Fin k, |a t * b t|) = ∑ j, |Ahat i j * x j| := by
        exact p53_schedule_sum A schedule i (fun j => |Ahat i j * x j|)
          (by intro j hj; simp [hzero i j hj])
      _ = _ := by simp [abs_mul]
  have hpow := p53_cascade_dot_pow_bound fp k a b
  rw [hsum, habs] at hpow
  have hclog := Nat.clog_mono_right 2 (schedule.count_le i)
  have hbudget := p53_pow_error_le_gamma fp.u fp.u_nonneg
    (Nat.add_le_add_right hclog 1) hvalid
  have hH : 0 ≤ (∑ j, |Ahat i j| * |x j|) :=
    Finset.sum_nonneg (by intro j hj; exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right hbudget hH
  change |p53CascadeDot fp k a b - ∑ j, Ahat i j * x j| ≤
    p53Gamma fp.u (Nat.clog 2 l + 1) *
      (∑ j, |Ahat i j| * |x j|)
  exact hpow.trans hmul

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
  have hcap : Nat.clog 2 l + 1 ≤ l := p53_clog_add_one_le l (by omega)
  have hvalidC : P53GammaValid fp.u (Nat.clog 2 l + 1) := by
    have hle : ((Nat.clog 2 l + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast hcap
    unfold P53GammaValid at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) fp.u_nonneg]
  constructor
  · intro i
    apply p53_finish
    · exact p53_gamma_nonneg fp.u fp.u_nonneg l hvalid
    · exact p53_recursive_row_eval fp A Ahat x schedule i hvalid hzero
    · exact (p53_row_coeff_bounds fp A Ahat x η hpre hzero i).1
    · exact (p53_row_coeff_bounds fp A Ahat x η hpre hzero i).2
  · intro i
    apply p53_finish
    · exact p53_gamma_nonneg fp.u fp.u_nonneg (Nat.clog 2 l + 1) hvalidC
    · exact p53_cascade_row_eval fp A Ahat x schedule i hvalidC hzero
    · exact (p53_row_coeff_bounds fp A Ahat x η hpre hzero i).1
    · exact (p53_row_coeff_bounds fp A Ahat x η hpre hzero i).2

end VSCLReuse

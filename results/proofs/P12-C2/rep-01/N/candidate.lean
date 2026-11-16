import VSCLReuse.P12.Definitions
import Mathlib

namespace VSCLReuse

private lemma p12_q_nonneg (fp : P12FPModel) : 0 ≤ 1 + fp.u := by
  linarith [fp.u_nonneg]

private lemma p12_pow_linear_bound (u : ℝ) (hu : 0 ≤ u) (m : ℕ) :
    (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : 0 ≤ (1 + u) ^ m := pow_nonneg (by linarith) _
      have ht : 0 ≤ (1 + u) ^ m * ((m + 1 : ℝ) * u ^ 2) :=
        mul_nonneg hp (mul_nonneg (by positivity) (sq_nonneg u))
      calc
        (1 + u) ^ (m + 1) * (1 - ((m + 1 : ℕ) : ℝ) * u)
            = (1 + u) ^ m * (1 - (m : ℝ) * u) -
                (1 + u) ^ m * ((m + 1 : ℝ) * u ^ 2) := by
                  push_cast
                  ring
        _ ≤ (1 + u) ^ m * (1 - (m : ℝ) * u) := sub_le_self _ ht
        _ ≤ 1 := ih

private lemma p12_pow_le_gamma (u : ℝ) (hu : 0 ≤ u) (m : ℕ)
    (hvalid : P12GammaValid u m) :
    (1 + u) ^ m - 1 ≤ p12Gamma u m := by
  have hd : 0 < 1 - (m : ℝ) * u := by
    unfold P12GammaValid at hvalid
    linarith
  have hb := p12_pow_linear_bound u hu m
  unfold p12Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private lemma p12_mul_error (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨d, hd, he⟩ := fp.model_mul x y
  rw [he]
  have heq : (x * y) * (1 + d) - x * y = (x * y) * d := by ring
  rw [heq, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hd (abs_nonneg (x * y))]

private lemma p12_mul_abs (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_mul x y| ≤ (1 + fp.u) * |x * y| := by
  obtain ⟨d, hd, he⟩ := fp.model_mul x y
  rw [he, abs_mul]
  have h : |1 + d| ≤ 1 + fp.u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hd 1
  nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (x * y))]

private lemma p12_add_error (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨d, hd, he⟩ := fp.model_add x y
  rw [he]
  have heq : (x + y) * (1 + d) - (x + y) = (x + y) * d := by ring
  rw [heq, abs_mul]
  calc
    |x + y| * |d| ≤ (|x| + |y|) * |d| :=
      mul_le_mul_of_nonneg_right (abs_add_le x y) (abs_nonneg d)
    _ ≤ (|x| + |y|) * fp.u :=
      mul_le_mul_of_nonneg_left hd (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = fp.u * (|x| + |y|) := mul_comm _ _

private lemma p12_add_step (fp : P12FPModel) (m : ℕ) (hm : 1 ≤ m)
    (r s a b A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : |s| ≤ A) (hr : |r - s| ≤ ((1 + fp.u) ^ m - 1) * A)
    (ha : |a - b| ≤ fp.u * B) (hab : |a| ≤ (1 + fp.u) * B) :
    |fp.fl_add r a - (s + b)| ≤
      ((1 + fp.u) ^ (m + 1) - 1) * (A + B) := by
  let q : ℝ := 1 + fp.u
  have hq : 1 ≤ q := by dsimp [q]; linarith [fp.u_nonneg]
  have hq0 : 0 ≤ q := by linarith
  have hpow : q ^ 2 ≤ q ^ (m + 1) :=
    pow_le_pow_right₀ hq (by omega)
  have hpow0 : 0 ≤ q ^ m := pow_nonneg hq0 _
  have hrabs : |r| ≤ A + |r - s| := by
    calc
      |r| = |(r - s) + s| := by ring
      _ ≤ |r - s| + |s| := abs_add_le _ _
      _ ≤ A + |r - s| := by linarith
  have he := p12_add_error fp r a
  have htri : |fp.fl_add r a - (s + b)| ≤
      |fp.fl_add r a - (r + a)| + |r - s| + |a - b| := by
    calc
      |fp.fl_add r a - (s + b)| =
          |(fp.fl_add r a - (r + a)) + (r - s) + (a - b)| := by ring
      _ ≤ |(fp.fl_add r a - (r + a)) + (r - s)| + |a - b| := abs_add_le _ _
      _ ≤ (|fp.fl_add r a - (r + a)| + |r - s|) + |a - b| :=
        by gcongr; exact abs_add_le _ _
  have hbound : |fp.fl_add r a - (s + b)| ≤
      fp.u * (A + |r - s| + q * B) + |r - s| + fp.u * B := by
    calc
      _ ≤ |fp.fl_add r a - (r + a)| + |r - s| + |a - b| := htri
      _ ≤ fp.u * (|r| + |a|) + |r - s| + fp.u * B := by
        gcongr
      _ ≤ fp.u * (A + |r - s| + q * B) + |r - s| + fp.u * B := by
        gcongr
        exact fp.u_nonneg
  have hr' : |r - s| ≤ (q ^ m - 1) * A := hr
  have hstep : |fp.fl_add r a - (s + b)| ≤
      (q ^ (m + 1) - 1) * A + (q ^ 2 - 1) * B := by
    calc
      _ ≤ fp.u * (A + |r - s| + q * B) + |r - s| + fp.u * B := hbound
      _ ≤ fp.u * (A + (q ^ m - 1) * A + q * B) +
          (q ^ m - 1) * A + fp.u * B := by
        gcongr
        exact fp.u_nonneg
      _ = (q ^ (m + 1) - 1) * A + (q ^ 2 - 1) * B := by
        dsimp [q]
        rw [pow_succ]
        ring
  calc
    _ ≤ (q ^ (m + 1) - 1) * A + (q ^ 2 - 1) * B := hstep
    _ ≤ (q ^ (m + 1) - 1) * A + (q ^ (m + 1) - 1) * B := by
      gcongr
    _ = _ := by dsimp [q]; ring

private lemma p12_pairs_fold_bound (fp : P12FPModel)
    (l : List (ℝ × ℝ)) (m : ℕ) (hm : 1 ≤ m)
    (r s A : ℝ) (hA : 0 ≤ A) (hs : |s| ≤ A)
    (hr : |r - s| ≤ ((1 + fp.u) ^ m - 1) * A) :
    |l.foldl (fun r z => fp.fl_add r (fp.fl_mul z.1 z.2)) r -
      l.foldl (fun s z => s + z.1 * z.2) s| ≤
      ((1 + fp.u) ^ (m + l.length) - 1) *
        l.foldl (fun A z => A + |z.1 * z.2|) A := by
  induction l generalizing m r s A with
  | nil => simpa using hr
  | cons z l ih =>
      let b := z.1 * z.2
      let B := |b|
      let a := fp.fl_mul z.1 z.2
      let r' := fp.fl_add r a
      let s' := s + b
      let A' := A + B
      have hB : 0 ≤ B := abs_nonneg _
      have hA' : 0 ≤ A' := add_nonneg hA hB
      have hs' : |s'| ≤ A' := by
        calc
          |s'| ≤ |s| + |b| := abs_add_le _ _
          _ ≤ A' := by dsimp [A', B]; linarith
      have hr' : |r' - s'| ≤ ((1 + fp.u) ^ (m + 1) - 1) * A' := by
        apply p12_add_step fp m hm r s a b A B hA hB hs hr
        · exact p12_mul_error fp z.1 z.2
        · exact p12_mul_abs fp z.1 z.2
      have hi := ih (m + 1) (by omega) r' s' A' hA' hs' hr'
      simpa [r', s', A', B, b, a, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hi

private lemma p12_fold_pair_sum (l : List (ℝ × ℝ)) (s : ℝ) :
    l.foldl (fun s z => s + z.1 * z.2) s =
      s + (l.map (fun z => z.1 * z.2)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons z l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

private lemma p12_fold_pair_abs_sum (l : List (ℝ × ℝ)) (s : ℝ) :
    l.foldl (fun s z => s + |z.1 * z.2|) s =
      s + (l.map (fun z => |z.1 * z.2|)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons z l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; ring

private lemma p12_rounded_dot_bound (fp : P12FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    |p12RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      ((1 + fp.u) ^ n - 1) * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero => simp [p12RoundedDotProduct]
  | succ m =>
      let l : List (ℝ × ℝ) :=
        (List.finRange m).map (fun i => (x i.succ, y i.succ))
      have hi : |l.foldl (fun r z => fp.fl_add r (fp.fl_mul z.1 z.2))
          (fp.fl_mul (x 0) (y 0)) -
          l.foldl (fun s z => s + z.1 * z.2) (x 0 * y 0)| ≤
          ((1 + fp.u) ^ (1 + l.length) - 1) *
          l.foldl (fun A z => A + |z.1 * z.2|) |x 0 * y 0| := by
        apply p12_pairs_fold_bound fp l 1 (by omega)
        · exact abs_nonneg _
        · exact le_refl _
        · simpa using p12_mul_error fp (x 0) (y 0)
      have hround : p12RoundedDotProduct fp (m + 1) x y =
          l.foldl (fun r z => fp.fl_add r (fp.fl_mul z.1 z.2))
            (fp.fl_mul (x 0) (y 0)) := by
        simp [p12RoundedDotProduct, Fin.foldl_eq_finRange_foldl, l, List.foldl_map]
      have hexact : l.foldl (fun s z => s + z.1 * z.2) (x 0 * y 0) =
          ∑ i : Fin (m + 1), x i * y i := by
        rw [p12_fold_pair_sum, Fin.sum_univ_succ, Fin.sum_univ_def]
        simp [l, List.map_map, Function.comp_def]
      have habs : l.foldl (fun A z => A + |z.1 * z.2|) |x 0 * y 0| =
          ∑ i : Fin (m + 1), |x i * y i| := by
        rw [p12_fold_pair_abs_sum, Fin.sum_univ_succ, Fin.sum_univ_def]
        simp [l, List.map_map, Function.comp_def]
      rw [hround, ← hexact, ← habs]
      convert hi using 1 <;> simp [l, Nat.add_comm]

private lemma p12_matmul_nonneg {n : ℕ} (A B : P12Matrix n)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i j : Fin n) :
    0 ≤ p12MatMul A B i j := by
  unfold p12MatMul
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

private lemma p12_matmul_mono_left {n : ℕ} (A B C : P12Matrix n)
    (h : ∀ i j, A i j ≤ B i j) (hC : ∀ i j, 0 ≤ C i j) (i j : Fin n) :
    p12MatMul A C i j ≤ p12MatMul B C i j := by
  unfold p12MatMul
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h i k) (hC k j)

private lemma p12_matmul_bounded_left {n : ℕ} (A B C : P12Matrix n)
    (c : ℝ) (h : ∀ i j, A i j ≤ c * B i j)
    (hC : ∀ i j, 0 ≤ C i j) (i j : Fin n) :
    p12MatMul A C i j ≤ c * p12MatMul B C i j := by
  unfold p12MatMul
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  calc
    A i k * C k j ≤ (c * B i k) * C k j :=
      mul_le_mul_of_nonneg_right (h i k) (hC k j)
    _ = c * (B i k * C k j) := by ring

private lemma p12_matmul_abs {n : ℕ} (A B : P12Matrix n) (i j : Fin n) :
    |p12MatMul A B i j| ≤
      p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  unfold p12MatMul p12AbsMatrix
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (fun k : Fin n => A i k * B k j) Finset.univ)

private lemma p12_matmul_sub_abs {n : ℕ} (A B C : P12Matrix n) (i j : Fin n) :
    |p12MatMul A C i j - p12MatMul B C i j| ≤
      p12MatMul (fun i j => |A i j - B i j|) (p12AbsMatrix C) i j := by
  have heq : p12MatMul A C i j - p12MatMul B C i j =
      ∑ k : Fin n, (A i k - B i k) * C k j := by
    simp only [p12MatMul, ← Finset.sum_sub_distrib]
    congr 1
    funext k
    ring
  rw [heq]
  unfold p12MatMul p12AbsMatrix
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (fun k : Fin n => (A i k - B i k) * C k j) Finset.univ)

private lemma p12_rounded_matmul_error {n : ℕ} (fp : P12FPModel)
    (A B C : P12Matrix n) (i j : Fin n) :
    |p12RoundedMatMul fp A C i j - p12MatMul B C i j| ≤
      ((1 + fp.u) ^ n - 1) *
          p12MatMul (p12AbsMatrix A) (p12AbsMatrix C) i j +
        p12MatMul (fun i j => |A i j - B i j|) (p12AbsMatrix C) i j := by
  have hdot := p12_rounded_dot_bound fp n (A i) (fun k => C k j)
  have hsub := p12_matmul_sub_abs A B C i j
  have htri := abs_sub_le (p12RoundedMatMul fp A C i j)
    (p12MatMul A C i j) (p12MatMul B C i j)
  have hdot' : |p12RoundedMatMul fp A C i j - p12MatMul A C i j| ≤
      ((1 + fp.u) ^ n - 1) *
        p12MatMul (p12AbsMatrix A) (p12AbsMatrix C) i j := by
    simpa only [p12RoundedMatMul, p12MatMul, p12AbsMatrix, abs_mul] using hdot
  exact htri.trans (add_le_add hdot' hsub)

private lemma p12_power_nonneg {n : ℕ} (X : P12Matrix n) (k : ℕ) :
    ∀ i j, 0 ≤ p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      simp [p12PowerSteps, p12AbsMatrix]
  | succ k ih =>
      intro i j
      change 0 ≤ p12MatMul (p12PowerSteps (p12AbsMatrix X) k) (p12AbsMatrix X) i j
      exact p12_matmul_nonneg _ _ ih (fun i j => abs_nonneg _) i j

private lemma p12_power_abs {n : ℕ} (X : P12Matrix n) (k : ℕ) :
    ∀ i j, |p12PowerSteps X k i j| ≤
      p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      simp [p12PowerSteps, p12AbsMatrix]
  | succ k ih =>
      intro i j
      have h1 := p12_matmul_abs (p12PowerSteps X k) X i j
      have h2 := p12_matmul_mono_left
        (p12AbsMatrix (p12PowerSteps X k))
        (p12PowerSteps (p12AbsMatrix X) k)
        (p12AbsMatrix X)
        (by simpa [p12AbsMatrix] using ih)
        (fun i j => abs_nonneg _) i j
      change |p12MatMul (p12PowerSteps X k) X i j| ≤
        p12MatMul (p12PowerSteps (p12AbsMatrix X) k) (p12AbsMatrix X) i j
      exact h1.trans h2

private lemma p12_rounded_power_pow_bound (fp : P12FPModel) (n k : ℕ)
    (X : P12Matrix n) :
    ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        ((1 + fp.u) ^ (k * n) - 1) *
          p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      simp [p12RoundedPowerSteps, p12PowerSteps]
  | succ k ih =>
      let q : ℝ := 1 + fp.u
      let c : ℝ := q ^ (k * n)
      let d : ℝ := q ^ n
      let R := p12RoundedPowerSteps fp X k
      let E := p12PowerSteps X k
      let P := p12PowerSteps (p12AbsMatrix X) k
      have hq : 1 ≤ q := by dsimp [q]; linarith [fp.u_nonneg]
      have hd : 0 ≤ d - 1 := sub_nonneg.mpr (one_le_pow₀ hq)
      have hX : ∀ i j, 0 ≤ p12AbsMatrix X i j :=
        fun i j => abs_nonneg _
      have hP : ∀ i j, 0 ≤ P i j := p12_power_nonneg X k
      have hEabs : ∀ i j, |E i j| ≤ P i j := p12_power_abs X k
      have hErr : ∀ i j, |R i j - E i j| ≤ (c - 1) * P i j := ih
      have hRabs : ∀ i j, |R i j| ≤ c * P i j := by
        intro i j
        calc
          |R i j| = |(R i j - E i j) + E i j| := by ring
          _ ≤ |R i j - E i j| + |E i j| := abs_add_le _ _
          _ ≤ (c - 1) * P i j + P i j := add_le_add (hErr i j) (hEabs i j)
          _ = c * P i j := by ring
      have hRmat (i j : Fin n) :
          p12MatMul (p12AbsMatrix R) (p12AbsMatrix X) i j ≤
            c * p12MatMul P (p12AbsMatrix X) i j :=
        p12_matmul_bounded_left _ _ _ c
          (by simpa [p12AbsMatrix] using hRabs) hX i j
      have hEmat (i j : Fin n) :
          p12MatMul (fun i j => |R i j - E i j|) (p12AbsMatrix X) i j ≤
            (c - 1) * p12MatMul P (p12AbsMatrix X) i j :=
        p12_matmul_bounded_left _ _ _ (c - 1) hErr hX i j
      intro i j
      have hround := p12_rounded_matmul_error fp R E X i j
      change |p12RoundedMatMul fp R X i j - p12MatMul E X i j| ≤
        (q ^ ((k + 1) * n) - 1) * p12MatMul P (p12AbsMatrix X) i j
      calc
        _ ≤ (d - 1) * p12MatMul (p12AbsMatrix R) (p12AbsMatrix X) i j +
            p12MatMul (fun i j => |R i j - E i j|) (p12AbsMatrix X) i j := hround
        _ ≤ (d - 1) * (c * p12MatMul P (p12AbsMatrix X) i j) +
            (c - 1) * p12MatMul P (p12AbsMatrix X) i j :=
          add_le_add (mul_le_mul_of_nonneg_left (hRmat i j) hd) (hEmat i j)
        _ = (q ^ ((k + 1) * n) - 1) * p12MatMul P (p12AbsMatrix X) i j := by
          have hp : q ^ ((k + 1) * n) = d * c := by
            dsimp [d, c]
            calc
              q ^ ((k + 1) * n) = q ^ (k * n + n) := by
                congr 1
                simp [Nat.add_mul]
              _ = q ^ (k * n) * q ^ n := pow_add _ _ _
              _ = q ^ n * q ^ (k * n) := mul_comm _ _
          rw [hp]
          ring

/-- P12-C2: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p12_c2_lemma_2_2
    (fp : P12FPModel) (n k : ℕ) (X : P12Matrix n)
    (hvalid : P12GammaValid fp.u (k * n)) :
    ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        p12Gamma fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  -- PROOF_START P12-C2-H001
  intro i j
  have hpow := p12_rounded_power_pow_bound fp n k X i j
  have hgamma := p12_pow_le_gamma fp.u fp.u_nonneg (k * n) hvalid
  have hnonneg := p12_power_nonneg X k i j
  exact hpow.trans (mul_le_mul_of_nonneg_right hgamma hnonneg)

end VSCLReuse

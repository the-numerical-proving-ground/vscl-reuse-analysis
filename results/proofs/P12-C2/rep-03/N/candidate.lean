import VSCLReuse.P12.Definitions
import Mathlib

namespace VSCLReuse

private noncomputable def p12Beta (u : ℝ) (m : ℕ) : ℝ := (1 + u) ^ m - 1

private lemma p12Beta_nonneg {u : ℝ} (hu : 0 ≤ u) (m : ℕ) :
    0 ≤ p12Beta u m := by
  unfold p12Beta
  have h : (1 : ℝ) ≤ (1 + u) ^ m := by
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + u)
  linarith

private lemma p12Beta_mono {u : ℝ} (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) : p12Beta u a ≤ p12Beta u b := by
  unfold p12Beta
  exact sub_le_sub_right (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + u) hab) _

private lemma p12Beta_add (u : ℝ) (a b : ℕ) :
    p12Beta u (a + b) = p12Beta u a + p12Beta u b +
      p12Beta u a * p12Beta u b := by
  unfold p12Beta
  rw [pow_add]
  ring

private lemma p12Fl_mul_error (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul x y
  rw [hfl]
  have heq : (x * y) * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x * y| * |δ| = |δ| * |x * y| := by ring
    _ ≤ fp.u * |x * y| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

private lemma p12Fl_add_error (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * (|x| + |y|) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
  rw [hfl]
  have heq : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [heq, abs_mul]
  calc
    |x + y| * |δ| ≤ (|x| + |y|) * fp.u := by
      exact mul_le_mul (abs_add_le x y) hδ (abs_nonneg _) (by positivity)
    _ = fp.u * (|x| + |y|) := by ring

private lemma p12Fl_add_step (fp : P12FPModel) (a s b t : ℝ)
    (hb : |b - t| ≤ fp.u * |t|) :
    |fp.fl_add a b - (s + t)| ≤
      (1 + fp.u) * |a - s| + fp.u * |s| +
        (2 * fp.u + fp.u ^ 2) * |t| := by
  have hfl := p12Fl_add_error fp a b
  have ha : |a| ≤ |s| + |a - s| := by
    calc
      |a| = |s + (a - s)| := by congr 1; ring
      _ ≤ |s| + |a - s| := abs_add_le _ _
  have hbb : |b| ≤ |t| + |b - t| := by
    calc
      |b| = |t + (b - t)| := by congr 1; ring
      _ ≤ |t| + |b - t| := abs_add_le _ _
  have htri : |fp.fl_add a b - (s + t)| ≤
      |fp.fl_add a b - (a + b)| + |a - s| + |b - t| := by
    calc
      |fp.fl_add a b - (s + t)| =
          |(fp.fl_add a b - (a + b)) + ((a - s) + (b - t))| := by
            congr 1; ring
      _ ≤ |fp.fl_add a b - (a + b)| + |(a - s) + (b - t)| := abs_add_le _ _
      _ ≤ |fp.fl_add a b - (a + b)| + |a - s| + |b - t| := by
        linarith [abs_add_le (a - s) (b - t)]
  have hsum : fp.u * (|a| + |b|) ≤
      fp.u * (|s| + |a - s| + |t| + |b - t|) := by
    exact mul_le_mul_of_nonneg_left (by linarith) fp.u_nonneg
  have hmul := mul_le_mul_of_nonneg_left hb (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
  nlinarith

private noncomputable def p12RoundedSum (fp : P12FPModel) (m : ℕ)
    (g : Fin (m + 1) → ℝ) : ℝ :=
  Fin.foldl m (fun acc i => fp.fl_add acc (g i.succ)) (g 0)

private lemma p12RoundedSum_succ (fp : P12FPModel) (m : ℕ)
    (g : Fin (m + 2) → ℝ) :
    p12RoundedSum fp (m + 1) g =
      fp.fl_add (p12RoundedSum fp m (fun i => g i.castSucc))
        (g (Fin.last (m + 1))) := by
  unfold p12RoundedSum
  rw [Fin.foldl_succ_last]
  congr 1

private lemma p12RoundedSum_error (fp : P12FPModel) :
    ∀ (m : ℕ) (t g : Fin (m + 1) → ℝ),
      (∀ i, |g i - t i| ≤ fp.u * |t i|) →
      |p12RoundedSum fp m g - ∑ i, t i| ≤
        p12Beta fp.u (m + 1) * ∑ i, |t i| := by
  intro m
  induction m with
  | zero =>
      intro t g hg
      simpa [p12RoundedSum, p12Beta] using hg 0
  | succ m ih =>
      intro t g hg
      let t' : Fin (m + 1) → ℝ := fun i => t i.castSucc
      let g' : Fin (m + 1) → ℝ := fun i => g i.castSucc
      let s : ℝ := ∑ i, t' i
      let S : ℝ := ∑ i, |t' i|
      let a : ℝ := p12RoundedSum fp m g'
      let j : Fin (m + 2) := Fin.last (m + 1)
      have hprev : |a - s| ≤ p12Beta fp.u (m + 1) * S := by
        exact ih t' g' (fun i => hg i.castSucc)
      have hs : |s| ≤ S := by
        exact Finset.abs_sum_le_sum_abs _ _
      have hb : |g j - t j| ≤ fp.u * |t j| := hg j
      have hstep := p12Fl_add_step fp a s (g j) (t j) hb
      have hcoef : p12Beta fp.u (m + 2) =
          (1 + fp.u) * p12Beta fp.u (m + 1) + fp.u := by
        unfold p12Beta
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
        ring
      have hterm : 2 * fp.u + fp.u ^ 2 ≤ p12Beta fp.u (m + 2) := by
        have hm := p12Beta_mono fp.u_nonneg (show 2 ≤ m + 2 by omega)
        have htwo : p12Beta fp.u 2 = 2 * fp.u + fp.u ^ 2 := by
          unfold p12Beta
          ring
        exact htwo ▸ hm
      have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have h1 := mul_le_mul_of_nonneg_left hprev (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
      have h2 := mul_le_mul_of_nonneg_left hs fp.u_nonneg
      have h3 := mul_le_mul_of_nonneg_right hterm (abs_nonneg (t j))
      rw [p12RoundedSum_succ, Fin.sum_univ_castSucc]
      conv_rhs => rw [Fin.sum_univ_castSucc]
      simpa only [t', g', s, S, a, j, Nat.succ_eq_add_one, Nat.add_assoc] using
        (show |fp.fl_add a (g j) - (s + t j)| ≤
            p12Beta fp.u (m + 2) * (S + |t j|) by
          calc
            _ ≤ (1 + fp.u) * |a - s| + fp.u * |s| +
                (2 * fp.u + fp.u ^ 2) * |t j| := hstep
            _ ≤ p12Beta fp.u (m + 2) * S +
                (2 * fp.u + fp.u ^ 2) * |t j| := by
                  rw [hcoef]
                  nlinarith
            _ ≤ p12Beta fp.u (m + 2) * (S + |t j|) := by
                  nlinarith)

private lemma p12RoundedDotProduct_error (fp : P12FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    |p12RoundedDotProduct fp n x y - ∑ i, x i * y i| ≤
      p12Beta fp.u n * ∑ i, |x i * y i| := by
  cases n with
  | zero => simp [p12RoundedDotProduct, p12Beta]
  | succ m =>
      change |p12RoundedSum fp m (fun i => fp.fl_mul (x i) (y i)) -
          ∑ i, x i * y i| ≤
        p12Beta fp.u (m + 1) * ∑ i, |x i * y i|
      exact p12RoundedSum_error fp m (fun i => x i * y i)
        (fun i => fp.fl_mul (x i) (y i))
        (fun i => p12Fl_mul_error fp (x i) (y i))

private lemma p12RoundedMatMul_error (fp : P12FPModel) (n : ℕ)
    (A B : P12Matrix n) (i j : Fin n) :
    |p12RoundedMatMul fp A B i j - p12MatMul A B i j| ≤
      p12Beta fp.u n * p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  have h := p12RoundedDotProduct_error fp n (A i) (fun l => B l j)
  simp only [p12RoundedMatMul, p12MatMul, p12AbsMatrix] at *
  simpa only [abs_mul] using h

private lemma p12MatMul_abs_le (n : ℕ) (A B : P12Matrix n) (i j : Fin n) :
    |p12MatMul A B i j| ≤
      p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  unfold p12MatMul p12AbsMatrix
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun l : Fin n => A i l * B l j))

private lemma p12MatMul_nonneg (n : ℕ) (A B : P12Matrix n)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i j : Fin n) : 0 ≤ p12MatMul A B i j := by
  unfold p12MatMul
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (hA i l) (hB l j))

private lemma p12Power_abs_nonneg (n k : ℕ) (X : P12Matrix n) :
    ∀ i j, 0 ≤ p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero => exact fun i j => abs_nonneg _
  | succ k ih =>
      exact fun i j => p12MatMul_nonneg n _ _ ih
        (fun a b => abs_nonneg _) i j

private lemma p12Power_abs_le (n k : ℕ) (X : P12Matrix n) :
    ∀ i j, |p12PowerSteps X k i j| ≤
      p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero => exact fun i j => le_refl _
  | succ k ih =>
      intro i j
      have h := p12MatMul_abs_le n (p12PowerSteps X k) X i j
      calc
        |p12PowerSteps X (k + 1) i j| ≤
            p12MatMul (p12AbsMatrix (p12PowerSteps X k))
              (p12AbsMatrix X) i j := h
        _ ≤ p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by
          change (∑ l : Fin n, |p12PowerSteps X k i l| * |X l j|) ≤
            ∑ l : Fin n, p12PowerSteps (p12AbsMatrix X) k i l * |X l j|
          exact Finset.sum_le_sum (fun l _ =>
            mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg _))

private lemma p12MatMul_diff_le (n : ℕ) (A B X : P12Matrix n)
    (i j : Fin n) :
    |p12MatMul A X i j - p12MatMul B X i j| ≤
      ∑ l : Fin n, |A i l - B i l| * |X l j| := by
  have heq : p12MatMul A X i j - p12MatMul B X i j =
      ∑ l : Fin n, (A i l - B i l) * X l j := by
    simp only [p12MatMul, ← Finset.sum_sub_distrib]
    congr 1
    ext l
    ring
  rw [heq]
  calc
    |∑ l : Fin n, (A i l - B i l) * X l j| ≤
        ∑ l : Fin n, |(A i l - B i l) * X l j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l : Fin n, |A i l - B i l| * |X l j| := by
      simp_rw [abs_mul]

private lemma p12Power_beta (fp : P12FPModel) (n k : ℕ) (X : P12Matrix n) :
    ∀ i j, |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
      p12Beta fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  induction k with
  | zero =>
      intro i j
      simp [p12Beta, p12RoundedPowerSteps, p12PowerSteps]
  | succ k ih =>
      intro i j
      let R := p12RoundedPowerSteps fp X k
      let P := p12PowerSteps X k
      let Q := p12PowerSteps (p12AbsMatrix X) k
      let e := p12Beta fp.u (k * n)
      let d := p12Beta fp.u n
      let M := p12MatMul Q (p12AbsMatrix X) i j
      have hQ : ∀ l, 0 ≤ Q i l := fun l => p12Power_abs_nonneg n k X i l
      have hP : ∀ l, |P i l| ≤ Q i l := fun l => p12Power_abs_le n k X i l
      have hR : ∀ l, |R i l| ≤ (1 + e) * Q i l := by
        intro l
        have hraw : |R i l| ≤ |R i l - P i l| + |P i l| := by
          calc
            |R i l| = |(R i l - P i l) + P i l| := by congr 1; ring
            _ ≤ |R i l - P i l| + |P i l| := abs_add_le _ _
        have hprev := ih i l
        have hp := hP l
        dsimp [R, P, Q, e] at *
        nlinarith
      have hround := p12RoundedMatMul_error fp n R X i j
      have hdiff := p12MatMul_diff_le n R P X i j
      have hsumR : p12MatMul (p12AbsMatrix R) (p12AbsMatrix X) i j ≤
          (1 + e) * M := by
        change (∑ l : Fin n, |R i l| * |X l j|) ≤
          (1 + e) * ∑ l : Fin n, Q i l * |X l j|
        calc
          (∑ l : Fin n, |R i l| * |X l j|) ≤
              ∑ l : Fin n, (1 + e) * (Q i l * |X l j|) := by
                exact Finset.sum_le_sum (fun l _ => by
                  have h := mul_le_mul_of_nonneg_right (hR l) (abs_nonneg (X l j))
                  nlinarith)
          _ = (1 + e) * ∑ l : Fin n, Q i l * |X l j| := by
            rw [Finset.mul_sum]
      have hsumD : (∑ l : Fin n, |R i l - P i l| * |X l j|) ≤
          e * M := by
        change (∑ l : Fin n, |R i l - P i l| * |X l j|) ≤
          e * ∑ l : Fin n, Q i l * |X l j|
        calc
          (∑ l : Fin n, |R i l - P i l| * |X l j|) ≤
              ∑ l : Fin n, e * (Q i l * |X l j|) := by
                exact Finset.sum_le_sum (fun l _ => by
                  have h := mul_le_mul_of_nonneg_right (ih i l) (abs_nonneg (X l j))
                  dsimp [e, Q, R, P] at *
                  nlinarith)
          _ = e * ∑ l : Fin n, Q i l * |X l j| := by
            rw [Finset.mul_sum]
      have hM : 0 ≤ M := p12MatMul_nonneg n Q (p12AbsMatrix X)
        (fun a b => p12Power_abs_nonneg n k X a b)
        (fun a b => abs_nonneg _) i j
      have hd : 0 ≤ d := p12Beta_nonneg fp.u_nonneg n
      have htri : |p12RoundedMatMul fp R X i j - p12MatMul P X i j| ≤
          |p12RoundedMatMul fp R X i j - p12MatMul R X i j| +
            |p12MatMul R X i j - p12MatMul P X i j| := by
        calc
          _ = |(p12RoundedMatMul fp R X i j - p12MatMul R X i j) +
                (p12MatMul R X i j - p12MatMul P X i j)| := by
                  congr 1
                  ring
          _ ≤ _ := abs_add_le _ _
      have hbeta : p12Beta fp.u ((k + 1) * n) = d * (1 + e) + e := by
        have hn : (k + 1) * n = n + k * n := by
          simp [Nat.add_mul, Nat.add_comm]
        rw [hn, p12Beta_add]
        dsimp [d, e]
        ring
      change |p12RoundedMatMul fp R X i j - p12MatMul P X i j| ≤
        p12Beta fp.u ((k + 1) * n) * M
      rw [hbeta]
      have hm := mul_le_mul_of_nonneg_left hsumR hd
      nlinarith

private lemma p12Pow_guard_le_one {u : ℝ} (hu : 0 ≤ u) (m : ℕ) :
    (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hcoef : (1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u) ≤
          1 - (m : ℝ) * u := by
        have hnonneg : 0 ≤ ((m + 1 : ℕ) : ℝ) * u ^ 2 :=
          mul_nonneg (by positivity) (sq_nonneg u)
        push_cast
        nlinarith
      have hpow : 0 ≤ (1 + u) ^ m := pow_nonneg (by linarith) _
      calc
        (1 + u) ^ (m + 1) * (1 - ((m + 1 : ℕ) : ℝ) * u) =
            (1 + u) ^ m * ((1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u)) := by
              rw [pow_succ]
              ring
        _ ≤ (1 + u) ^ m * (1 - (m : ℝ) * u) :=
          mul_le_mul_of_nonneg_left hcoef hpow
        _ ≤ 1 := ih

private lemma p12Beta_le_gamma {u : ℝ} (hu : 0 ≤ u) (m : ℕ)
    (hvalid : P12GammaValid u m) : p12Beta u m ≤ p12Gamma u m := by
  have hd : 0 < 1 - (m : ℝ) * u := by
    dsimp [P12GammaValid] at hvalid
    linarith
  have hp := p12Pow_guard_le_one hu m
  unfold p12Beta p12Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

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
  have hb := p12Power_beta fp n k X i j
  have hg := p12Beta_le_gamma fp.u_nonneg (k * n) hvalid
  have hnonneg := p12Power_abs_nonneg n k X i j
  exact hb.trans (mul_le_mul_of_nonneg_right hg hnonneg)

end VSCLReuse

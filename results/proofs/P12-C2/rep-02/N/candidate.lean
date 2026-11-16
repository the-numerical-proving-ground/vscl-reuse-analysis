import VSCLReuse.P12.Definitions
import Mathlib.Tactic

namespace VSCLReuse

private lemma gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P12GammaValid u m) : 0 ≤ p12Gamma u m := by
  unfold p12Gamma P12GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr hm.le)

private lemma gamma_ge_u (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P12GammaValid u m) (hpos : 1 ≤ m) : u ≤ p12Gamma u m := by
  unfold p12Gamma P12GammaValid at *
  have hr : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
  apply (le_div_iff₀ (sub_pos.mpr hm)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hm.le) hu]

private lemma gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P12GammaValid u (m + 1)) :
    (1 + u) * p12Gamma u m + u ≤ p12Gamma u (m + 1) := by
  unfold p12Gamma P12GammaValid at *
  push_cast at hm ⊢
  have hr : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd : 0 < 1 - (m : ℝ) * u := by nlinarith
  have he : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  apply (le_div_iff₀ he).2
  have hne : 1 - (m : ℝ) * u ≠ 0 := ne_of_gt hd
  rw [show (1 + u) * ((m : ℝ) * u / (1 - (m : ℝ) * u)) + u =
      ((m : ℝ) * u + u) / (1 - (m : ℝ) * u) by
    field_simp [hne, mul_comm u (m : ℝ)]
    ring]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (add_nonneg hr hu) hu]

private lemma round_mul_bound (fp : P12FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul x y
  rw [hmul]
  have heq : (x * y) * (1 + δ) - x * y = δ * (x * y) := by ring
  rw [heq, abs_mul]
  exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)

private lemma round_step_bound (fp : P12FPModel)
    (g S T a t b : ℝ) (huge : fp.u ≤ g) (hT : 0 ≤ T)
    (hS : |S| ≤ T) (ha : |a - S| ≤ g * T)
    (hb : |b - t| ≤ fp.u * |t|) :
    |fp.fl_add a b - (S + t)| ≤
      ((1 + fp.u) * g + fp.u) * (T + |t|) := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  have hbasic : |fp.fl_add a b - (S + t)| ≤
      |a - S| + |b - t| + fp.u * (|a| + |b|) := by
    rw [hadd]
    have heq : (a + b) * (1 + δ) - (S + t) =
        (a - S) + (b - t) + δ * (a + b) := by ring
    rw [heq]
    calc
      _ ≤ |(a - S) + (b - t)| + |δ * (a + b)| := abs_add_le _ _
      _ ≤ (|a - S| + |b - t|) + |δ * (a + b)| := by
        exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ |a - S| + |b - t| + fp.u * (|a| + |b|) := by
        rw [abs_mul]
        have hsum := abs_add_le a b
        have hprod := mul_le_mul hδ hsum (abs_nonneg _) fp.u_nonneg
        linarith
  have habsa : |a| ≤ g * T + T := by
    calc
      |a| = |(a - S) + S| := by ring
      _ ≤ |a - S| + |S| := abs_add_le _ _
      _ ≤ g * T + T := add_le_add ha hS
  have habsb : |b| ≤ fp.u * |t| + |t| := by
    calc
      |b| = |(b - t) + t| := by ring
      _ ≤ |b - t| + |t| := abs_add_le _ _
      _ ≤ fp.u * |t| + |t| := add_le_add hb le_rfl
  have hcoeff : fp.u + fp.u * (1 + fp.u) ≤ (1 + fp.u) * g + fp.u := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + fp.u by linarith [fp.u_nonneg])
      (show 0 ≤ g - fp.u by linarith)]
  have hcoeff_t := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg t)
  have hscale := mul_le_mul_of_nonneg_left (add_le_add habsa habsb) fp.u_nonneg
  nlinarith

private lemma rounded_dot_succ_last (fp : P12FPModel) (m : ℕ)
    (x y : Fin (m + 2) → ℝ) :
    p12RoundedDotProduct fp (m + 2) x y =
      fp.fl_add
        (p12RoundedDotProduct fp (m + 1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) := by
  simp only [p12RoundedDotProduct, Fin.foldl_succ_last]
  rfl

private lemma rounded_dot_bound (fp : P12FPModel) :
    ∀ m : ℕ, ∀ x y : Fin (m + 1) → ℝ,
      P12GammaValid fp.u (m + 1) →
      |p12RoundedDotProduct fp (m + 1) x y - ∑ i, x i * y i| ≤
        p12Gamma fp.u (m + 1) * ∑ i, |x i * y i| := by
  intro m
  induction m with
  | zero =>
      intro x y hvalid
      have hγ : fp.u ≤ p12Gamma fp.u 1 :=
        gamma_ge_u fp.u 1 fp.u_nonneg hvalid (by omega)
      have hprod := round_mul_bound fp (x 0) (y 0)
      have hscale := mul_le_mul_of_nonneg_right hγ (abs_nonneg (x 0 * y 0))
      simpa [p12RoundedDotProduct] using le_trans hprod hscale
  | succ m ih =>
      intro x y hvalid
      let x' : Fin (m + 1) → ℝ := fun i => x i.castSucc
      let y' : Fin (m + 1) → ℝ := fun i => y i.castSucc
      let S : ℝ := ∑ i : Fin (m + 1), x' i * y' i
      let T : ℝ := ∑ i : Fin (m + 1), |x' i * y' i|
      let t : ℝ := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
      let a : ℝ := p12RoundedDotProduct fp (m + 1) x' y'
      let b : ℝ := fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
      have hprevvalid : P12GammaValid fp.u (m + 1) := by
        unfold P12GammaValid at *
        push_cast at hvalid ⊢
        have hu := fp.u_nonneg
        nlinarith
      have ha : |a - S| ≤ p12Gamma fp.u (m + 1) * T :=
        ih x' y' hprevvalid
      have hS : |S| ≤ T := by
        simpa [S, T, x', y'] using
          (Finset.abs_sum_le_sum_abs
            (fun i : Fin (m + 1) => x' i * y' i) Finset.univ)
      have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hb : |b - t| ≤ fp.u * |t| :=
        round_mul_bound fp _ _
      have hγu : fp.u ≤ p12Gamma fp.u (m + 1) :=
        gamma_ge_u fp.u (m + 1) fp.u_nonneg hprevvalid (by omega)
      have hstep := round_step_bound fp (p12Gamma fp.u (m + 1))
        S T a t b hγu hT hS ha hb
      have hγstep :
          (1 + fp.u) * p12Gamma fp.u (m + 1) + fp.u ≤
            p12Gamma fp.u (m + 2) := by
        convert gamma_step fp.u (m + 1) fp.u_nonneg hvalid using 1 <;> omega
      have hscale := mul_le_mul_of_nonneg_right hγstep
        (add_nonneg hT (abs_nonneg t))
      calc
        |p12RoundedDotProduct fp (m + 2) x y - ∑ i, x i * y i| =
            |fp.fl_add a b - (S + t)| := by
              rw [rounded_dot_succ_last, Fin.sum_univ_castSucc]
        _ ≤ ((1 + fp.u) * p12Gamma fp.u (m + 1) + fp.u) *
              (T + |t|) := hstep
        _ ≤ p12Gamma fp.u (m + 2) * (T + |t|) := hscale
        _ = p12Gamma fp.u (m + 2) * ∑ i, |x i * y i| := by
              rw [Fin.sum_univ_castSucc]

private lemma valid_of_le (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hb : P12GammaValid u b) : P12GammaValid u a := by
  unfold P12GammaValid at *
  have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hb

private lemma gamma_one_add (u : ℝ) (m : ℕ) (hm : P12GammaValid u m) :
    1 + p12Gamma u m = 1 / (1 - (m : ℝ) * u) := by
  unfold p12Gamma P12GammaValid at *
  have hne : 1 - (m : ℝ) * u ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  field_simp [hne]
  ring

private lemma gamma_combine (u : ℝ) (a b : ℕ) (hu : 0 ≤ u)
    (hvalid : P12GammaValid u (a + b)) :
    p12Gamma u b * (1 + p12Gamma u a) + p12Gamma u a ≤
      p12Gamma u (a + b) := by
  have ha : P12GammaValid u a :=
    valid_of_le u hu (Nat.le_add_right a b) hvalid
  have hb : P12GammaValid u b :=
    valid_of_le u hu (Nat.le_add_left b a) (by simpa [Nat.add_comm] using hvalid)
  have hra : 0 ≤ (a : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hrb : 0 ≤ (b : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hda : 0 < 1 - (a : ℝ) * u := sub_pos.mpr ha
  have hdb : 0 < 1 - (b : ℝ) * u := sub_pos.mpr hb
  have hdc : 0 < 1 - ((a : ℝ) + b) * u := by
    unfold P12GammaValid at hvalid
    push_cast at hvalid
    linarith
  have hprod : 0 < (1 - (a : ℝ) * u) * (1 - (b : ℝ) * u) := mul_pos hda hdb
  have hdenom : 1 - ((a : ℝ) + b) * u ≤
      (1 - (a : ℝ) * u) * (1 - (b : ℝ) * u) := by
    nlinarith [mul_nonneg hra hrb]
  have hfrac : 1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) ≤
      1 / (1 - ((a : ℝ) + b) * u) := by
    apply (div_le_div_iff₀ hprod hdc).2
    simpa using hdenom
  calc
    p12Gamma u b * (1 + p12Gamma u a) + p12Gamma u a =
        (1 + p12Gamma u a) * (1 + p12Gamma u b) - 1 := by ring
    _ = 1 / ((1 - (a : ℝ) * u) * (1 - (b : ℝ) * u)) - 1 := by
      rw [gamma_one_add u a ha, gamma_one_add u b hb]
      field_simp
    _ ≤ 1 / (1 - ((a : ℝ) + b) * u) - 1 := sub_le_sub_right hfrac 1
    _ = p12Gamma u (a + b) := by
      have heq := gamma_one_add u (a + b) hvalid
      simp only [Nat.cast_add] at heq
      rw [← heq]
      ring

private lemma rounded_mat_mul_bound (fp : P12FPModel) (n : ℕ)
    (A B : P12Matrix n) (hvalid : P12GammaValid fp.u n) (i j : Fin n) :
    |p12RoundedMatMul fp A B i j - p12MatMul A B i j| ≤
      p12Gamma fp.u n *
        p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
      simpa only [p12RoundedMatMul, p12MatMul, p12AbsMatrix, abs_mul] using
        (rounded_dot_bound fp m (A i) (fun k => B k j) hvalid)

private lemma mat_mul_nonneg {n : ℕ} (A B : P12Matrix n)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (i j : Fin n) : 0 ≤ p12MatMul A B i j := by
  unfold p12MatMul
  exact Finset.sum_nonneg (fun t _ => mul_nonneg (hA i t) (hB t j))

private lemma mat_mul_abs_le {n : ℕ} (A B : P12Matrix n)
    (i j : Fin n) :
    |p12MatMul A B i j| ≤
      p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
  calc
    |p12MatMul A B i j| ≤ ∑ t : Fin n, |A i t * B t j| := by
      simpa only [p12MatMul] using
        (Finset.abs_sum_le_sum_abs (fun t : Fin n => A i t * B t j) Finset.univ)
    _ = p12MatMul (p12AbsMatrix A) (p12AbsMatrix B) i j := by
      simp only [p12MatMul, p12AbsMatrix, abs_mul]

private lemma mat_mul_mono_left {n : ℕ} (A C B : P12Matrix n)
    (hAC : ∀ i j, A i j ≤ C i j) (hB : ∀ i j, 0 ≤ B i j)
    (i j : Fin n) : p12MatMul A B i j ≤ p12MatMul C B i j := by
  unfold p12MatMul
  exact Finset.sum_le_sum (fun t _ =>
    mul_le_mul_of_nonneg_right (hAC i t) (hB t j))

private lemma mat_mul_scale_left {n : ℕ} (g : ℝ)
    (A B : P12Matrix n) (i j : Fin n) :
    p12MatMul (fun i j => g * A i j) B i j =
      g * p12MatMul A B i j := by
  simp only [p12MatMul, Finset.mul_sum]
  congr 1
  funext t
  ring

private lemma mat_mul_sub_bound {n : ℕ} (A C P B : P12Matrix n)
    (g : ℝ) (hAC : ∀ i j, |A i j - C i j| ≤ g * P i j)
    (i j : Fin n) :
    |p12MatMul A B i j - p12MatMul C B i j| ≤
      g * p12MatMul P (p12AbsMatrix B) i j := by
  have heq : p12MatMul A B i j - p12MatMul C B i j =
      ∑ t : Fin n, (A i t - C i t) * B t j := by
    simp only [p12MatMul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [heq]
  calc
    |∑ t : Fin n, (A i t - C i t) * B t j| ≤
        ∑ t : Fin n, |(A i t - C i t) * B t j| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun t : Fin n => (A i t - C i t) * B t j) Finset.univ)
    _ ≤ ∑ t : Fin n, (g * P i t) * |B t j| := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hAC i t) (abs_nonneg _)
    _ = g * p12MatMul P (p12AbsMatrix B) i j := by
      simp only [p12MatMul, p12AbsMatrix, Finset.mul_sum]
      congr 1
      funext t
      ring

private lemma power_nonneg {n : ℕ} (X : P12Matrix n) :
    ∀ k i j, 0 ≤ p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      exact abs_nonneg _
  | succ k ih =>
      intro i j
      exact mat_mul_nonneg _ _ ih (fun i j => abs_nonneg (X i j)) i j

private lemma power_abs_le {n : ℕ} (X : P12Matrix n) :
    ∀ k i j, |p12PowerSteps X k i j| ≤
      p12PowerSteps (p12AbsMatrix X) k i j := by
  intro k
  induction k with
  | zero =>
      intro i j
      rfl
  | succ k ih =>
      intro i j
      calc
        |p12PowerSteps X (k + 1) i j| =
            |p12MatMul (p12PowerSteps X k) X i j| := rfl
        _ ≤ p12MatMul (p12AbsMatrix (p12PowerSteps X k))
            (p12AbsMatrix X) i j := mat_mul_abs_le _ _ i j
        _ ≤ p12MatMul (p12PowerSteps (p12AbsMatrix X) k)
            (p12AbsMatrix X) i j :=
              mat_mul_mono_left _ _ _ ih (fun i j => abs_nonneg (X i j)) i j
        _ = p12PowerSteps (p12AbsMatrix X) (k + 1) i j := rfl

/-- P12-C2: Lemma 2.2, reindexed so `k` counts the rounded matrix
multiplications after the supplied matrix `X`. -/
theorem p12_c2_lemma_2_2
    (fp : P12FPModel) (n k : ℕ) (X : P12Matrix n)
    (hvalid : P12GammaValid fp.u (k * n)) :
    ∀ i j,
      |p12RoundedPowerSteps fp X k i j - p12PowerSteps X k i j| ≤
        p12Gamma fp.u (k * n) * p12PowerSteps (p12AbsMatrix X) k i j := by
  -- PROOF_START P12-C2-H001
  induction k with
  | zero =>
      intro i j
      simp [p12RoundedPowerSteps, p12PowerSteps, p12Gamma]
  | succ k ih =>
      have hprevvalid : P12GammaValid fp.u (k * n) :=
        valid_of_le fp.u fp.u_nonneg (Nat.mul_le_mul_right n (Nat.le_succ k)) hvalid
      have hnvalid : P12GammaValid fp.u n := by
        apply valid_of_le fp.u fp.u_nonneg
          (show n ≤ (k + 1) * n by
            calc
              n = 1 * n := by simp
              _ ≤ (k + 1) * n := Nat.mul_le_mul_right n (by omega)) hvalid
      have hIH := ih hprevvalid
      let Y : P12Matrix n := p12RoundedPowerSteps fp X k
      let Z : P12Matrix n := p12PowerSteps X k
      let P : P12Matrix n := p12PowerSteps (p12AbsMatrix X) k
      let G : ℝ := p12Gamma fp.u (k * n)
      let H : ℝ := p12Gamma fp.u n
      have hG : 0 ≤ G := gamma_nonneg fp.u (k * n) fp.u_nonneg hprevvalid
      have hH : 0 ≤ H := gamma_nonneg fp.u n fp.u_nonneg hnvalid
      have hYabs : ∀ i j, |Y i j| ≤ (1 + G) * P i j := by
        intro i j
        calc
          |Y i j| = |(Y i j - Z i j) + Z i j| := by ring
          _ ≤ |Y i j - Z i j| + |Z i j| := abs_add_le _ _
          _ ≤ G * P i j + P i j :=
            add_le_add (hIH i j) (power_abs_le X k i j)
          _ = (1 + G) * P i j := by ring
      have hYmat (i j : Fin n) :
          p12MatMul (p12AbsMatrix Y) (p12AbsMatrix X) i j ≤
            (1 + G) * p12MatMul P (p12AbsMatrix X) i j := by
        calc
          p12MatMul (p12AbsMatrix Y) (p12AbsMatrix X) i j ≤
              p12MatMul (fun i j => (1 + G) * P i j)
                (p12AbsMatrix X) i j := by
            apply mat_mul_mono_left
              (p12AbsMatrix Y) (fun i j => (1 + G) * P i j)
                (p12AbsMatrix X)
            · intro a b
              exact hYabs a b
            · intro a b
              exact abs_nonneg _
          _ = (1 + G) * p12MatMul P (p12AbsMatrix X) i j :=
            mat_mul_scale_left _ _ _ i j
      have hcombine : H * (1 + G) + G ≤ p12Gamma fp.u ((k + 1) * n) := by
        convert gamma_combine fp.u (k * n) n fp.u_nonneg
          (by simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hvalid)
          using 1 <;> simp [G, H, Nat.succ_mul]
      intro i j
      have hQ : 0 ≤ p12PowerSteps (p12AbsMatrix X) (k + 1) i j :=
        power_nonneg X (k + 1) i j
      have hround :
          |p12RoundedMatMul fp Y X i j - p12MatMul Y X i j| ≤
            H * ((1 + G) * p12PowerSteps (p12AbsMatrix X) (k + 1) i j) := by
        calc
          _ ≤ H * p12MatMul (p12AbsMatrix Y) (p12AbsMatrix X) i j :=
            rounded_mat_mul_bound fp n Y X hnvalid i j
          _ ≤ H * ((1 + G) * p12MatMul P (p12AbsMatrix X) i j) :=
            mul_le_mul_of_nonneg_left (hYmat i j) hH
          _ = H * ((1 + G) * p12PowerSteps (p12AbsMatrix X) (k + 1) i j) := rfl
      have hexact :
          |p12MatMul Y X i j - p12MatMul Z X i j| ≤
            G * p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by
        simpa only [P, p12PowerSteps] using
          (mat_mul_sub_bound Y Z P X G hIH i j)
      have hscale := mul_le_mul_of_nonneg_right hcombine hQ
      calc
        |p12RoundedPowerSteps fp X (k + 1) i j -
            p12PowerSteps X (k + 1) i j| =
            |p12RoundedMatMul fp Y X i j - p12MatMul Z X i j| := rfl
        _ ≤ |p12RoundedMatMul fp Y X i j - p12MatMul Y X i j| +
            |p12MatMul Y X i j - p12MatMul Z X i j| := by
              have heq : p12RoundedMatMul fp Y X i j - p12MatMul Z X i j =
                  (p12RoundedMatMul fp Y X i j - p12MatMul Y X i j) +
                    (p12MatMul Y X i j - p12MatMul Z X i j) := by ring
              rw [heq]
              exact abs_add_le _ _
        _ ≤ H * ((1 + G) * p12PowerSteps (p12AbsMatrix X) (k + 1) i j) +
            G * p12PowerSteps (p12AbsMatrix X) (k + 1) i j :=
              add_le_add hround hexact
        _ = (H * (1 + G) + G) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := by ring
        _ ≤ p12Gamma fp.u ((k + 1) * n) *
              p12PowerSteps (p12AbsMatrix X) (k + 1) i j := hscale

end VSCLReuse

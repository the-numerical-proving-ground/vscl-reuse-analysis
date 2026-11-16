import VSCLReuse.P48.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p48_pow_bound (u : ℝ) (hu : 0 ≤ u) (n : ℕ)
    (hv : (n : ℝ) * u < 1) :
    (1 + u) ^ n - 1 ≤ p48Gamma u n := by
  have hprod : ∀ k : ℕ, (1 + u) ^ k * (1 - (k : ℝ) * u) ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hp : 0 ≤ (1 + u) ^ k * ((k : ℝ) + 1) * u ^ 2 := by positivity
        calc
          (1 + u) ^ (k + 1) * (1 - ((k + 1 : ℕ) : ℝ) * u) =
              (1 + u) ^ k * (1 - (k : ℝ) * u) -
                (1 + u) ^ k * ((k : ℝ) + 1) * u ^ 2 := by
                  push_cast; ring
          _ ≤ (1 + u) ^ k * (1 - (k : ℝ) * u) := sub_le_self _ hp
          _ ≤ 1 := ih
  have hd : 0 < 1 - (n : ℝ) * u := by linarith
  have h := hprod n
  unfold p48Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private lemma p48_fold_bound (fp : P48FPModel) (n : ℕ)
    (a : Fin n → ℝ) (init : ℝ) :
    |Fin.foldl n (fun acc i => fp.flHighAdd acc (a i)) init -
        (init + ∑ i, a i)| ≤
      ((1 + fp.uHigh) ^ n - 1) * (|init| + ∑ i, |a i|) := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
      let r := Fin.foldl n (fun acc i => fp.flHighAdd acc (a i.castSucc)) init
      let v := init + ∑ i : Fin n, a i.castSucc
      let s := |init| + ∑ i : Fin n, |a i.castSucc|
      let b := a (Fin.last n)
      have hi : |r - v| ≤ ((1 + fp.uHigh) ^ n - 1) * s := by
        simpa [r, v, s] using ih (fun i : Fin n => a i.castSucc) init
      have hs : 0 ≤ s := by
        dsimp [s]
        positivity
      have hv : |v| ≤ s := by
        dsimp [v, s]
        calc
          |init + ∑ i : Fin n, a i.castSucc| ≤
              |init| + |∑ i : Fin n, a i.castSucc| := abs_add_le _ _
          _ ≤ |init| + ∑ i : Fin n, |a i.castSucc| := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
      obtain ⟨δ, hδ, hfl⟩ := fp.modelHighAdd r b
      have hδ' : |1 + δ| ≤ 1 + fp.uHigh := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.uHigh := by simpa using add_le_add_left hδ 1
      have hq : 0 ≤ (1 + fp.uHigh) ^ n - 1 := by
        have hp : 1 ≤ (1 + fp.uHigh) ^ n := one_le_pow₀ (by linarith [fp.uHigh_nonneg])
        linarith
      have hterm : |v + b| ≤ s + |b| := by
        linarith [abs_add_le v b]
      have hstep : |fp.flHighAdd r b - (v + b)| ≤
          (1 + fp.uHigh) * (((1 + fp.uHigh) ^ n - 1) * s) +
            fp.uHigh * (s + |b|) := by
        rw [hfl]
        have heq : (r + b) * (1 + δ) - (v + b) =
            (r - v) * (1 + δ) + δ * (v + b) := by ring
        rw [heq]
        calc
          |(r - v) * (1 + δ) + δ * (v + b)| ≤
              |(r - v) * (1 + δ)| + |δ * (v + b)| := abs_add_le _ _
          _ = |r - v| * |1 + δ| + |δ| * |v + b| := by rw [abs_mul, abs_mul]
          _ ≤ ((1 + fp.uHigh) ^ n - 1) * s * (1 + fp.uHigh) +
              fp.uHigh * (s + |b|) := by
                apply add_le_add
                · exact mul_le_mul hi hδ' (abs_nonneg _) (mul_nonneg hq hs)
                · exact mul_le_mul hδ hterm (abs_nonneg _) fp.uHigh_nonneg
          _ = _ := by ring
      have hstep' : |fp.flHighAdd r b - (v + b)| ≤
          ((1 + fp.uHigh) ^ (n + 1) - 1) * (s + |b|) := by
        calc
          _ ≤ (1 + fp.uHigh) * (((1 + fp.uHigh) ^ n - 1) * s) +
                fp.uHigh * (s + |b|) := hstep
          _ ≤ ((1 + fp.uHigh) ^ (n + 1) - 1) * (s + |b|) := by
            have hp : 0 ≤ (1 + fp.uHigh) * (((1 + fp.uHigh) ^ n - 1) * |b|) :=
              mul_nonneg (by linarith [fp.uHigh_nonneg]) (mul_nonneg hq (abs_nonneg b))
            rw [pow_succ]
            nlinarith
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simpa only [r, v, s, b, add_assoc] using hstep'

private lemma p48_high_dot_bound (fp : P48FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    |p48HighDot fp (n + 1) x y - ∑ i, x i * y i| ≤
      ((1 + fp.uHigh) ^ n - 1) * ∑ i, |x i * y i| := by
  have h := p48_fold_bound fp n (fun i : Fin n => x i.succ * y i.succ)
      (x 0 * y 0)
  unfold p48HighDot
  rw [Fin.foldl_succ, fp.flHighAdd_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simpa using h

private noncomputable def p48_sign (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

private lemma p48_sign_mul (z : ℝ) : p48_sign z * z = |z| := by
  by_cases hz : 0 ≤ z
  · simp [p48_sign, hz, abs_of_nonneg hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    simp [p48_sign, hz, abs_of_neg hz']

private lemma p48_abs_sign (z : ℝ) : |p48_sign z| = 1 := by
  by_cases hz : 0 ≤ z <;> simp [p48_sign, hz]

private lemma p48_mixed_dot_forward_bound (fp : P48FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) (hvalid : P48GammaValid fp.uHigh n) :
    |p48MixedDot fp (n + 1) x y - ∑ i, x i * y i| ≤
      ((1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1) *
        ∑ i, |x i * y i| := by
  let A := p48HighDot fp (n + 1) x y
  let B := ∑ i : Fin (n + 1), x i * y i
  let S := ∑ i : Fin (n + 1), |x i * y i|
  let q := (1 + fp.uHigh) ^ n - 1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB : |B| ≤ S := by
    dsimp [B, S]
    exact Finset.abs_sum_le_sum_abs _ _
  have hA : |A - B| ≤ q * S := by
    simpa [A, B, S, q] using p48_high_dot_bound fp n x y
  obtain ⟨δ, hδ, hcast⟩ := fp.castDown_model A
  have hδ' : |1 + δ| ≤ 1 + fp.uLow := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.uLow := by simpa using add_le_add_left hδ 1
  have hq : 0 ≤ q := by
    dsimp [q]
    have hp : 1 ≤ (1 + fp.uHigh) ^ n :=
      one_le_pow₀ (by linarith [fp.uHigh_nonneg])
    linarith
  have hcastbound : |p48MixedDot fp (n + 1) x y - B| ≤
      ((1 + fp.uLow) * (1 + q) - 1) * S := by
    change |fp.castDown A - B| ≤ _
    rw [hcast]
    have heq : A * (1 + δ) - B = (A - B) * (1 + δ) + δ * B := by ring
    rw [heq]
    calc
      |(A - B) * (1 + δ) + δ * B| ≤
          |(A - B) * (1 + δ)| + |δ * B| := abs_add_le _ _
      _ = |A - B| * |1 + δ| + |δ| * |B| := by rw [abs_mul, abs_mul]
      _ ≤ q * S * (1 + fp.uLow) + fp.uLow * S := by
        apply add_le_add
        · exact mul_le_mul hA hδ' (abs_nonneg _) (mul_nonneg hq hS)
        · exact mul_le_mul hδ hB (abs_nonneg _) fp.uLow_nonneg
      _ = ((1 + fp.uLow) * (1 + q) - 1) * S := by ring
  have hpow : q ≤ p48Gamma fp.uHigh n :=
    p48_pow_bound fp.uHigh fp.uHigh_nonneg n hvalid
  have hcoef : (1 + fp.uLow) * (1 + q) - 1 ≤
      (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + fp.uLow by linarith [fp.uLow_nonneg])
      (sub_nonneg.mpr hpow)]
  exact hcastbound.trans (mul_le_mul_of_nonneg_right hcoef hS)

private lemma p48_backward_from_forward (m : ℕ) (x y : Fin m → ℝ)
    (z c : ℝ) (hc : 0 ≤ c)
    (herr : |z - ∑ i, x i * y i| ≤ c * ∑ i, |x i * y i|) :
    ∃ dx dy : Fin m → ℝ,
      (∀ i, |dx i| ≤ c * |x i|) ∧
      (∀ i, |dy i| ≤ c * |y i|) ∧
      z = ∑ i, (x i + dx i) * y i ∧
      z = ∑ i, x i * (y i + dy i) := by
  let B := ∑ i : Fin m, x i * y i
  let S := ∑ i : Fin m, |x i * y i|
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  by_cases hS : S = 0
  · have he : z = B := by
      have hzero : |z - B| ≤ 0 := by
        have hh : |z - B| ≤ c * S := herr
        simpa [hS] using hh
      have habs : |z - B| = 0 := le_antisymm hzero (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs)
    refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro i
      simpa using mul_nonneg hc (abs_nonneg (x i))
    · intro i
      simpa using mul_nonneg hc (abs_nonneg (y i))
    · simpa [B] using he
    · simpa [B] using he
  · have hSpos : 0 < S := by
      rcases lt_or_eq_of_le hSnonneg with hp | hz
      · exact hp
      · exact False.elim (hS hz.symm)
    let t := (z - B) / S
    have ht : |t| ≤ c := by
      dsimp [t]
      rw [abs_div, abs_of_nonneg hSpos.le]
      exact (div_le_iff₀ hSpos).2 (by simpa [B, S] using herr)
    have hte : t * S = z - B := by
      dsimp [t]
      exact div_mul_cancel₀ _ hS
    let dx : Fin m → ℝ := fun i => t * |x i| * p48_sign (y i)
    let dy : Fin m → ℝ := fun i => t * |y i| * p48_sign (x i)
    have hdx : ∀ i, |dx i| ≤ c * |x i| := by
      intro i
      simpa [dx, abs_mul, p48_abs_sign] using
        mul_le_mul_of_nonneg_right ht (abs_nonneg (x i))
    have hdy : ∀ i, |dy i| ≤ c * |y i| := by
      intro i
      simpa [dy, abs_mul, p48_abs_sign] using
        mul_le_mul_of_nonneg_right ht (abs_nonneg (y i))
    have hdxterm (i : Fin m) : dx i * y i = t * |x i * y i| := by
      calc
        dx i * y i = t * |x i| * (p48_sign (y i) * y i) := by
          dsimp [dx]; ring
        _ = t * |x i * y i| := by rw [p48_sign_mul, abs_mul]; ring
    have hdyterm (i : Fin m) : x i * dy i = t * |x i * y i| := by
      calc
        x i * dy i = t * (p48_sign (x i) * x i) * |y i| := by
          dsimp [dy]; ring
        _ = t * |x i * y i| := by rw [p48_sign_mul, abs_mul]; ring
    refine ⟨dx, dy, hdx, hdy, ?_, ?_⟩
    · calc
        z = B + t * S := by linarith
        _ = ∑ i, (x i + dx i) * y i := by
          simp_rw [add_mul, Finset.sum_add_distrib, hdxterm]
          simp only [B, S, Finset.mul_sum]
    · calc
        z = B + t * S := by linarith
        _ = ∑ i, x i * (y i + dy i) := by
          simp_rw [mul_add, Finset.sum_add_distrib, hdyterm]
          simp only [B, S, Finset.mul_sum]

theorem p48_c2_mixed_dot_backward_bound
    (fp : P48FPModel) (n : ℕ) (x y : Fin (n + 1) → ℝ)
    (hvalid : P48GammaValid fp.uHigh n) :
    let c := (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1
    ∃ dx dy : Fin (n + 1) → ℝ,
      (∀ i, |dx i| ≤ c * |x i|) ∧
      (∀ i, |dy i| ≤ c * |y i|) ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), (x i + dx i) * y i ∧
      p48MixedDot fp (n + 1) x y =
        ∑ i : Fin (n + 1), x i * (y i + dy i) := by
  -- PROOF_START P48-C2-H001
  let c := (1 + fp.uLow) * (1 + p48Gamma fp.uHigh n) - 1
  have hgamma : 0 ≤ p48Gamma fp.uHigh n := by
    have hq : 0 ≤ (1 + fp.uHigh) ^ n - 1 := by
      have hp : 1 ≤ (1 + fp.uHigh) ^ n :=
        one_le_pow₀ (by linarith [fp.uHigh_nonneg])
      linarith
    exact hq.trans (p48_pow_bound fp.uHigh fp.uHigh_nonneg n hvalid)
  have hc : 0 ≤ c := by
    dsimp [c]
    nlinarith [fp.uLow_nonneg, hgamma, mul_nonneg fp.uLow_nonneg hgamma]
  exact p48_backward_from_forward (n + 1) x y
    (p48MixedDot fp (n + 1) x y) c hc
    (by simpa only [c] using p48_mixed_dot_forward_bound fp n x y hvalid)

end VSCLReuse

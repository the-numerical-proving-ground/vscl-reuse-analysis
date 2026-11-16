import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma recursiveSum_bounds (fp : StandardAddModel)
    (hu : fp.u ≤ 1) : ∀ (n : ℕ) (v : Fin n → ℝ),
      (∀ i, 0 ≤ v i) →
      (1 - fp.u) ^ n * (∑ i, v i) ≤ recursiveSum fp.fl_add n v ∧
      recursiveSum fp.fl_add n v ≤ (1 + fp.u) ^ n * (∑ i, v i) := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [recursiveSum]
  | succ n ih =>
      intro v hv
      cases n with
      | zero =>
          simp [recursiveSum]
          constructor <;> nlinarith [hv 0, fp.u_nonneg]
      | succ m =>
          have hm : m + 1 ≠ 0 := by omega
          have hrec := ih (fun i : Fin (m + 1) => v i.castSucc)
            (fun i => hv i.castSucc)
          obtain ⟨δ, hδ, hadd⟩ := fp.model_add
            (recursiveSum fp.fl_add (m + 1) (fun i => v i.castSucc))
            (v (Fin.last (m + 1)))
          have hδlo : 1 - fp.u ≤ 1 + δ := by
            have := (abs_le.mp hδ).1
            linarith
          have hδhi : 1 + δ ≤ 1 + fp.u := by
            have := (abs_le.mp hδ).2
            linarith
          have hp : 0 ≤ 1 - fp.u := by linarith
          have hq : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hp1 : (1 - fp.u) ^ (m + 1) ≤ 1 := by
            calc
              _ ≤ (1 : ℝ) ^ (m + 1) := by gcongr; linarith [fp.u_nonneg]
              _ = 1 := by simp
          have hq1 : 1 ≤ (1 + fp.u) ^ (m + 1) := by
            calc
              1 = (1 : ℝ) ^ (m + 1) := by simp
              _ ≤ _ := by gcongr; linarith [fp.u_nonneg]
          rw [recursiveSum, dif_neg hm, hadd, Fin.sum_univ_castSucc]
          constructor
          · have hA : 0 ≤ (∑ i : Fin (m + 1), v i.castSucc) :=
              Finset.sum_nonneg (fun i hi => hv i.castSucc)
            have hb : 0 ≤ v (Fin.last (m + 1)) := hv _
            have hbase : (1 - fp.u) ^ (m + 1) *
                ((∑ i : Fin (m + 1), v i.castSucc) + v (Fin.last (m + 1))) ≤
                recursiveSum fp.fl_add (m + 1) (fun i => v i.castSucc) +
                v (Fin.last (m + 1)) := by
              nlinarith [mul_nonneg (pow_nonneg hp (m + 1)) hb]
            have hnonneg : 0 ≤ recursiveSum fp.fl_add (m + 1)
                (fun i => v i.castSucc) + v (Fin.last (m + 1)) := by
              nlinarith [mul_nonneg (pow_nonneg hp (m + 1)) (add_nonneg hA hb)]
            rw [pow_succ]
            nlinarith [mul_le_mul_of_nonneg_left hbase hp,
              mul_le_mul_of_nonneg_left hδlo hnonneg]
          · have hA : 0 ≤ (∑ i : Fin (m + 1), v i.castSucc) :=
              Finset.sum_nonneg (fun i hi => hv i.castSucc)
            have hb : 0 ≤ v (Fin.last (m + 1)) := hv _
            have hbase : recursiveSum fp.fl_add (m + 1) (fun i => v i.castSucc) +
                v (Fin.last (m + 1)) ≤
                (1 + fp.u) ^ (m + 1) *
                  ((∑ i : Fin (m + 1), v i.castSucc) + v (Fin.last (m + 1))) := by
              nlinarith
            have hnonneg : 0 ≤ recursiveSum fp.fl_add (m + 1)
                (fun i => v i.castSucc) + v (Fin.last (m + 1)) := by
              nlinarith [mul_nonneg (pow_nonneg hp (m + 1)) (add_nonneg hA hb)]
            rw [pow_succ]
            nlinarith [mul_le_mul_of_nonneg_left hbase hq,
              mul_le_mul_of_nonneg_left hδhi hnonneg]

private lemma pow_one_add_quadratic (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      (1 + u) ^ k ≤ 1 + (k : ℝ) * u + C * u ^ 2 := by
  induction k with
  | zero =>
      refine ⟨0, le_refl _, ?_⟩
      intro u hu hu1
      simp
  | succ k ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨2 * C + k, by positivity, ?_⟩
      intro u hu hu1
      have h := mul_le_mul_of_nonneg_right (hbound u hu hu1)
        (by linarith : 0 ≤ 1 + u)
      have hcube := mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)
      rw [pow_succ]
      push_cast
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hcube)]

private lemma computed_sum_bounds {n : ℕ} (x : Fin n → ℝ) (u : ℝ)
    (run : P07BasicSumExecution x u) (hu : u ≤ 1) :
    (1 - u) ^ (n + 1) * p07ExpSum x ≤ p07RecursiveComputedExpSum run ∧
    p07RecursiveComputedExpSum run ≤ (1 + u) ^ (n + 1) * p07ExpSum x := by
  have hu0 : 0 ≤ u := run.unit_eq ▸ run.fp.u_nonneg
  have hterm (i : Fin n) :
      (1 - u) * Real.exp (x i) ≤ p07ComputedExp run i ∧
      p07ComputedExp run i ≤ (1 + u) * Real.exp (x i) := by
    have he := Real.exp_pos (x i)
    have herr := abs_le.mp (run.expError_le i)
    simp only [p07ComputedExp]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right
        (show 1 - u ≤ 1 + run.expError i by linarith) (le_of_lt he)]
    · nlinarith [mul_le_mul_of_nonneg_right
        (show 1 + run.expError i ≤ 1 + u by linarith) (le_of_lt he)]
  have hw : ∀ i, 0 ≤ p07ComputedExp run i := by
    intro i
    have h := (hterm i).1
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - u)
      (le_of_lt (Real.exp_pos (x i)))]
  have hsumlo : (1 - u) * p07ExpSum x ≤ p07ExactComputedExpSum run := by
    simp only [p07ExpSum, p07ExactComputedExpSum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (hterm i).1)
  have hsumhi : p07ExactComputedExpSum run ≤ (1 + u) * p07ExpSum x := by
    simp only [p07ExpSum, p07ExactComputedExpSum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => (hterm i).2)
  have hfp : run.fp.u ≤ 1 := by rw [run.unit_eq]; exact hu
  have hrec := recursiveSum_bounds run.fp hfp n
    (p07ComputedExp run) hw
  simp only [run.unit_eq] at hrec
  have hp : 0 ≤ (1 - u) ^ n := pow_nonneg (by linarith) _
  have hq : 0 ≤ (1 + u) ^ n := pow_nonneg (by linarith) _
  simp only [p07RecursiveComputedExpSum, p07ExactComputedExpSum] at *
  constructor
  · calc
      (1 - u) ^ (n + 1) * p07ExpSum x =
          (1 - u) ^ n * ((1 - u) * p07ExpSum x) := by rw [pow_succ]; ring
      _ ≤ (1 - u) ^ n * (∑ i, p07ComputedExp run i) :=
        mul_le_mul_of_nonneg_left hsumlo hp
      _ ≤ _ := hrec.1
  · calc
      _ ≤ (1 + u) ^ n * (∑ i, p07ComputedExp run i) := hrec.2
      _ ≤ (1 + u) ^ n * ((1 + u) * p07ExpSum x) :=
        mul_le_mul_of_nonneg_left hsumhi hq
      _ = (1 + u) ^ (n + 1) * p07ExpSum x := by rw [pow_succ]; ring

private lemma p07_expSum_pos {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    0 < p07ExpSum x := by
  unfold p07ExpSum
  exact Finset.sum_pos (fun i hi => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

private lemma softmax_ratio_bound {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (u C : ℝ)
    (run : P07BasicSumExecution x u) (divError : Fin n → ℝ)
    (hdiv : ∀ i, |divError i| ≤ u) (hC : 0 ≤ C)
    (hpow : (1 + u) ^ (n + 1) ≤
      1 + (n + 1 : ℝ) * u + C * u ^ 2)
    (hsmall : (n + 1 : ℝ) * u ≤ 1 / 2) :
    ‖(fun i : Fin n => p07ComputedSoftmax run divError i -
      p07ExactSoftmax x i)‖ /
      ‖(fun i : Fin n => p07ExactSoftmax x i)‖ ≤
      (((n + 3 : ℝ) * u + (C + 1) * u ^ 2) /
        (1 - (n + 1 : ℝ) * u)) := by
  let S := p07ExpSum x
  let A := p07RecursiveComputedExpSum run
  let k : ℝ := n + 1
  let B : ℝ := (n + 3 : ℝ) * u + (C + 1) * u ^ 2
  let d : ℝ := 1 - k * u
  have hu0 : 0 ≤ u := by rw [← run.unit_eq]; exact run.fp.u_nonneg
  have hku : 0 ≤ k := by dsimp [k]; positivity
  have hu1 : u ≤ 1 := by
    have hk : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hu0]
  have hS : 0 < S := p07_expSum_pos hn x
  have hd : 0 < d := by dsimp [d, k]; linarith
  have hbounds := computed_sum_bounds x u run hu1
  have hBern : d ≤ (1 - u) ^ (n + 1) := by
    simpa [d, k, sub_eq_add_neg, mul_neg] using
      (one_add_mul_le_pow (show (-2 : ℝ) ≤ -u by linarith) (n + 1))
  have hAlo : d * S ≤ A := by
    calc
      d * S ≤ (1 - u) ^ (n + 1) * S :=
        mul_le_mul_of_nonneg_right hBern (le_of_lt hS)
      _ ≤ A := hbounds.1
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos hd hS) hAlo
  have hAhi : A ≤ (1 + k * u + C * u ^ 2) * S := by
    calc
      A ≤ (1 + u) ^ (n + 1) * S := hbounds.2
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa [k] using hpow) (le_of_lt hS)
  have hAerr : |A - S| ≤ S * (k * u + C * u ^ 2) := by
    apply abs_le.mpr
    have hCu : 0 ≤ C * u ^ 2 := mul_nonneg hC (sq_nonneg u)
    constructor <;> dsimp [d] at hAlo <;> nlinarith
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hnormS : 0 < ‖(fun i : Fin n => p07ExactSoftmax x i)‖ := by
    have i0 : Fin n := ⟨0, hn⟩
    have hi : 0 < p07ExactSoftmax x i0 := by
      unfold p07ExactSoftmax
      exact div_pos (Real.exp_pos _) hS
    have hle := norm_le_pi_norm (fun i : Fin n => p07ExactSoftmax x i) i0
    rw [Real.norm_eq_abs, abs_of_pos hi] at hle
    linarith
  have hpoint (i : Fin n) :
      |p07ComputedSoftmax run divError i - p07ExactSoftmax x i| ≤
        p07ExactSoftmax x i * (B / d) := by
    let e := run.expError i
    let f := divError i
    let p := (1 + e) * (1 + f)
    have he : |e| ≤ u := run.expError_le i
    have hf : |f| ≤ u := hdiv i
    have hprod : |e * f| ≤ u ^ 2 := by
      rw [abs_mul]
      calc
        |e| * |f| ≤ u * |f| := mul_le_mul_of_nonneg_right he (abs_nonneg f)
        _ ≤ u * u := mul_le_mul_of_nonneg_left hf hu0
        _ = u ^ 2 := by ring
    have hp : |p - 1| ≤ 2 * u + u ^ 2 := by
      have htri := abs_add_le (e + f) (e * f)
      have htri2 := abs_add_le e f
      have hpEq : p - 1 = (e + f) + e * f := by dsimp [p]; ring
      rw [hpEq]
      linarith
    have hnum : |p * S - A| ≤ S * B := by
      have htri := abs_add_le ((p - 1) * S) (S - A)
      have heq : p * S - A = (p - 1) * S + (S - A) := by ring
      have h1 := mul_le_mul_of_nonneg_right hp (le_of_lt hS)
      have h2 : |S - A| ≤ S * (k * u + C * u ^ 2) := by
        rwa [abs_sub_comm]
      calc
        |p * S - A| = |(p - 1) * S + (S - A)| := congrArg abs heq
        _ ≤ |(p - 1) * S| + |S - A| := htri
        _ ≤ S * B := by
          rw [abs_mul, abs_of_pos hS]
          dsimp [B, k] at h2 ⊢
          nlinarith
    have hexact : 0 < p07ExactSoftmax x i := by
      unfold p07ExactSoftmax
      exact div_pos (Real.exp_pos _) hS
    have hid : p07ComputedSoftmax run divError i - p07ExactSoftmax x i =
        p07ExactSoftmax x i * ((p * S - A) / A) := by
      change Real.exp (x i) * (1 + e) / A * (1 + f) - Real.exp (x i) / S =
        (Real.exp (x i) / S) * ((p * S - A) / A)
      have hAne : A ≠ 0 := ne_of_gt hApos
      have hSne : S ≠ 0 := ne_of_gt hS
      field_simp [hAne, hSne]
      dsimp [p]
      ring
    have hratio : |p * S - A| / A ≤ B / d := by
      apply (div_le_div_iff₀ hApos hd).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hAlo) hBnonneg]
    rw [hid, abs_mul, abs_of_pos hexact, abs_div, abs_of_pos hApos]
    exact mul_le_mul_of_nonneg_left hratio (le_of_lt hexact)
  have hnorm : ‖(fun i : Fin n => p07ComputedSoftmax run divError i -
      p07ExactSoftmax x i)‖ ≤
      ‖(fun i : Fin n => p07ExactSoftmax x i)‖ * (B / d) := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_of_lt hnormS)
      (div_nonneg hBnonneg (le_of_lt hd)))).2
    intro i
    rw [Real.norm_eq_abs]
    have hexact : 0 < p07ExactSoftmax x i :=
      div_pos (Real.exp_pos _) hS
    have hle := norm_le_pi_norm (fun i : Fin n => p07ExactSoftmax x i) i
    rw [Real.norm_eq_abs, abs_of_pos hexact] at hle
    exact le_trans (hpoint i) (mul_le_mul_of_nonneg_right hle
      (div_nonneg hBnonneg (le_of_lt hd)))
  apply (div_le_iff₀ hnormS).2
  simpa [B, d, k, mul_comm, mul_left_comm, mul_assoc] using hnorm

/-- Blanchard–Higham–Higham, full Theorem 3.3, equation (3.6). -/
theorem p07_c2_full_basic_softmax_algorithm
    {n : ℕ} (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : Fin n → ℝ)
    (u : ι → ℝ)
    (run : ∀ t, P07BasicSumExecution x (u t))
    (divError : ∀ t, Fin n → ℝ)
    (hdiv : ∀ t i, |divError t i| ≤ u t)
    (hu : Filter.Tendsto u l (nhds 0)) :
    ∃ remainder : ι → ℝ,
      remainder =O[l] (fun t => (u t) ^ 2) ∧
      ∀ᶠ t in l,
        ‖(fun i : Fin n =>
            p07ComputedSoftmax (run t) (divError t) i -
              p07ExactSoftmax x i)‖ /
          ‖(fun i : Fin n => p07ExactSoftmax x i)‖ ≤
          (n + 3 : ℝ) * u t + |remainder t| := by
  -- PROOF_START P07-C2-H001
  obtain ⟨C, hC, hpow⟩ := pow_one_add_quadratic (n + 1)
  let k : ℝ := n + 1
  let D : ℝ := C + 1 + k * (n + 3)
  let remainder : ι → ℝ := fun t => D * (u t) ^ 2 / (1 - k * u t)
  have hkpos : 0 < k := by dsimp [k]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hnear : ∀ᶠ t in l, u t < 1 / (2 * k) :=
    Filter.Tendsto.eventually_lt_const (by positivity) hu
  have hsmall : ∀ᶠ t in l, k * u t ≤ 1 / 2 := by
    filter_upwards [hnear] with t ht
    have h := mul_lt_mul_of_pos_left ht hkpos
    have heq : k * (1 / (2 * k)) = (1 / 2 : ℝ) := by
      field_simp
    rw [heq] at h
    exact le_of_lt h
  refine ⟨remainder, ?_, ?_⟩
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨2 * D, ?_⟩
    filter_upwards [hsmall] with t ht
    have hu0 : 0 ≤ u t := by rw [← (run t).unit_eq]; exact (run t).fp.u_nonneg
    have hd : 0 < 1 - k * u t := by linarith
    have hdhalf : (1 / 2 : ℝ) ≤ 1 - k * u t := by linarith
    have hnum : 0 ≤ D * (u t) ^ 2 := mul_nonneg hD (sq_nonneg _)
    have hrnonneg : 0 ≤ remainder t := div_nonneg hnum (le_of_lt hd)
    have hrbound : remainder t ≤ (2 * D) * (u t) ^ 2 := by
      dsimp [remainder]
      apply (div_le_iff₀ hd).2
      nlinarith [mul_le_mul_of_nonneg_left hdhalf hnum]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hrnonneg,
      abs_of_nonneg (sq_nonneg (u t))]
    exact hrbound
  · filter_upwards [hsmall] with t ht
    have hu0 : 0 ≤ u t := by rw [← (run t).unit_eq]; exact (run t).fp.u_nonneg
    have hkge : (1 : ℝ) ≤ k := by
      dsimp [k]
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    have hu1 : u t ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkge) hu0]
    have hd : 0 < 1 - k * u t := by linarith
    have hpow' : (1 + u t) ^ (n + 1) ≤
        1 + (n + 1 : ℝ) * u t + C * (u t) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hpow (u t) hu0 hu1
    have hbound := softmax_ratio_bound hn x (u t) C (run t) (divError t)
      (hdiv t) hC hpow' (by simpa [k] using ht)
    have hrnonneg : 0 ≤ remainder t := by
      dsimp [remainder]
      exact div_nonneg (mul_nonneg hD (sq_nonneg _)) (le_of_lt hd)
    have heq :
        (((n + 3 : ℝ) * u t + (C + 1) * (u t) ^ 2) /
          (1 - (n + 1 : ℝ) * u t)) =
        (n + 3 : ℝ) * u t + remainder t := by
      change (((n + 3 : ℝ) * u t + (C + 1) * (u t) ^ 2) /
          (1 - (n + 1 : ℝ) * u t)) =
        (n + 3 : ℝ) * u t +
          (C + 1 + (n + 1 : ℝ) * (n + 3 : ℝ)) * (u t) ^ 2 /
            (1 - (n + 1 : ℝ) * u t)
      have hden : 1 - (n + 1 : ℝ) * u t ≠ 0 := ne_of_gt hd
      have hnum :
          (n + 3 : ℝ) * u t + (C + 1) * (u t) ^ 2 =
          ((n + 3 : ℝ) * u t) * (1 - (n + 1 : ℝ) * u t) +
            (C + 1 + (n + 1 : ℝ) * (n + 3 : ℝ)) * (u t) ^ 2 := by ring
      rw [hnum, add_div, mul_div_cancel_right₀ _ hden]
    rw [heq] at hbound
    simpa [abs_of_nonneg hrnonneg] using hbound

end VSCLReuse

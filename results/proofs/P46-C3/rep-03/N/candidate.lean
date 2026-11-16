import VSCLReuse.P46.Definitions

namespace VSCLReuse

open scoped BigOperators


private theorem p46_gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u k) : 0 ≤ p46Gamma u k := by
  unfold p46Gamma P46GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hk))

private theorem p46_gamma_valid_mono (u : ℝ) (k l : ℕ) (hu : 0 ≤ u)
    (hkl : k ≤ l) (hl : P46GammaValid u l) : P46GammaValid u k := by
  unfold P46GammaValid at *
  have hc : (k : ℝ) ≤ l := by exact_mod_cast hkl
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) hu]

private theorem p46_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P46GammaValid u (k + 1)) :
    p46Gamma u k + u ≤ (1 - u) * p46Gamma u (k + 1) ∧
    u * (1 + u) ≤ (1 - u) * p46Gamma u (k + 1) := by
  unfold P46GammaValid at hvalid
  have hvalid' : ((k : ℝ) + 1) * u < 1 := by simpa using hvalid
  have hku : (k : ℝ) * u < 1 := by
    nlinarith
  have hku0 : 0 < 1 - (k : ℝ) * u := by linarith
  have hku1 : 0 < 1 - (k + 1 : ℝ) * u := by linarith
  have hu1 : u < 1 := by
    have : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast (Nat.le_add_left 1 k)
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hu]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold p46Gamma
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · rw [show (k : ℝ) * u / (1 - (k : ℝ) * u) + u =
        ((k : ℝ) * u + u * (1 - (k : ℝ) * u)) /
          (1 - (k : ℝ) * u) by field_simp]
    rw [show (1 - u) * ((k + 1 : ℝ) * u / (1 - (k + 1 : ℝ) * u)) =
        ((1 - u) * ((k + 1 : ℝ) * u)) /
          (1 - (k + 1 : ℝ) * u) by ring]
    apply (div_le_div_iff₀ hku0 hku1).2
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) (sq_nonneg u)]
  · rw [show (1 - u) * ((k + 1 : ℝ) * u / (1 - (k + 1 : ℝ) * u)) =
        ((1 - u) * ((k + 1 : ℝ) * u)) /
          (1 - (k + 1 : ℝ) * u) by ring]
    apply (le_div_iff₀ hku1).2
    have hkk : (2 : ℝ) ≤ (k + 1 : ℝ) := by nlinarith
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity) (sq_nonneg u)]

private theorem p46_gamma_mono (u : ℝ) (k l : ℕ) (hu : 0 ≤ u)
    (hkl : k ≤ l) (hl : P46GammaValid u l) :
    p46Gamma u k ≤ p46Gamma u l := by
  have hk := p46_gamma_valid_mono u k l hu hkl hl
  unfold p46Gamma P46GammaValid at *
  have hden1 : 0 < 1 - (k : ℝ) * u := by linarith
  have hden2 : 0 < 1 - (l : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hden1 hden2).2
  have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
  nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hu]

private theorem p46_gamma_forward_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : 1 ≤ k) (hvalid : P46GammaValid u (k + 1)) :
    (1 + u) * p46Gamma u k + u ≤ p46Gamma u (k + 1) ∧
    u * (2 + u) ≤ p46Gamma u (k + 1) := by
  have hku := p46_gamma_valid_mono u k (k + 1) hu (by omega) hvalid
  have hden1 : 0 < 1 - (k : ℝ) * u := by
    unfold P46GammaValid at hku
    linarith
  have hden2 : 0 < 1 - (k + 1 : ℝ) * u := by
    have hv : ((k : ℝ) + 1) * u < 1 := by simpa [P46GammaValid] using hvalid
    exact sub_pos.mpr hv
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold p46Gamma
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · rw [show (1 + u) * ((k : ℝ) * u / (1 - (k : ℝ) * u)) + u =
        ((1 + u) * ((k : ℝ) * u) + u * (1 - (k : ℝ) * u)) /
          (1 - (k : ℝ) * u) by
          have hD : 1 - u * (k : ℝ) ≠ 0 := by nlinarith [hden1]
          field_simp [ne_of_gt hden1, hD]]
    apply (div_le_div_iff₀ hden1 hden2).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity)
      (sq_nonneg u)]
  · apply (le_div_iff₀ hden2).2
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ k - 1)) hu,
      mul_nonneg (show (0 : ℝ) ≤ (k + 1 : ℝ) by positivity) (sq_nonneg u)]

private theorem p46_reverse_sub_step
    (u c d W z s v s' δm δs : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hW : 0 ≤ W)
    (hm : |δm| ≤ u) (hs : |δs| ≤ u)
    (hs' : s' = (s - v * (1 + δm)) * (1 + δs))
    (hz : |z| ≤ W) (he : |z - s'| ≤ c * W)
    (hcoef : c + u ≤ (1 - u) * d)
    (hterm : u * (1 + u) ≤ (1 - u) * d) :
    |z + v - s| ≤ d * (W + |v|) := by
  have hlow : 1 - u ≤ |1 + δs| := by
    have := abs_add_le (1 + δs) (-δs)
    simp only [add_neg_cancel_right, abs_one, abs_neg] at this
    linarith
  have hupp : |1 + δs| ≤ 1 + u := by
    calc |1 + δs| ≤ |(1 : ℝ)| + |δs| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hs 1
  let r := z + v - s
  have hid : r * (1 + δs) = (z - s') + z * δs - v * δm * (1 + δs) := by
    dsimp [r]
    rw [hs']
    ring
  have htri : |r * (1 + δs)| ≤ |z - s'| + |z| * |δs| + |v| * |δm| * |1 + δs| := by
    rw [hid]
    calc
      |(z - s') + z * δs - v * δm * (1 + δs)| ≤
          |(z - s') + z * δs| + |v * δm * (1 + δs)| := by
          simpa only [abs_neg] using abs_add_le ((z - s') + z * δs) (-(v * δm * (1 + δs)))
      _ ≤ |z - s'| + |z * δs| + |v * δm * (1 + δs)| := by
          gcongr
          exact abs_add_le _ _
      _ = |z - s'| + |z| * |δs| + |v| * |δm| * |1 + δs| := by
          simp only [abs_mul]
  have hmain : (1 - u) * |r| ≤ (c + u) * W + u * (1 + u) * |v| := by
    have hleft : (1 - u) * |r| ≤ |r * (1 + δs)| := by
      rw [abs_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlow (abs_nonneg r)
    have h2 : |z| * |δs| ≤ W * u := by
      gcongr
    have h3 : |v| * |δm| * |1 + δs| ≤ |v| * u * (1 + u) := by
      gcongr
    nlinarith [he]
  have hWv : 0 ≤ W + |v| := add_nonneg hW (abs_nonneg _)
  have hfinal : (c + u) * W + u * (1 + u) * |v| ≤
      (1 - u) * d * (W + |v|) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hW,
      mul_nonneg (sub_nonneg.mpr hterm) (abs_nonneg v)]
  have huone : 0 < 1 - u := by linarith
  have : (1 - u) * |r| ≤ (1 - u) * (d * (W + |v|)) := by
    calc (1 - u) * |r| ≤ (c + u) * W + u * (1 + u) * |v| := hmain
      _ ≤ (1 - u) * d * (W + |v|) := hfinal
      _ = (1 - u) * (d * (W + |v|)) := by ring
  exact le_of_mul_le_mul_left this huone

private theorem p46_forward_add_step
    (u c d W acc S v acc' δm δa : ℝ)
    (hu : 0 ≤ u) (hW : 0 ≤ W)
    (hm : |δm| ≤ u) (ha : |δa| ≤ u)
    (hacc' : acc' = (acc + v * (1 + δm)) * (1 + δa))
    (hS : |S| ≤ W) (he : |acc - S| ≤ c * W)
    (hcoef : (1 + u) * c + u ≤ d)
    (hterm : u * (2 + u) ≤ d) :
    |acc' - (S + v)| ≤ d * (W + |v|) := by
  have hfactor : |1 + δa| ≤ 1 + u := by
    calc |1 + δa| ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left ha 1
  have hdelta : |δm + δa + δm * δa| ≤ u * (2 + u) := by
    calc
      |δm + δa + δm * δa| ≤ |δm + δa| + |δm * δa| := abs_add_le _ _
      _ ≤ |δm| + |δa| + |δm| * |δa| := by
        rw [abs_mul]
        gcongr
        exact abs_add_le _ _
      _ ≤ u * (2 + u) := by
        have hp : |δm| * |δa| ≤ u * u := by gcongr
        nlinarith
  have hid : acc' - (S + v) =
      (acc - S) * (1 + δa) + S * δa + v * (δm + δa + δm * δa) := by
    rw [hacc']
    ring
  have hcW : 0 ≤ c * W := le_trans (abs_nonneg _) he
  rw [hid]
  calc
    |(acc - S) * (1 + δa) + S * δa + v * (δm + δa + δm * δa)| ≤
        |acc - S| * |1 + δa| + |S| * |δa| +
          |v| * |δm + δa + δm * δa| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]
          exact le_trans (abs_add_le _ _) (by
            gcongr
            exact abs_add_le _ _)
    _ ≤ (c * W) * (1 + u) + W * u + |v| * (u * (2 + u)) := by
          gcongr
    _ ≤ d * (W + |v|) := by
          have h1 := mul_le_mul_of_nonneg_right hcoef hW
          have h2 := mul_le_mul_of_nonneg_right hterm (abs_nonneg v)
          nlinarith [h1, h2]

private noncomputable def p46SubFold (fp : P46TriFPModel) (k : ℕ)
    (a x : Fin k → ℝ) (s : ℝ) : ℝ :=
  Fin.foldl k (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) s

private noncomputable def p46AddMulFold (fp : P46FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (s : ℝ) : ℝ :=
  Fin.foldl k (fun acc i => fp.fl_add acc (fp.fl_mul (a i) (x i))) s

private theorem p46_add_fold_bound (fp : P46FPModel) (k t : ℕ)
    (a x : Fin k → ℝ) (acc S W : ℝ)
    (ht : 1 ≤ t) (hvalid : P46GammaValid fp.u (t + k))
    (hW : 0 ≤ W) (hS : |S| ≤ W)
    (hbase : |acc - S| ≤ p46Gamma fp.u t * W) :
    |p46AddMulFold fp k a x acc -
      (S + ∑ i : Fin k, a i * x i)| ≤
      p46Gamma fp.u (t + k) *
        (W + ∑ i : Fin k, |a i * x i|) := by
  induction k generalizing t acc S W with
  | zero =>
      simpa [p46AddMulFold] using hbase
  | succ k ih =>
      let acc' := fp.fl_add acc (fp.fl_mul (a 0) (x 0))
      let a' : Fin k → ℝ := fun i => a i.succ
      let x' : Fin k → ℝ := fun i => x i.succ
      let v := a 0 * x 0
      let S' := S + v
      let W' := W + |v|
      have hvalid' : P46GammaValid fp.u ((t + 1) + k) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvalid
      have hstep := p46_gamma_forward_step fp.u t fp.u_nonneg ht
        (p46_gamma_valid_mono fp.u (t + 1) (t + (k + 1)) fp.u_nonneg
          (by omega) hvalid)
      obtain ⟨δm, hm, hmul⟩ := fp.model_mul (a 0) (x 0)
      obtain ⟨δa, ha, hadd⟩ := fp.model_add acc (fp.fl_mul (a 0) (x 0))
      have hacc' : acc' = (acc + v * (1 + δm)) * (1 + δa) := by
        simp only [acc', v, hadd, hmul]
      have hW' : 0 ≤ W' := add_nonneg hW (abs_nonneg _)
      have hS' : |S'| ≤ W' := by
        calc |S + v| ≤ |S| + |v| := abs_add_le _ _
          _ ≤ W + |v| := by gcongr
      have hbase' : |acc' - S'| ≤ p46Gamma fp.u (t + 1) * W' :=
        p46_forward_add_step fp.u (p46Gamma fp.u t)
          (p46Gamma fp.u (t + 1)) W acc S v acc' δm δa
          fp.u_nonneg hW hm ha hacc' hS hbase hstep.1 hstep.2
      have hrec := ih (t + 1) a' x' acc' S' W' (by omega) hvalid' hW' hS' hbase'
      simpa only [p46AddMulFold, Fin.foldl_succ, Fin.sum_univ_succ,
        Nat.add_comm 1 k, add_assoc, acc', a', x', S', W', v] using hrec

private theorem p46_gamma_one_ge_u (u : ℝ)
    (hvalid : P46GammaValid u 1) : u ≤ p46Gamma u 1 := by
  have hden : 0 < 1 - u := by simpa [P46GammaValid] using hvalid
  unfold p46Gamma
  norm_num
  exact (le_div_iff₀ hden).2 (by nlinarith [sq_nonneg u])

private theorem p46_rounded_dot_bound (fp : P46FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P46GammaValid fp.u n) :
    |p46RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p46Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero =>
      simp [p46RoundedDotProduct]
  | succ k =>
      let a : Fin k → ℝ := fun i => x i.succ
      let b : Fin k → ℝ := fun i => y i.succ
      let v := x 0 * y 0
      let acc := fp.fl_mul (x 0) (y 0)
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      have hbaseu : |acc - v| ≤ fp.u * |v| := by
        simp only [acc, v, hmul]
        have heq : x 0 * y 0 * (1 + δ) - x 0 * y 0 = (x 0 * y 0) * δ := by ring
        rw [heq, abs_mul]
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hδ (abs_nonneg (x 0 * y 0))
      have hvalid1 := p46_gamma_valid_mono fp.u 1 (k + 1) fp.u_nonneg
        (by omega) hvalid
      have hbase : |acc - v| ≤ p46Gamma fp.u 1 * |v| :=
        le_trans hbaseu (mul_le_mul_of_nonneg_right
          (p46_gamma_one_ge_u fp.u hvalid1) (abs_nonneg _))
      have hfold := p46_add_fold_bound fp k 1 a b acc v |v|
        (by omega) (by simpa [Nat.add_comm] using hvalid)
        (abs_nonneg _) le_rfl hbase
      simpa only [p46RoundedDotProduct, p46AddMulFold,
        Fin.sum_univ_succ, Nat.add_comm 1 k, a, b, acc, v] using hfold

private theorem p46_gamma_size_coeff (u u_low : ℝ) (n : ℕ)
    (hu : 0 < u) (hlow : 0 ≤ u_low)
    (hvalid : P46GammaValid u n)
    (hsize : (n : ℝ) ≤ u_low / (u * (1 + 2 * u_low))) :
    p46Gamma u n + u_low * (1 + p46Gamma u n) ≤ 2 * u_low := by
  have hsizeDen : 0 < u * (1 + 2 * u_low) :=
    mul_pos hu (by linarith)
  have hprod : (n : ℝ) * u * (1 + 2 * u_low) ≤ u_low := by
    have h := (le_div_iff₀ hsizeDen).mp hsize
    nlinarith
  have hgammaDen : 0 < 1 - (n : ℝ) * u := by
    unfold P46GammaValid at hvalid
    linarith
  have hcoef : (1 + u_low) * p46Gamma u n ≤ u_low := by
    unfold p46Gamma
    rw [show (1 + u_low) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) =
      ((1 + u_low) * ((n : ℝ) * u)) / (1 - (n : ℝ) * u) by ring]
    apply (div_le_iff₀ hgammaDen).2
    nlinarith [hprod]
  nlinarith [hcoef]

private theorem p46_simulated_product_bound (fp : P46FPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (hu : 0 < fp.u) (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (i : Fin m) (j : Fin p) :
    |p46SimulatedMatMul fp A B i j - p46MatMul A B i j| ≤
      2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j := by
  let c := ∑ k : Fin n, A i k * B k j
  let h := p46RoundedDotProduct fp n (A i) (fun k => B k j)
  let W := ∑ k : Fin n, |A i k| * |B k j|
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hhigh : |h - c| ≤ p46Gamma fp.u n * W := by
    have hb := p46_rounded_dot_bound fp n (A i) (fun k => B k j) hvalid
    simpa only [c, h, W, abs_mul] using hb
  have hc : |c| ≤ W := by
    calc
      |c| ≤ ∑ k : Fin n, |A i k * B k j| := by
        simpa only [c] using
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun k : Fin n => A i k * B k j))
      _ = W := by simp only [W, abs_mul]
  have hh : |h| ≤ (1 + p46Gamma fp.u n) * W := by
    have htri : |h| ≤ |h - c| + |c| := by
      calc |h| = |(h - c) + c| := by congr 1; ring
        _ ≤ |h - c| + |c| := abs_add_le _ _
    nlinarith [htri, hhigh, hc]
  have hlow := fp.model_low h
  have htri : |fp.fl_low h - c| ≤ |fp.fl_low h - h| + |h - c| := by
    calc |fp.fl_low h - c| = |(fp.fl_low h - h) + (h - c)| := by congr 1; ring
      _ ≤ |fp.fl_low h - h| + |h - c| := abs_add_le _ _
  have hcoef := p46_gamma_size_coeff fp.u fp.u_low n hu fp.u_low_nonneg hvalid hsize
  have hcoefW := mul_le_mul_of_nonneg_right hcoef hW
  change |fp.fl_low h - c| ≤ 2 * fp.u_low * W
  calc
    _ ≤ |fp.fl_low h - h| + |h - c| := htri
    _ ≤ fp.u_low * |h| + p46Gamma fp.u n * W := add_le_add hlow hhigh
    _ ≤ fp.u_low * ((1 + p46Gamma fp.u n) * W) + p46Gamma fp.u n * W := by
      gcongr
      exact fp.u_low_nonneg
    _ ≤ 2 * fp.u_low * W := by nlinarith [hcoefW]

private theorem p46_sub_fold_bound (fp : P46TriFPModel) (k t : ℕ)
    (a x : Fin k → ℝ) (s z : ℝ)
    (ht : 1 ≤ t) (hvalid : P46GammaValid fp.u (t + k))
    (hbase : |z - p46SubFold fp k a x s| ≤
      p46Gamma fp.u t * |z|) :
    |z + ∑ i : Fin k, a i * x i - s| ≤
      p46Gamma fp.u (t + k) *
        (|z| + ∑ i : Fin k, |a i * x i|) := by
  induction k generalizing t s z with
  | zero =>
      simpa [p46SubFold] using hbase
  | succ k ih =>
      let s' := fp.fl_sub s (fp.fl_mul (a 0) (x 0))
      let a' : Fin k → ℝ := fun i => a i.succ
      let x' : Fin k → ℝ := fun i => x i.succ
      have hvalid' : P46GammaValid fp.u (t + k) :=
        p46_gamma_valid_mono fp.u _ _ fp.u_nonneg (by omega) hvalid
      have hbase' : |z - p46SubFold fp k a' x' s'| ≤
          p46Gamma fp.u t * |z| := by
        simpa [p46SubFold, Fin.foldl_succ, s', a', x'] using hbase
      have hrec := ih t a' x' s' z ht hvalid' hbase'
      obtain ⟨δm, hm, hmul⟩ := fp.model_mul (a 0) (x 0)
      obtain ⟨δs, hs, hsub⟩ := fp.model_sub s (fp.fl_mul (a 0) (x 0))
      have hs' : s' = (s - (a 0 * x 0) * (1 + δm)) * (1 + δs) := by
        simp only [s', hsub, hmul]
      let v := a 0 * x 0
      let W := |z| + ∑ i : Fin k, |a' i * x' i|
      let z' := z + ∑ i : Fin k, a' i * x' i
      have hW : 0 ≤ W := by
        dsimp [W]
        positivity
      have hz' : |z'| ≤ W := by
        dsimp [z', W]
        calc
          |z + ∑ i : Fin k, a' i * x' i| ≤
              |z| + |∑ i : Fin k, a' i * x' i| := abs_add_le _ _
          _ ≤ |z| + ∑ i : Fin k, |a' i * x' i| := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
      have hrec' : |z' - s'| ≤ p46Gamma fp.u (t + k) * W := by
        simpa [z', W] using hrec
      have hstep := p46_gamma_step fp.u (t + k) fp.u_nonneg (by omega)
        (by simpa [Nat.add_assoc] using hvalid)
      have hu1 : fp.u < 1 := by
        have hpos : 1 ≤ t + (k + 1) := by omega
        have h := p46_gamma_valid_mono fp.u 1 (t + (k + 1)) fp.u_nonneg hpos hvalid
        simpa [P46GammaValid] using h
      have hres := p46_reverse_sub_step fp.u
        (p46Gamma fp.u (t + k)) (p46Gamma fp.u (t + (k + 1)))
        W z' s v s' δm δs fp.u_nonneg hu1 hW hm hs hs' hz' hrec'
        (by simpa [Nat.add_assoc] using hstep.1)
        (by simpa [Nat.add_assoc] using hstep.2)
      simpa only [Fin.sum_univ_succ, Nat.add_assoc, add_assoc, add_left_comm,
        add_comm, v, W, z', a', x'] using hres

private theorem p46_div_base (fp : P46TriFPModel) (s d : ℝ)
    (hd : d ≠ 0) (hu1 : fp.u < 1) :
    let x := fp.fl_div s d
    |d * x - s| ≤ p46Gamma fp.u 1 * |d * x| := by
  dsimp
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s d hd
  have hdx : d * fp.fl_div s d = s * (1 + δ) := by
    rw [hdiv]
    field_simp
  have he : |d * fp.fl_div s d - s| ≤ fp.u * |s| := by
    rw [hdx]
    have heq : s * (1 + δ) - s = s * δ := by ring
    rw [heq, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg s)
  have hs : |s| ≤ |d * fp.fl_div s d| + |d * fp.fl_div s d - s| := by
    calc
      |s| = |d * fp.fl_div s d + -(d * fp.fl_div s d - s)| := by congr 1; ring
      _ ≤ |d * fp.fl_div s d| + |d * fp.fl_div s d - s| := by
        simpa only [abs_neg] using abs_add_le (d * fp.fl_div s d)
          (-(d * fp.fl_div s d - s))
  have hu := fp.u_nonneg
  have hmain : (1 - fp.u) * |d * fp.fl_div s d - s| ≤
      fp.u * |d * fp.fl_div s d| := by
    nlinarith [mul_le_mul_of_nonneg_left hs hu]
  have hden : 0 < 1 - fp.u := by linarith
  have hquot : |d * fp.fl_div s d - s| ≤
      fp.u * |d * fp.fl_div s d| / (1 - fp.u) := by
    exact (le_div_iff₀ hden).2 (by nlinarith [hmain])
  simpa [p46Gamma, div_mul_eq_mul_div] using hquot

private theorem p46_sum_upper_row (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, j.val < i.val → f j = 0) :
    ∑ j : Fin n, f j = f i +
      ∑ t : Fin (n - i.val - 1),
        f ⟨i.val + 1 + t.val, by omega⟩ := by
  have hn : n = i.val + 1 + (n - i.val - 1) := by omega
  let g : ℕ → ℝ := fun k => if hk : k < n then f ⟨k, hk⟩ else 0
  have hsum : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, g k := by
    simpa [g] using (Finset.sum_fin_eq_sum_range f)
  have hlow : (∑ k ∈ Finset.range i.val, g k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k < i.val := Finset.mem_range.mp hk
    have hkn : k < n := lt_trans hki i.isLt
    simp [g, hkn, hzero ⟨k, hkn⟩ hki]
  have htail : (∑ k ∈ Finset.range (n - i.val - 1), g (i.val + 1 + k)) =
      ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hkr : k < n - i.val - 1 := Finset.mem_range.mp hk
    have hkn : i.val + 1 + k < n := by omega
    simp [g, hkr, hkn]
  rw [hsum]
  conv_lhs => rw [hn]
  rw [Finset.sum_range_add, Finset.sum_range_succ, hlow, zero_add, htail]
  simp [g, i.isLt]

private theorem p46_local_row_bound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hd : U i i ≠ 0) (hvalid : P46GammaValid fp.u n) :
    let q := n - i.val - 1
    let a : Fin q → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
    let y : Fin q → ℝ := fun t => x ⟨i.val + 1 + t.val, by omega⟩
    let s := p46SubFold fp q a y (b i)
    |U i i * fp.fl_div s (U i i) + ∑ t : Fin q, a t * y t - b i| ≤
      p46Gamma fp.u n *
        (|U i i * fp.fl_div s (U i i)| + ∑ t : Fin q, |a t * y t|) := by
  dsimp only
  let q := n - i.val - 1
  let a : Fin q → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
  let y : Fin q → ℝ := fun t => x ⟨i.val + 1 + t.val, by omega⟩
  let s := p46SubFold fp q a y (b i)
  have hq : 1 + q ≤ n := by dsimp [q]; omega
  have hvalidq := p46_gamma_valid_mono fp.u (1 + q) n fp.u_nonneg hq hvalid
  have hvalid1 := p46_gamma_valid_mono fp.u 1 n fp.u_nonneg (by omega) hvalid
  have hu1 : fp.u < 1 := by simpa [P46GammaValid] using hvalid1
  have hbase : |U i i * fp.fl_div s (U i i) - p46SubFold fp q a y (b i)| ≤
      p46Gamma fp.u 1 * |U i i * fp.fl_div s (U i i)| := by
    simpa [s] using p46_div_base fp s (U i i) hd hu1
  have hfold := p46_sub_fold_bound fp q 1 a y (b i)
    (U i i * fp.fl_div s (U i i)) (by omega) hvalidq hbase
  have hgamma := p46_gamma_mono fp.u (1 + q) n fp.u_nonneg hq hvalid
  have hw : 0 ≤ |U i i * fp.fl_div s (U i i)| +
      ∑ t : Fin q, |a t * y t| := by positivity
  have hfinal := le_trans hfold (mul_le_mul_of_nonneg_right hgamma hw)
  simpa only [Nat.add_comm, a, y, q, s] using hfinal

private theorem p46_steps_preserve (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) (j : Fin n) (hj : k ≤ j.val) :
    p46BackSubSteps fp n U b k hk x j = x j := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      let ik : Fin n := ⟨k, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      change p46BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' j = x j
      rw [ih (Nat.le_of_succ_le hk) x' (by omega)]
      have hne : j ≠ ik := by intro h; have := congrArg Fin.val h; dsimp [ik] at this; omega
      simp [x', hne]

private theorem p46_upper_row_congr (n : ℕ) (U : P46Matrix n n)
    (i : Fin n) (hupper : ∀ j : Fin n, j.val < i.val → U i j = 0)
    (x y : Fin n → ℝ) (hxy : ∀ j : Fin n, i.val ≤ j.val → x j = y j) :
    (∑ j : Fin n, U i j * x j) = (∑ j : Fin n, U i j * y j) ∧
    (∑ j : Fin n, |U i j| * |x j|) = (∑ j : Fin n, |U i j| * |y j|) := by
  constructor <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    by_cases hj : j.val < i.val
  · simp [hupper j hj]
  · simp [hxy j (by omega)]
  · simp [hupper j hj]
  · simp [hxy j (by omega)]

private theorem p46_updated_row_bound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hd : U i i ≠ 0) (hupper : ∀ j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P46GammaValid fp.u n) :
    let q := n - i.val - 1
    let s := Fin.foldl q
      (fun acc (t : Fin q) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩)))
      (b i)
    let x' := Function.update x i (fp.fl_div s (U i i))
    |(∑ j : Fin n, U i j * x' j) - b i| ≤
      p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |x' j| := by
  dsimp only
  let q := n - i.val - 1
  let a : Fin q → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
  let y : Fin q → ℝ := fun t => x ⟨i.val + 1 + t.val, by omega⟩
  let s := p46SubFold fp q a y (b i)
  let x' : Fin n → ℝ := Function.update x i (fp.fl_div s (U i i))
  have htail (t : Fin q) : x' ⟨i.val + 1 + t.val, by omega⟩ = y t := by
    have hne : (⟨i.val + 1 + t.val, by omega⟩ : Fin n) ≠ i := by
      intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    simp [x', y, hne]
  have hdiag : x' i = fp.fl_div s (U i i) := by simp [x']
  have hsum : (∑ j : Fin n, U i j * x' j) =
      U i i * fp.fl_div s (U i i) + ∑ t : Fin q, a t * y t := by
    rw [p46_sum_upper_row n i (fun j => U i j * x' j)
      (by intro j hj; simp [hupper j hj])]
    rw [hdiag]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp only [a, htail, y]
  have hweight : (∑ j : Fin n, |U i j| * |x' j|) =
      |U i i * fp.fl_div s (U i i)| + ∑ t : Fin q, |a t * y t| := by
    rw [p46_sum_upper_row n i (fun j => |U i j| * |x' j|)
      (by intro j hj; simp [hupper j hj])]
    rw [hdiag, abs_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    simp only [a, htail, y, abs_mul]
  have hloc := p46_local_row_bound fp n U b x i hd hvalid
  change |(∑ j : Fin n, U i j * x' j) - b i| ≤
    p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |x' j|
  rw [hsum, hweight]
  simpa only [p46SubFold, a, y, q, s] using hloc

private theorem p46_steps_rows_bound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P46GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    ∀ i : Fin n, i.val < k →
      |(∑ j : Fin n, U i j * p46BackSubSteps fp n U b k hk x j) - b i| ≤
        p46Gamma fp.u n *
          ∑ j : Fin n, |U i j| * |p46BackSubSteps fp n U b k hk x j| := by
  induction k generalizing x with
  | zero =>
      intro i hi
      omega
  | succ k ih =>
      let ik : Fin n := ⟨k, by omega⟩
      let q := n - k - 1
      let s := Fin.foldl q
        (fun acc (t : Fin q) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      let y := p46BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      intro i hi
      change |(∑ j : Fin n, U i j * y j) - b i| ≤
        p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |y j|
      by_cases hik : i.val < k
      · exact ih (Nat.le_of_succ_le hk) x' i hik
      · have hieq : i = ik := Fin.ext (by dsimp [ik]; omega)
        subst i
        have hloc := p46_updated_row_bound fp n U b x ik
          (hdiag ik) (hupper ik) hvalid
        have hxy : ∀ j : Fin n, ik.val ≤ j.val → x' j = y j := by
          intro j hj
          dsimp [y]
          exact (p46_steps_preserve fp n U b k (Nat.le_of_succ_le hk) x' j
            (by simpa [ik] using hj)).symm
        have hcongr := p46_upper_row_congr n U ik (hupper ik) x' y hxy
        rw [← hcongr.1, ← hcongr.2]
        simpa only [ik, q, s, x'] using hloc

private theorem p46_simulated_solve_bound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P46GammaValid fp.u n) (i : Fin n) :
    |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
      (p46Gamma fp.u n + fp.u_low) *
        ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j| := by
  let x := p46BackSub fp n U b
  let W := ∑ j : Fin n, |U i j| * |x j|
  have hhigh : |(∑ j : Fin n, U i j * x j) - b i| ≤ p46Gamma fp.u n * W := by
    simpa [x, W, p46BackSub] using
      p46_steps_rows_bound fp n U b hdiag hupper hvalid n (le_refl n)
        (fun _ => 0) i i.isLt
  have hround : |(∑ j : Fin n, U i j * fp.fl_low (x j)) -
      (∑ j : Fin n, U i j * x j)| ≤ fp.u_low * W := by
    have heq : (∑ j : Fin n, U i j * fp.fl_low (x j)) -
        (∑ j : Fin n, U i j * x j) =
        ∑ j : Fin n, U i j * (fp.fl_low (x j) - x j) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext j
      ring
    rw [heq]
    calc
      |∑ j : Fin n, U i j * (fp.fl_low (x j) - x j)| ≤
          ∑ j : Fin n, |U i j * (fp.fl_low (x j) - x j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, fp.u_low * (|U i j| * |x j|) := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          calc
            |U i j| * |fp.fl_low (x j) - x j| ≤
                |U i j| * (fp.u_low * |x j|) :=
                  mul_le_mul_of_nonneg_left (fp.model_low (x j)) (abs_nonneg _)
            _ = fp.u_low * (|U i j| * |x j|) := by ring
      _ = fp.u_low * W := by simp [W, Finset.mul_sum]
  have htri : |(∑ j : Fin n, U i j * fp.fl_low (x j)) - b i| ≤
      |(∑ j : Fin n, U i j * fp.fl_low (x j)) -
        (∑ j : Fin n, U i j * x j)| +
      |(∑ j : Fin n, U i j * x j) - b i| := by
    have heq : (∑ j : Fin n, U i j * fp.fl_low (x j)) - b i =
        ((∑ j : Fin n, U i j * fp.fl_low (x j)) -
          (∑ j : Fin n, U i j * x j)) +
        ((∑ j : Fin n, U i j * x j) - b i) := by ring
    rw [heq]
    exact abs_add_le _ _
  change |(∑ j : Fin n, U i j * fp.fl_low (x j)) - b i| ≤
    (p46Gamma fp.u n + fp.u_low) * W
  calc
    _ ≤ _ := htri
    _ ≤ fp.u_low * W + p46Gamma fp.u n * W := add_le_add hround hhigh
    _ = (p46Gamma fp.u n + fp.u_low) * W := by ring

/-- Section 3.2: high-precision kernels rounded once to low precision. -/
theorem p46_c3_simulated_product_and_triangular_solve
    (fp : P46TriFPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hu : 0 < fp.u)
    (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    (∀ i j,
      |p46SimulatedMatMul fp.toP46FPModel A B i j - p46MatMul A B i j| ≤
        2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j) ∧
    (∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j|) := by
  -- PROOF_START P46-C3-H001
  constructor
  · intro i j
    exact p46_simulated_product_bound fp.toP46FPModel m n p A B
      hu hvalid hsize i j
  · intro i
    exact p46_simulated_solve_bound fp n U b hUdiag hUupper hvalid i

end VSCLReuse

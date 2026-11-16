import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p07_scalar_step
    (u q A a B b δ : ℝ)
    (hu : 0 ≤ u) (hq : 1 + u ≤ q)
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hB : |B - A| ≤ (q - 1) * A)
    (hb : |b - a| ≤ u * a)
    (hδ : |δ| ≤ u) :
    |(B + b) * (1 + δ) - (A + a)| ≤
      (q * (1 + u) - 1) * (A + a) := by
  have hsum : |B + b| ≤ q * A + (1 + u) * a := by
    calc
      |B + b| = |(B - A) + (b - a) + (A + a)| := by congr 1; ring
      _ ≤ |B - A| + |b - a| + |A + a| := by
        simpa [add_assoc] using (abs_add_three (B - A) (b - a) (A + a))
      _ ≤ q * A + (1 + u) * a := by
        rw [abs_of_nonneg (add_nonneg hA ha)]
        nlinarith
  have hqnonneg : 0 ≤ q := by linarith
  have hqA : 0 ≤ q * A + (1 + u) * a := by positivity
  have hmul : |B + b| * |δ| ≤ (q * A + (1 + u) * a) * u := by
    exact mul_le_mul hsum hδ (abs_nonneg _) hqA
  have htri : |(B + b) * (1 + δ) - (A + a)| ≤
      |B - A| + |b - a| + |B + b| * |δ| := by
    calc
      |(B + b) * (1 + δ) - (A + a)| =
          |(B - A) + (b - a) + (B + b) * δ| := by congr 1; ring
      _ ≤ |B - A| + |b - a| + |(B + b) * δ| := by
        simpa [add_assoc] using (abs_add_three (B - A) (b - a) ((B + b) * δ))
      _ = _ := by rw [abs_mul]
  have hcoeff : (1 + u) ^ 2 ≤ q * (1 + u) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by positivity : 0 ≤ 1 + u)]
  nlinarith

private theorem p07_recursive_error
    (n : ℕ) : ∀ (a b : Fin n → ℝ) (fp : StandardAddModel),
    fp.u ≤ 1 → (∀ i, 0 ≤ a i) →
    (∀ i, |b i - a i| ≤ fp.u * a i) →
    |recursiveSum fp.fl_add n b - ∑ i, a i| ≤
      ((1 + fp.u) ^ n - 1) * ∑ i, a i := by
  induction n with
  | zero =>
      intro a b fp hu ha hb
      simp [recursiveSum]
  | succ n ih =>
      intro a b fp hu ha hb
      by_cases hn : n = 0
      · subst n
        have h0 : fp.fl_add 0 (b 0) = b 0 := fp.fl_add_zero (b 0)
        simpa [recursiveSum, Fin.sum_univ_one, fp.fl_add_zero] using hb 0
      · let A : ℝ := ∑ i : Fin n, a i.castSucc
        let B : ℝ := recursiveSum fp.fl_add n (fun i => b i.castSucc)
        have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i.castSucc
        have hprev : |B - A| ≤ ((1 + fp.u) ^ n - 1) * A :=
          ih (fun i => a i.castSucc) (fun i => b i.castSucc) fp hu
            (fun i => ha i.castSucc) (fun i => hb i.castSucc)
        have hq : 1 + fp.u ≤ (1 + fp.u) ^ n := by
          simpa using (pow_le_pow_right₀ (by linarith [fp.u_nonneg] : 1 ≤ 1 + fp.u)
            (show 1 ≤ n by omega))
        obtain ⟨δ, hδ, heq⟩ := fp.model_add B (b (Fin.last n))
        calc
          |recursiveSum fp.fl_add (n + 1) b - ∑ i, a i| =
              |fp.fl_add B (b (Fin.last n)) - (A + a (Fin.last n))| := by
                simp [recursiveSum, hn, A, B, Fin.sum_univ_castSucc]
          _ = |(B + b (Fin.last n)) * (1 + δ) - (A + a (Fin.last n))| := by
              rw [heq]
          _ ≤ (((1 + fp.u) ^ n) * (1 + fp.u) - 1) *
                (A + a (Fin.last n)) :=
              p07_scalar_step fp.u ((1 + fp.u) ^ n) A (a (Fin.last n))
                B (b (Fin.last n)) δ fp.u_nonneg hq hA
                (ha (Fin.last n)) hprev (hb (Fin.last n)) hδ
          _ = ((1 + fp.u) ^ (n + 1) - 1) * ∑ i, a i := by
              rw [pow_succ, Fin.sum_univ_castSucc]

private def p07_coeff : ℕ → ℝ
  | 0 => 0
  | n + 1 => 2 * p07_coeff n + n

private theorem p07_coeff_nonneg (n : ℕ) : 0 ≤ p07_coeff n := by
  induction n with
  | zero => simp [p07_coeff]
  | succ n ih =>
      simp only [p07_coeff]
      positivity

private theorem p07_pow_bound (n : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ n - 1 ≤ (n : ℝ) * u + p07_coeff n * u ^ 2 := by
  induction n with
  | zero => simp [p07_coeff]
  | succ n ih =>
      have hc := p07_coeff_nonneg n
      have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1 + u)
      have hu3 : u ^ 3 ≤ u ^ 2 := by nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
      simp only [pow_succ, p07_coeff, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hu1)]

private theorem p07_sum_error_bound {n : ℕ} (x : Fin n → ℝ) (u : ℝ)
    (run : P07BasicSumExecution x u) (hu : u ≤ 1) :
    |p07RecursiveComputedExpSum run - p07ExpSum x| ≤
      ((n : ℝ) * u + p07_coeff n * u ^ 2) * p07ExpSum x := by
  have hu0 : 0 ≤ u := run.unit_eq ▸ run.fp.u_nonneg
  have hpoint (i : Fin n) :
      |p07ComputedExp run i - Real.exp (x i)| ≤
        run.fp.u * Real.exp (x i) := by
    calc
      |p07ComputedExp run i - Real.exp (x i)| =
          Real.exp (x i) * |run.expError i| := by
            rw [p07ComputedExp]
            calc
              |Real.exp (x i) * (1 + run.expError i) - Real.exp (x i)| =
                  |Real.exp (x i) * run.expError i| := by congr 1; ring
              _ = _ := by rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ Real.exp (x i) * u :=
        mul_le_mul_of_nonneg_left (run.expError_le i) (Real.exp_nonneg _)
      _ = run.fp.u * Real.exp (x i) := by rw [run.unit_eq]; ring
  have hrecursive := p07_recursive_error n (fun i => Real.exp (x i))
    (p07ComputedExp run) run.fp (by simpa [run.unit_eq] using hu)
    (fun i => Real.exp_nonneg (x i)) hpoint
  have hpow := p07_pow_bound n u hu0 hu
  have hs : 0 ≤ p07ExpSum x := by
    exact Finset.sum_nonneg (fun i _ => Real.exp_nonneg (x i))
  have hmul := mul_le_mul_of_nonneg_right hpow hs
  have hrecursive' :
      |p07RecursiveComputedExpSum run - p07ExpSum x| ≤
        ((1 + u) ^ n - 1) * p07ExpSum x := by
    simpa only [p07RecursiveComputedExpSum, p07ExpSum, run.unit_eq] using hrecursive
  exact hrecursive'.trans hmul

private theorem p07_softmax_scalar
    (a u S T E e d : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsmall : a * u ≤ 1 / 2)
    (hS : 0 < S) (hE : 0 ≤ E)
    (hsum : |T - S| ≤ a * u * S)
    (he : |e| ≤ u) (hd : |d| ≤ u) :
    |E * (1 + e) / T * (1 + d) - E / S| ≤
      (E / S) *
        ((a + 2) * u + (2 * (1 + a * (a + 2))) * u ^ 2) := by
  let R : ℝ := (a + 2) * u + (2 * (1 + a * (a + 2))) * u ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hTlower : (1 - a * u) * S ≤ T := by
    have := (abs_le.mp hsum).1
    nlinarith
  have hT : 0 < T := by
    have hden : 0 < 1 - a * u := by linarith
    exact lt_of_lt_of_le (mul_pos hden hS) hTlower
  have hprod : |(1 + e) * (1 + d) - 1| ≤ 2 * u + u ^ 2 := by
    have hmul : |e| * |d| ≤ u * u :=
      mul_le_mul he hd (abs_nonneg _) hu
    calc
      |(1 + e) * (1 + d) - 1| = |e + d + e * d| := by congr 1; ring
      _ ≤ |e| + |d| + |e * d| := by
        simpa using (abs_add_three e d (e * d))
      _ ≤ 2 * u + u ^ 2 := by
        rw [abs_mul]
        nlinarith
  have hnum : |S * ((1 + e) * (1 + d)) - T| ≤
      ((a + 2) * u + u ^ 2) * S := by
    calc
      |S * ((1 + e) * (1 + d)) - T| =
          |S * (((1 + e) * (1 + d)) - 1) - (T - S)| := by congr 1; ring
      _ ≤ |S * (((1 + e) * (1 + d)) - 1)| + |T - S| := by
        rw [sub_eq_add_neg]
        simpa only [abs_neg] using
          (abs_add_le (S * (((1 + e) * (1 + d)) - 1)) (-(T - S)))
      _ ≤ (2 * u + u ^ 2) * S + a * u * S := by
        rw [abs_mul, abs_of_pos hS]
        convert add_le_add (mul_le_mul_of_nonneg_right hprod hS.le) hsum using 1
        ring
      _ = _ := by ring
  have hcoeff : (a + 2) * u + u ^ 2 ≤ R * (1 - a * u) := by
    have hfactor : 0 ≤ (1 + a * (a + 2)) * u ^ 2 * (1 - 2 * a * u) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (sq_nonneg u)
      · linarith
    dsimp [R]
    nlinarith
  have hfrac : |S * ((1 + e) * (1 + d)) - T| / T ≤ R := by
    apply (div_le_iff₀ hT).2
    calc
      |S * ((1 + e) * (1 + d)) - T| ≤ ((a + 2) * u + u ^ 2) * S := hnum
      _ ≤ (R * (1 - a * u)) * S :=
        mul_le_mul_of_nonneg_right hcoeff hS.le
      _ ≤ R * T := by
        calc
          (R * (1 - a * u)) * S = R * ((1 - a * u) * S) := by ring
          _ ≤ R * T := mul_le_mul_of_nonneg_left hTlower hR
  have hEdiv : 0 ≤ E / S := div_nonneg hE hS.le
  have hid : E * (1 + e) / T * (1 + d) - E / S =
      (E / S) * ((S * ((1 + e) * (1 + d)) - T) / T) := by
    field_simp
  rw [hid]
  calc
    |(E / S) * ((S * ((1 + e) * (1 + d)) - T) / T)| =
        (E / S) * (|S * ((1 + e) * (1 + d)) - T| / T) := by
          rw [abs_mul, abs_of_nonneg hEdiv, abs_div, abs_of_pos hT]
    _ ≤ (E / S) * R := mul_le_mul_of_nonneg_left hfrac hEdiv
    _ = _ := rfl

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
  let a : ℝ := (n : ℝ) + 1
  let K : ℝ := 2 * (1 + a * (a + 2))
  refine ⟨fun t => K * (u t) ^ 2, ?_, ?_⟩
  · have hK : 0 ≤ K := by
      dsimp [K, a]
      positivity
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨K, Filter.Eventually.of_forall (fun t => ?_)⟩
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (sq_nonneg (u t))]
    exact le_rfl
  · have ha : 0 ≤ a := by dsimp [a]; positivity
    have hC : 0 ≤ p07_coeff n := p07_coeff_nonneg n
    have hM : 0 < 2 * ((n : ℝ) + p07_coeff n + 2) := by positivity
    have hev : ∀ᶠ t in l,
        u t < 1 / (2 * ((n : ℝ) + p07_coeff n + 2)) :=
      hu.eventually_lt_const (by positivity)
    filter_upwards [hev] with t ht
    have hu0 : 0 ≤ u t := (run t).unit_eq ▸ (run t).fp.u_nonneg
    have hprod : u t * (2 * ((n : ℝ) + p07_coeff n + 2)) < 1 :=
      (lt_div_iff₀ hM).mp ht
    have hu1 : u t ≤ 1 := by nlinarith [mul_nonneg hC hu0]
    have hCu : p07_coeff n * u t ≤ 1 := by nlinarith
    have hsmall : a * u t ≤ 1 / 2 := by
      dsimp [a]
      nlinarith [mul_nonneg hC hu0]
    have hS : 0 < p07ExpSum x := by
      unfold p07ExpSum
      exact Finset.sum_pos (fun i _ => Real.exp_pos (x i))
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hsum :
        |p07RecursiveComputedExpSum (run t) - p07ExpSum x| ≤
          a * u t * p07ExpSum x := by
      have hraw := p07_sum_error_bound x (u t) (run t) hu1
      have hcoeff : (n : ℝ) * u t + p07_coeff n * (u t) ^ 2 ≤ a * u t := by
        have := mul_nonneg (by linarith : 0 ≤ 1 - p07_coeff n * u t) hu0
        dsimp [a]
        nlinarith
      exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff hS.le)
    let g : Fin n → ℝ := fun i => p07ExactSoftmax x i
    let gh : Fin n → ℝ := fun i => p07ComputedSoftmax (run t) (divError t) i
    let R : ℝ := a * u t + 2 * u t + K * (u t) ^ 2
    have hR : 0 ≤ R := by dsimp [R, K]; positivity
    have hpoint (i : Fin n) : |gh i - g i| ≤ g i * R := by
      have h := p07_softmax_scalar a (u t) (p07ExpSum x)
        (p07RecursiveComputedExpSum (run t)) (Real.exp (x i))
        ((run t).expError i) (divError t i) ha hu0 hsmall hS
        (Real.exp_nonneg _) hsum ((run t).expError_le i) (hdiv t i)
      simpa [g, gh, R, K, p07ComputedSoftmax, p07ComputedExp,
        p07ExactSoftmax, mul_add, add_mul] using h
    have hgpos (i : Fin n) : 0 < g i := by
      dsimp [g, p07ExactSoftmax]
      exact div_pos (Real.exp_pos _) hS
    have hgnorm : 0 < ‖g‖ := by
      have hi := norm_le_pi_norm g (⟨0, hn⟩ : Fin n)
      have hipos : 0 < ‖g (⟨0, hn⟩ : Fin n)‖ := norm_pos_iff.mpr (ne_of_gt (hgpos _))
      exact lt_of_lt_of_le hipos hi
    have hnorm : ‖gh - g‖ ≤ ‖g‖ * R := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) hR)).2
      intro i
      have hi := hpoint i
      calc
        ‖(gh - g) i‖ = |gh i - g i| := by simp [Real.norm_eq_abs]
        _ ≤ g i * R := hi
        _ = ‖g i‖ * R := by rw [Real.norm_eq_abs, abs_of_pos (hgpos i)]
        _ ≤ ‖g‖ * R :=
          mul_le_mul_of_nonneg_right (norm_le_pi_norm g i) hR
    have hratio : ‖gh - g‖ / ‖g‖ ≤ R :=
      (div_le_iff₀ hgnorm).2 (by nlinarith [hnorm])
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hright : R = (n + 3 : ℝ) * u t + |K * (u t) ^ 2| := by
      rw [abs_mul, abs_of_nonneg hK, abs_of_nonneg (sq_nonneg _)]
      dsimp [R, a]
      ring
    change ‖gh - g‖ / ‖g‖ ≤ (n + 3 : ℝ) * u t + |K * (u t) ^ 2|
    rw [← hright]
    exact hratio

end VSCLReuse

import VSCLReuse.P52.Definitions

namespace VSCLReuse

open scoped BigOperators
open SignType

set_option maxHeartbeats 1000000

private theorem p52_fold_error (fp : P52FPModel) (n : ℕ)
    (v : Fin n → ℝ) (x : ℝ) :
    |Fin.foldl n (fun acc i => fp.fl_add acc (v i)) x -
        (x + ∑ i : Fin n, v i)| ≤
      ((1 + fp.u) ^ n - 1) * (|x| + ∑ i : Fin n, |v i|) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    let y := v 0
    let z := fp.fl_add x y
    let w : Fin n → ℝ := fun i => v i.succ
    obtain ⟨δ, hδ, hz⟩ := fp.model_add x y
    have hu : 0 ≤ fp.u := fp.u_nonneg
    have ht : 1 ≤ 1 + fp.u := by linarith
    have hpow : 1 ≤ (1 + fp.u) ^ n := one_le_pow₀ ht
    have hP : 0 ≤ |x| + |y| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hT : 0 ≤ ∑ i : Fin n, |w i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have he : |z - (x + y)| ≤ fp.u * (|x| + |y|) := by
      dsimp [z]
      rw [hz]
      have hmul : |(x + y) * δ| ≤ (|x| + |y|) * fp.u := by
        rw [abs_mul]
        exact mul_le_mul (abs_add_le _ _) hδ (abs_nonneg _) hP
      convert hmul using 1 <;> ring
    have hzabs : |z| ≤ (1 + fp.u) * (|x| + |y|) := by
      dsimp [z]
      rw [hz, abs_mul]
      have hd : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hm := mul_le_mul (abs_add_le x y) hd (abs_nonneg (1 + δ)) hP
      nlinarith
    have hi := ih w z
    have hle : |z| + ∑ i : Fin n, |w i| ≤
        (1 + fp.u) * (|x| + |y|) + ∑ i : Fin n, |w i| := by linarith
    have hmul := mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ (1 + fp.u) ^ n - 1)
    have htri : |Fin.foldl n (fun acc i => fp.fl_add acc (w i)) z -
        ((x + y) + ∑ i : Fin n, w i)| ≤
        |Fin.foldl n (fun acc i => fp.fl_add acc (w i)) z -
          (z + ∑ i : Fin n, w i)| + |z - (x + y)| := by
      convert abs_add_le
        (Fin.foldl n (fun acc i => fp.fl_add acc (w i)) z -
          (z + ∑ i : Fin n, w i)) (z - (x + y)) using 1 <;> ring
    have hfinal :
        |Fin.foldl n (fun acc i => fp.fl_add acc (w i)) z -
          ((x + y) + ∑ i : Fin n, w i)| ≤
        ((1 + fp.u) ^ (n + 1) - 1) *
          (|x| + |y| + ∑ i : Fin n, |w i|) := by
      calc
        _ ≤ |Fin.foldl n (fun acc i => fp.fl_add acc (w i)) z -
              (z + ∑ i : Fin n, w i)| + |z - (x + y)| := htri
        _ ≤ ((1 + fp.u) ^ n - 1) *
              ((1 + fp.u) * (|x| + |y|) + ∑ i : Fin n, |w i|) +
              fp.u * (|x| + |y|) := by linarith
        _ ≤ _ := by
          rw [pow_succ]
          nlinarith [mul_nonneg hu hT]
    simpa [Fin.foldl_succ, Fin.sum_univ_succ, y, z, w, add_assoc] using hfinal

private theorem p52_sum_error (fp : P52FPModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : 0 < n) :
    |p52RecursiveSum fp n v - ∑ i : Fin n, v i| ≤
      ((1 + fp.u) ^ (n - 1) - 1) * (∑ i : Fin n, |v i|) := by
  cases n with
  | zero => omega
  | succ n =>
    have h := p52_fold_error fp n (fun i : Fin n => v i.succ) (v 0)
    simpa [p52RecursiveSum, Fin.foldl_succ, fp.fl_add_zero,
      Fin.sum_univ_succ, Nat.succ_eq_add_one, add_assoc] using h

private theorem p52_dot_eq_sum (fp : P52FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    p52RoundedDotProduct fp n x y =
      p52RecursiveSum fp n (fun i => fp.fl_mul (x i) (y i)) := by
  cases n with
  | zero => simp [p52RoundedDotProduct, p52RecursiveSum]
  | succ n =>
    simp [p52RoundedDotProduct, p52RecursiveSum, Fin.foldl_succ,
      fp.fl_add_zero]

private theorem p52_perturbed_sum_error (fp : P52FPModel) (n : ℕ)
    (v w : Fin n → ℝ) (hn : 0 < n) (e : ℝ) (he : 0 ≤ e)
    (hv : ∀ i, |v i - w i| ≤ e * |w i|) :
    |p52RecursiveSum fp n v - ∑ i : Fin n, w i| ≤
      ((1 + fp.u) ^ (n - 1) * (1 + e) - 1) *
        (∑ i : Fin n, |w i|) := by
  let S : ℝ := ∑ i : Fin n, |w i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsumdiff : |(∑ i : Fin n, v i) - ∑ i : Fin n, w i| ≤ e * S := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i : Fin n, (v i - w i)| ≤ ∑ i : Fin n, |v i - w i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, e * |w i| := Finset.sum_le_sum fun i _ => hv i
      _ = e * S := by simp [S, Finset.mul_sum]
  have hvabs (i : Fin n) : |v i| ≤ (1 + e) * |w i| := by
    have h := abs_add_le (v i - w i) (w i)
    have heq : v i - w i + w i = v i := by ring
    rw [heq] at h
    have hvi := hv i
    nlinarith
  have hsumabs : (∑ i : Fin n, |v i|) ≤ (1 + e) * S := by
    calc
      _ ≤ ∑ i : Fin n, (1 + e) * |w i| := Finset.sum_le_sum fun i _ => hvabs i
      _ = (1 + e) * S := by simp [S, Finset.mul_sum]
  have hp : 0 ≤ (1 + fp.u) ^ (n - 1) - 1 := by
    have : 1 ≤ (1 + fp.u) ^ (n - 1) := one_le_pow₀ (by linarith [fp.u_nonneg])
    linarith
  have hround := p52_sum_error fp n v hn
  have htri : |p52RecursiveSum fp n v - ∑ i : Fin n, w i| ≤
      |p52RecursiveSum fp n v - ∑ i : Fin n, v i| +
        |(∑ i : Fin n, v i) - ∑ i : Fin n, w i| := by
    convert abs_add_le
      (p52RecursiveSum fp n v - ∑ i : Fin n, v i)
      ((∑ i : Fin n, v i) - ∑ i : Fin n, w i) using 1 <;> ring
  calc
    _ ≤ |p52RecursiveSum fp n v - ∑ i : Fin n, v i| +
      |(∑ i : Fin n, v i) - ∑ i : Fin n, w i| := htri
    _ ≤ ((1 + fp.u) ^ (n - 1) - 1) * (1 + e) * S + e * S := by
      have hh := mul_le_mul_of_nonneg_left hsumabs hp
      linarith
    _ = _ := by ring

private theorem p52_two_perturb (x α δ e u : ℝ)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hα : |α| ≤ e) (hδ : |δ| ≤ u) :
    |x * (1 + α) * (1 + δ) - x| ≤
      ((1 + e) * (1 + u) - 1) * |x| := by
  have hprod : |α * δ| ≤ e * u := by
    rw [abs_mul]
    exact mul_le_mul hα hδ (abs_nonneg _) he
  have hsum : |α + δ + α * δ| ≤ e + u + e * u := by
    calc
      _ ≤ |α + δ| + |α * δ| := abs_add_le _ _
      _ ≤ |α| + |δ| + |α * δ| := by linarith [abs_add_le α δ]
      _ ≤ e + u + e * u := by linarith
  have hfactor : x * (1 + α) * (1 + δ) - x = x * (α + δ + α * δ) := by ring
  rw [hfactor, abs_mul]
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg x)
  nlinarith

private theorem p52_one_perturb (x α e : ℝ) (he : 0 ≤ e)
    (hα : |α| ≤ e) : |x * (1 + α) - x| ≤ e * |x| := by
  have h : x * (1 + α) - x = x * α := by ring
  rw [h, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hα (abs_nonneg x)]

private theorem p52_product_quadratic (n : ℕ) (A CA : ℝ)
    (hA : 0 ≤ A) (hCA : 0 ≤ CA) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        (1 + A * u + CA * u ^ 2) * (1 + u) ^ n ≤
          1 + ((n : ℝ) + A) * u + C * u ^ 2 := by
  induction n with
  | zero =>
    refine ⟨CA, hCA, ?_⟩
    intro u hu hu1
    simp
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨2 * C + (n : ℝ) + A, by positivity, ?_⟩
    intro u hu hu1
    have ht : 0 ≤ 1 + u := by linarith
    have h := mul_le_mul_of_nonneg_right (hbound u hu hu1) ht
    have hcu : 0 ≤ C * u ^ 2 * (1 - u) :=
      mul_nonneg (mul_nonneg hC (sq_nonneg u)) (by linarith)
    rw [pow_succ (1 + u) n]
    push_cast
    nlinarith

private theorem p52_numerator_error (fp : P52FPModel) (n : ℕ)
    (a f ahat : Fin n → ℝ) (A CA : ℝ)
    (hA : 0 ≤ A) (hCA : 0 ≤ CA) (hn : 0 < n)
    (hahat : ∀ i, ∃ α : ℝ,
      ahat i = a i * (1 + α) ∧ |α| ≤ A * fp.u + CA * fp.u ^ 2) :
    |p52RoundedDotProduct fp n ahat f - ∑ i : Fin n, a i * f i| ≤
      ((1 + A * fp.u + CA * fp.u ^ 2) * (1 + fp.u) ^ n - 1) *
        (∑ i : Fin n, |a i * f i|) := by
  let g := 1 + A * fp.u + CA * fp.u ^ 2
  let e := g * (1 + fp.u) - 1
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hEA : 0 ≤ A * fp.u + CA * fp.u ^ 2 := by positivity
  have he : 0 ≤ e := by dsimp [e, g]; nlinarith [mul_nonneg hEA hu]
  have hv (i : Fin n) :
      |fp.fl_mul (ahat i) (f i) - a i * f i| ≤ e * |a i * f i| := by
    obtain ⟨α, ha, hα⟩ := hahat i
    obtain ⟨δ, hδ, hm⟩ := fp.model_mul (ahat i) (f i)
    have hh := p52_two_perturb (a i * f i) α δ
      (A * fp.u + CA * fp.u ^ 2) fp.u hEA hu hα hδ
    rw [hm, ha]
    convert hh using 1 <;> ring
  have h := p52_perturbed_sum_error fp n
    (fun i => fp.fl_mul (ahat i) (f i)) (fun i => a i * f i) hn e he hv
  rw [p52_dot_eq_sum]
  have hn1 : n - 1 + 1 = n := by omega
  convert h using 1
  · congr 1
    dsimp [e, g]
    have hpow : (1 + fp.u) ^ n = (1 + fp.u) ^ (n - 1) * (1 + fp.u) := by
      rw [← pow_succ (1 + fp.u) (n - 1), hn1]
    rw [hpow]
    ring

private theorem p52_denominator_error (fp : P52FPModel) (m : ℕ)
    (b bhat : Fin m → ℝ) (B CB : ℝ)
    (hB : 0 ≤ B) (hCB : 0 ≤ CB) (hm : 0 < m)
    (hbhat : ∀ j, ∃ β : ℝ,
      bhat j = b j * (1 + β) ∧ |β| ≤ B * fp.u + CB * fp.u ^ 2) :
    |p52RecursiveSum fp m bhat - ∑ j : Fin m, b j| ≤
      ((1 + B * fp.u + CB * fp.u ^ 2) * (1 + fp.u) ^ (m - 1) - 1) *
        (∑ j : Fin m, |b j|) := by
  let e := B * fp.u + CB * fp.u ^ 2
  have he : 0 ≤ e := by
    dsimp [e]
    exact add_nonneg (mul_nonneg hB fp.u_nonneg)
      (mul_nonneg hCB (sq_nonneg _))
  have hv (j : Fin m) : |bhat j - b j| ≤ e * |b j| := by
    obtain ⟨β, hb, hβ⟩ := hbhat j
    rw [hb]
    exact p52_one_perturb (b j) β e he hβ
  have h := p52_perturbed_sum_error fp m bhat b hm e he hv
  convert h using 1
  congr 1
  dsimp [e]
  ring

private theorem p52_reconstruct (n : ℕ) (a f : Fin n → ℝ)
    (D Q L : ℝ) (hD : D ≠ 0) (hL : 0 ≤ L)
    (hE : |Q * D - ∑ i : Fin n, a i * f i| ≤
      L * ∑ i : Fin n, |a i * f i|) :
    ∃ fhat : Fin n → ℝ,
      Q = (∑ i : Fin n, a i * fhat i) / D ∧
      ‖fhat - f‖ ≤ L * ‖f‖ := by
  let S : ℝ := ∑ i : Fin n, |a i * f i|
  let E : ℝ := Q * D - ∑ i : Fin n, a i * f i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hS : S = 0
  · have hE0 : E = 0 := by
      have hh : |E| ≤ L * S := hE
      rw [hS, mul_zero] at hh
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    refine ⟨f, ?_, ?_⟩
    · have hQ : Q * D = ∑ i : Fin n, a i * f i := sub_eq_zero.mp hE0
      exact (eq_div_iff hD).mpr hQ
    · simpa using mul_nonneg hL (norm_nonneg f)
  · have hSpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS)
    let t := E / S
    have ht : t * S = E := div_mul_cancel₀ E hS
    have htbound : |t| ≤ L := by
      have hh : |E| ≤ L * S := by simpa [S, E] using hE
      have hh' : |E| / S ≤ L := (div_le_iff₀ hSpos).mpr hh
      simpa [t, abs_div, abs_of_pos hSpos] using hh'
    have hsign (x : ℝ) : |(sign x : ℝ)| ≤ (1 : ℝ) := by
      rcases lt_trichotomy x 0 with hx | hx | hx
      · simp [sign_apply, hx]
      · subst x; simp
      · simp [sign_apply, hx]
    let fhat : Fin n → ℝ := fun i => f i + t * sign (a i) * |f i|
    refine ⟨fhat, ?_, ?_⟩
    · have hsum : (∑ i : Fin n, a i * fhat i) =
          (∑ i : Fin n, a i * f i) + t * S := by
        simp_rw [fhat, mul_add, Finset.sum_add_distrib]
        congr 1
        calc
          (∑ i : Fin n, a i * (t * sign (a i) * |f i|)) =
              ∑ i : Fin n, t * |a i * f i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, ← self_mul_sign (a i)]
            ring
          _ = t * S := by simp [S, Finset.mul_sum]
      rw [hsum, ht]
      dsimp [E]
      exact (eq_div_iff hD).mpr (by ring)
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL (norm_nonneg f))).mpr
      intro i
      have hf : |f i| ≤ ‖f‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm f i
      have hs : |(sign (a i) : ℝ)| ≤ (1 : ℝ) := hsign _
      have hfi : 0 ≤ |f i| := abs_nonneg _
      have ht0 : 0 ≤ |t| := abs_nonneg _
      have h1 : abs (t * sign (a i) * |f i|) ≤ |t| * |f i| := by
        rw [abs_mul, abs_mul, abs_abs]
        nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hs), hfi]
      have h2 : |t| * |f i| ≤ L * ‖f‖ := by
        calc
          _ ≤ L * |f i| := mul_le_mul_of_nonneg_right htbound hfi
          _ ≤ L * ‖f‖ := mul_le_mul_of_nonneg_left hf hL
      simpa only [Pi.sub_apply, Real.norm_eq_abs, fhat, add_sub_cancel_left] using h1.trans h2

private theorem p52_quotient_budget
    (X Y D F S en q u δ K : ℝ)
    (hD : D ≠ 0) (hS : 0 ≤ S) (hen : 0 ≤ en)
    (hq : 0 ≤ q) (hq1 : q < 1) (hu : 0 ≤ u) (hK : 0 ≤ K)
    (hX : |X - F| ≤ en * S)
    (hY : |Y - D| ≤ q * |D|)
    (hF : |F| ≤ S) (hδ : |δ| ≤ u)
    (hbudget : en * (1 + u) + u + q ≤ (1 - q) * K) :
    |((X / Y) * (1 + δ)) * D - F| ≤ K * S := by
  have hDabs : 0 < |D| := abs_pos.mpr hD
  have hYlow : (1 - q) * |D| ≤ |Y| := by
    have ht := abs_add_le (D - Y) Y
    have ht' : |D| ≤ |D - Y| + |Y| := by
      convert ht using 1 <;> ring
    rw [abs_sub_comm] at ht'
    nlinarith
  have hYpos : 0 < |Y| := lt_of_lt_of_le (mul_pos (by linarith) hDabs) hYlow
  have hYne : Y ≠ 0 := abs_pos.mp hYpos
  have hδ1 : |1 + δ| ≤ 1 + u := by
    calc
      _ ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  have hrem : |δ * D + (D - Y)| ≤ (u + q) * |D| := by
    calc
      _ ≤ |δ * D| + |D - Y| := abs_add_le _ _
      _ ≤ u * |D| + q * |D| := by
        rw [abs_mul, abs_sub_comm]
        have hh := mul_le_mul_of_nonneg_right hδ (abs_nonneg D)
        linarith
      _ = _ := by ring
  have hEq : (((X / Y) * (1 + δ)) * D - F) * Y =
      (X - F) * (1 + δ) * D + F * (δ * D + (D - Y)) := by
    field_simp
    ring
  have h1 : |(X - F) * (1 + δ) * D| ≤ en * S * (1 + u) * |D| := by
    rw [abs_mul, abs_mul]
    have hh := mul_le_mul hX hδ1 (abs_nonneg _) (mul_nonneg hen hS)
    have hh' := mul_le_mul_of_nonneg_right hh (abs_nonneg D)
    nlinarith
  have h2 : |F * (δ * D + (D - Y))| ≤ S * ((u + q) * |D|) := by
    rw [abs_mul]
    exact mul_le_mul hF hrem (abs_nonneg _) hS
  have hE : |((X / Y) * (1 + δ)) * D - F| * |Y| ≤
      (en * (1 + u) + u + q) * S * |D| := by
    calc
      _ = |(((X / Y) * (1 + δ)) * D - F) * Y| := by rw [abs_mul]
      _ = |(X - F) * (1 + δ) * D + F * (δ * D + (D - Y))| := by rw [hEq]
      _ ≤ |(X - F) * (1 + δ) * D| + |F * (δ * D + (D - Y))| := abs_add_le _ _
      _ ≤ en * S * (1 + u) * |D| + S * ((u + q) * |D|) := by linarith
      _ = _ := by ring
  have hlow := mul_le_mul_of_nonneg_left hYlow (abs_nonneg (((X / Y) * (1 + δ)) * D - F))
  have hhigh := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hS hDabs.le)
  have hmain : |((X / Y) * (1 + δ)) * D - F| * ((1 - q) * |D|) ≤
      K * S * ((1 - q) * |D|) := by
    nlinarith [hE, hlow, hhigh]
  exact le_of_mul_le_mul_right hmain (mul_pos (by linarith) hDabs)

private theorem p52_budget_quadratic
    (u en q cN CN cD CD Kn Kq C : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hcN : 0 ≤ cN) (hCN : 0 ≤ CN)
    (hcD : 0 ≤ cD) (hCD : 0 ≤ CD)
    (hKn : 0 ≤ Kn) (hKq : 0 ≤ Kq) (hC : 0 ≤ C)
    (hen : en ≤ cN * u + CN * u ^ 2)
    (henLinear : en ≤ Kn * u)
    (hq : q ≤ cD * u + CD * u ^ 2)
    (hqLinear : q ≤ Kq * u) (hqHalf : q ≤ 1 / 2)
    (hCsize : 2 * (CN + Kn + CD + Kq * (cN + 1 + cD)) ≤ C) :
    en * (1 + u) + u + q ≤
      (1 - q) * ((cN + 1 + cD) * u + C * u ^ 2) := by
  have hc : 0 ≤ cN + 1 + cD := by linarith
  have hen2 : en * u ≤ Kn * u ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right henLinear hu
    nlinarith
  have hq2 : q * ((cN + 1 + cD) * u) ≤
      Kq * (cN + 1 + cD) * u ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hqLinear (mul_nonneg hc hu)
    nlinarith
  have hq3 : q * (C * u ^ 2) ≤ (C / 2) * u ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hqHalf (mul_nonneg hC (sq_nonneg u))
    nlinarith
  have hCq : CN + Kn + CD + Kq * (cN + 1 + cD) ≤ C / 2 := by linarith
  have hCq2 := mul_le_mul_of_nonneg_right hCq (sq_nonneg u)
  nlinarith

theorem p52_c3_theorem2_full_named
    (N M : ℕ) (a f : Fin N → ℝ) (b : Fin M → ℝ)
    (A B CA CB betaBound : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hN : 0 < N) (hM : 0 < M)
    (hD0 : (∑ j : Fin M, b j) ≠ 0)
    (hbetaBound : p52DenominatorCondition M b ≤ betaBound)
    (hbetaBound0 : 0 ≤ betaBound) :
    ∃ u0 C : ℝ, 0 < u0 ∧ 0 ≤ C ∧
      ∀ (fp : P52FPModel) (ahat : Fin N → ℝ) (bhat : Fin M → ℝ),
      fp.u ≤ u0 →
      (∀ i, ∃ alpha_i : ℝ,
        ahat i = a i * (1 + alpha_i) ∧
          |alpha_i| ≤ A * fp.u + CA * fp.u ^ 2) →
      (∀ j, ∃ beta_j : ℝ,
        bhat j = b j * (1 + beta_j) ∧
          |beta_j| ≤ B * fp.u + CB * fp.u ^ 2) →
      ∃ fhat : Fin N → ℝ,
        p52ComputedQuotient fp N M ahat f bhat =
          (∑ i : Fin N, a i * fhat i) / (∑ j : Fin M, b j) ∧
        ‖fhat - f‖ ≤
          ((((N : ℝ) + 1 + A) +
            (((M - 1 : ℕ) : ℝ) + B) * betaBound) * fp.u +
            C * fp.u ^ 2) * ‖f‖ := by
  -- PROOF_START P52-C3-H001
  obtain ⟨CN, hCN, hNpoly⟩ := p52_product_quadratic N A CA hA hCA
  obtain ⟨CD, hCD, hDpoly⟩ := p52_product_quadratic (M - 1) B CB hB hCB
  let cN : ℝ := (N : ℝ) + A
  let d : ℝ := ((M - 1 : ℕ) : ℝ) + B
  let cD : ℝ := d * betaBound
  let QD : ℝ := CD * betaBound
  let Kn : ℝ := cN + CN
  let Kq : ℝ := cD + QD
  let c : ℝ := cN + 1 + cD
  let C : ℝ := 2 * (CN + Kn + QD + Kq * c + 1)
  let u0 : ℝ := 1 / (2 * (Kq + 1))
  have hcN : 0 ≤ cN := by dsimp [cN]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hcD : 0 ≤ cD := mul_nonneg hd hbetaBound0
  have hQD : 0 ≤ QD := mul_nonneg hCD hbetaBound0
  have hKn : 0 ≤ Kn := add_nonneg hcN hCN
  have hKq : 0 ≤ Kq := add_nonneg hcD hQD
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hu0 : 0 < u0 := by
    dsimp [u0]
    positivity
  have hu01 : u0 ≤ 1 := by
    dsimp [u0]
    apply (div_le_iff₀ (by linarith : 0 < 2 * (Kq + 1))).mpr
    nlinarith
  have hKqu0 : Kq * u0 ≤ 1 / 2 := by
    dsimp [u0]
    rw [mul_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 2 * (Kq + 1))).mpr
    nlinarith
  refine ⟨u0, C, hu0, hC, ?_⟩
  intro fp ahat bhat hu hahat hbhat
  let u : ℝ := fp.u
  have hu0' : 0 ≤ u := fp.u_nonneg
  have hu1 : u ≤ 1 := le_trans hu hu01
  have hu2 : u ^ 2 ≤ u := by nlinarith [mul_nonneg hu0' (sub_nonneg.mpr hu1)]
  let D : ℝ := ∑ j : Fin M, b j
  let F : ℝ := ∑ i : Fin N, a i * f i
  let S : ℝ := ∑ i : Fin N, |a i * f i|
  let T : ℝ := ∑ j : Fin M, |b j|
  let X : ℝ := p52RoundedDotProduct fp N ahat f
  let Y : ℝ := p52RecursiveSum fp M bhat
  let en : ℝ := (1 + A * u + CA * u ^ 2) * (1 + u) ^ N - 1
  let ed : ℝ := (1 + B * u + CB * u ^ 2) * (1 + u) ^ (M - 1) - 1
  let q : ℝ := ed * betaBound
  let L : ℝ := c * u + C * u ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hF : |F| ≤ S := Finset.abs_sum_le_sum_abs _ _
  have hDabs : 0 < |D| := abs_pos.mpr hD0
  have hTbound : T ≤ betaBound * |D| := by
    have hh := mul_le_mul_of_nonneg_right hbetaBound hDabs.le
    have hcondition : p52DenominatorCondition M b * |D| = T := by
      dsimp [p52DenominatorCondition, D, T]
      exact div_mul_cancel₀ _ (ne_of_gt hDabs)
    simpa [hcondition] using hh
  have hen0 : 0 ≤ en := by
    have hfirst : 1 ≤ 1 + A * u + CA * u ^ 2 := by
      nlinarith [mul_nonneg hA hu0', mul_nonneg hCA (sq_nonneg u)]
    have hpow : 1 ≤ (1 + u) ^ N := one_le_pow₀ (by linarith)
    dsimp [en]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hpow)]
  have hed0 : 0 ≤ ed := by
    have hfirst : 1 ≤ 1 + B * u + CB * u ^ 2 := by
      nlinarith [mul_nonneg hB hu0', mul_nonneg hCB (sq_nonneg u)]
    have hpow : 1 ≤ (1 + u) ^ (M - 1) := one_le_pow₀ (by linarith)
    dsimp [ed]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfirst) (sub_nonneg.mpr hpow)]
  have hq0 : 0 ≤ q := mul_nonneg hed0 hbetaBound0
  have henBound : en ≤ cN * u + CN * u ^ 2 := by
    have hh := hNpoly u hu0' hu1
    dsimp [en, cN, u]
    linarith
  have hedBound : ed ≤ d * u + CD * u ^ 2 := by
    have hh := hDpoly u hu0' hu1
    dsimp [ed, d, u]
    linarith
  have hqBound : q ≤ cD * u + QD * u ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hedBound hbetaBound0
    change ed * betaBound ≤ (d * betaBound) * u +
      (CD * betaBound) * u ^ 2
    convert hh using 1 <;> ring
  have henLinear : en ≤ Kn * u := by
    have hh := mul_le_mul_of_nonneg_left hu2 hCN
    dsimp [Kn]
    nlinarith
  have hqLinear : q ≤ Kq * u := by
    have hh := mul_le_mul_of_nonneg_left hu2 hQD
    dsimp [Kq]
    nlinarith
  have hqHalf : q ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hu hKq
    linarith [hqLinear, hKqu0]
  have hq1 : q < 1 := by linarith
  have hX : |X - F| ≤ en * S := by
    simpa [X, F, en, S, u] using
      p52_numerator_error fp N a f ahat A CA hA hCA hN hahat
  have hYraw : |Y - D| ≤ ed * T := by
    simpa [Y, D, ed, T, u] using
      p52_denominator_error fp M b bhat B CB hB hCB hM hbhat
  have hY : |Y - D| ≤ q * |D| := by
    have hh := mul_le_mul_of_nonneg_left hTbound hed0
    dsimp [q]
    nlinarith [hYraw, hh]
  have hYne : Y ≠ 0 := by
    intro hy
    rw [hy, zero_sub, abs_neg] at hY
    nlinarith [mul_pos (by linarith : 0 < 1 - q) hDabs]
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div X Y hYne
  have hbudget : en * (1 + u) + u + q ≤ (1 - q) * L := by
    have hsize : 2 * (CN + Kn + QD + Kq * (cN + 1 + cD)) ≤ C := by
      dsimp [C, c]
      linarith
    simpa [L, c] using
      p52_budget_quadratic u en q cN CN cD QD Kn Kq C
        hu0' hu1 hcN hCN hcD hQD hKn hKq hC
        henBound henLinear hqBound hqLinear hqHalf hsize
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hE : |p52ComputedQuotient fp N M ahat f bhat * D - F| ≤ L * S := by
    have hh := p52_quotient_budget X Y D F S en q u δ L
      hD0 hS hen0 hq0 hq1 hu0' hL hX hY hF hδ hbudget
    have hQ : p52ComputedQuotient fp N M ahat f bhat =
        (X / Y) * (1 + δ) := by
      simpa [p52ComputedQuotient, X, Y] using hdiv
    simpa [hQ] using hh
  obtain ⟨fhat, heq, hnorm⟩ := p52_reconstruct N a f D
    (p52ComputedQuotient fp N M ahat f bhat) L hD0 hL hE
  refine ⟨fhat, ?_, ?_⟩
  · simpa [D] using heq
  · calc
      ‖fhat - f‖ ≤ L * ‖f‖ := hnorm
      _ = _ := by dsimp [L, c, cN, cD, d, u]; ring

end VSCLReuse

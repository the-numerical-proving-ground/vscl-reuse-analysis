import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p07_recursive_bounds
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (fl : ℝ → ℝ → ℝ)
    (hfl : ∀ x y : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧ fl x y = (x + y) * (1 + δ)) :
    ∀ n : ℕ, ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      ∀ e : Fin n → ℝ, (∀ i, |e i| ≤ u) →
      (1 - u) ^ n * (∑ i, a i) ≤
        recursiveSum fl n (fun i => a i * (1 + e i)) ∧
      recursiveSum fl n (fun i => a i * (1 + e i)) ≤
        (1 + u) ^ n * (∑ i, a i) := by
  intro n
  induction n with
  | zero =>
      intro a ha e he
      simp [recursiveSum]
  | succ n ih =>
      intro a ha e he
      let b : Fin n → ℝ := fun i => a i.castSucc
      let d : Fin n → ℝ := fun i => e i.castSucc
      have hb : ∀ i, 0 ≤ b i := fun i => ha i.castSucc
      have hd : ∀ i, |d i| ≤ u := fun i => he i.castSucc
      obtain ⟨hlo, hhi⟩ := ih b hb d hd
      let A : ℝ := ∑ i, b i
      let z : ℝ := a (Fin.last n)
      let E : ℝ := e (Fin.last n)
      let R : ℝ := recursiveSum fl n (fun i => b i * (1 + d i))
      have hsum : (∑ i, a i) = A + z := by
        simp only [Fin.sum_univ_castSucc]
        rfl
      have hz : 0 ≤ z := ha _
      have hA : 0 ≤ A := Finset.sum_nonneg fun i hi => hb i
      have hElo : 1 - u ≤ 1 + E := by
        have := (abs_le.mp (he (Fin.last n))).1
        linarith
      have hEhi : 1 + E ≤ 1 + u := by
        have := (abs_le.mp (he (Fin.last n))).2
        linarith
      have hmin : 0 ≤ 1 - u := by linarith
      have hplus : 0 ≤ 1 + u := by linarith
      have hpowlo : (1 - u) ^ n ≤ 1 - u ∨ n = 0 := by
        by_cases hn : n = 0
        · exact Or.inr hn
        · left
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [pow_succ]
          have hp : (1 - u) ^ k ≤ 1 := pow_le_one₀ hmin (by linarith)
          exact mul_le_of_le_one_left hmin hp
      have hpowhi : 1 + u ≤ (1 + u) ^ n ∨ n = 0 := by
        by_cases hn : n = 0
        · exact Or.inr hn
        · left
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
          rw [pow_succ]
          have hp : 1 ≤ (1 + u) ^ k := one_le_pow₀ (by linarith)
          exact le_mul_of_one_le_left hplus hp
      by_cases hn : n = 0
      · subst n
        simp only [recursiveSum, ↓reduceDIte]
        constructor
        · simpa [Fin.sum_univ_one, z, E, mul_comm] using
            (mul_le_mul_of_nonneg_left hElo hz)
        · simpa [Fin.sum_univ_one, z, E, mul_comm] using
            (mul_le_mul_of_nonneg_left hEhi hz)
      · have hR0 : 0 ≤ R := by
          have h : 0 ≤ (1 - u) ^ n * A := mul_nonneg (pow_nonneg hmin _) hA
          exact h.trans hlo
        obtain ⟨δ, hδ, hflδ⟩ := hfl R (z * (1 + E))
        have hδlo : 1 - u ≤ 1 + δ := by
          have := (abs_le.mp hδ).1
          linarith
        have hδhi : 1 + δ ≤ 1 + u := by
          have := (abs_le.mp hδ).2
          linarith
        have hv0 : 0 ≤ z * (1 + E) := mul_nonneg hz (hmin.trans hElo)
        have hRlo : (1 - u) ^ n * A + (1 - u) * z ≤ R + z * (1 + E) := by
          exact add_le_add hlo (by nlinarith [mul_le_mul_of_nonneg_left hElo hz])
        have hRhi : R + z * (1 + E) ≤ (1 + u) ^ n * A + (1 + u) * z := by
          nlinarith [mul_le_mul_of_nonneg_left hEhi hz]
        have hbaseLo : (1 - u) ^ n * (A + z) ≤
            (1 - u) ^ n * A + (1 - u) * z := by
          have hp := hpowlo.resolve_right hn
          nlinarith [mul_nonneg (sub_nonneg.mpr hp) hz]
        have hbaseHi : (1 + u) ^ n * A + (1 + u) * z ≤
            (1 + u) ^ n * (A + z) := by
          have hp := hpowhi.resolve_right hn
          nlinarith [mul_nonneg (sub_nonneg.mpr hp) hz]
        have hresult : recursiveSum fl (n + 1) (fun i => a i * (1 + e i)) =
            (R + z * (1 + E)) * (1 + δ) := by
          simp only [recursiveSum, hn, ↓reduceDIte, R, z, E, b, d]
          exact hflδ
        rw [hsum, hresult]
        constructor
        · calc
            (1 - u) ^ (n + 1) * (A + z) =
                ((1 - u) ^ n * (A + z)) * (1 - u) := by rw [pow_succ]; ring
            _ ≤ ((1 - u) ^ n * A + (1 - u) * z) * (1 - u) :=
              mul_le_mul_of_nonneg_right hbaseLo hmin
            _ ≤ (R + z * (1 + E)) * (1 + δ) := by
              exact (mul_le_mul_of_nonneg_right hRlo hmin).trans
                (mul_le_mul_of_nonneg_left hδlo (add_nonneg hR0 hv0))
        · calc
            (R + z * (1 + E)) * (1 + δ) ≤
                (R + z * (1 + E)) * (1 + u) :=
              mul_le_mul_of_nonneg_left hδhi (add_nonneg hR0 hv0)
            _ ≤ ((1 + u) ^ n * A + (1 + u) * z) * (1 + u) :=
              mul_le_mul_of_nonneg_right hRhi hplus
            _ ≤ ((1 + u) ^ n * (A + z)) * (1 + u) :=
              mul_le_mul_of_nonneg_right hbaseHi hplus
            _ = (1 + u) ^ (n + 1) * (A + z) := by rw [pow_succ]; ring

private theorem p07_pow_bounds (n : ℕ) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - (n : ℝ) * u ≤ (1 - u) ^ n ∧
      (1 + u) ^ n ≤
        1 + (n : ℝ) * u + ((n + 1 : ℝ) * (4 : ℝ) ^ n) * u ^ 2 := by
  induction n with
  | zero => simp [sq_nonneg]
  | succ n ih =>
      have hmin : 0 ≤ 1 - u := by linarith
      have hplus : 0 ≤ 1 + u := by linarith
      have hfour : 1 ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      have hcoef :
          (n : ℝ) + 2 * ((n + 1 : ℝ) * (4 : ℝ) ^ n) ≤
            ((n + 2 : ℝ) * (4 : ℝ) ^ (n + 1)) := by
        rw [pow_succ]
        have hh : 0 ≤ (2 * (n : ℝ) + 8) * ((4 : ℝ) ^ n - 1) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith
      have hu3 : u ^ 3 ≤ u ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
      constructor
      · calc
          1 - ((n + 1 : ℕ) : ℝ) * u ≤
              (1 - (n : ℝ) * u) * (1 - u) := by
                have h : 0 ≤ (n : ℝ) * u ^ 2 := mul_nonneg (by positivity) (sq_nonneg u)
                push_cast
                nlinarith
          _ ≤ (1 - u) ^ n * (1 - u) :=
            mul_le_mul_of_nonneg_right ih.1 hmin
          _ = (1 - u) ^ (n + 1) := by rw [pow_succ]
      · calc
          (1 + u) ^ (n + 1) = (1 + u) ^ n * (1 + u) := by rw [pow_succ]
          _ ≤ (1 + (n : ℝ) * u + ((n + 1 : ℝ) * (4 : ℝ) ^ n) * u ^ 2) *
                (1 + u) := mul_le_mul_of_nonneg_right ih.2 hplus
          _ ≤ 1 + ((n + 1 : ℕ) : ℝ) * u +
                ((n + 2 : ℝ) * (4 : ℝ) ^ (n + 1)) * u ^ 2 := by
              have hC : 0 ≤
                  ((n + 2 : ℝ) * (4 : ℝ) ^ (n + 1)) -
                    ((n : ℝ) + 2 * ((n + 1 : ℝ) * (4 : ℝ) ^ n)) := by
                linarith
              have h1 : 0 ≤
                  (((n + 2 : ℝ) * (4 : ℝ) ^ (n + 1)) -
                    ((n : ℝ) + 2 * ((n + 1 : ℝ) * (4 : ℝ) ^ n))) * u ^ 2 :=
                mul_nonneg hC (sq_nonneg u)
              have h2 : 0 ≤ ((n + 1 : ℝ) * (4 : ℝ) ^ n) * (u ^ 2 - u ^ 3) :=
                mul_nonneg (by positivity) (by linarith)
              push_cast
              nlinarith
          _ = 1 + ((n + 1 : ℕ) : ℝ) * u +
                (((n + 1 : ℕ) + 1 : ℝ) * (4 : ℝ) ^ (n + 1)) * u ^ 2 := by
              push_cast
              ring

private theorem p07_ratio_error
    (N C u S r e d : ℝ)
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hu : 0 ≤ u)
    (hsmall : (C + 1 + N * (N + 3)) * u ≤ 1)
    (hS : 0 < S)
    (hrlo : (1 - N * u) * S ≤ r)
    (hrhi : r ≤ (1 + N * u + C * u ^ 2) * S)
    (he : |e| ≤ u) (hd : |d| ≤ u) :
    |S * (1 + e) * (1 + d) - r| ≤ (N + 3) * u * r := by
  have helo : 1 - u ≤ 1 + e := by
    have := (abs_le.mp he).1
    linarith
  have hehi : 1 + e ≤ 1 + u := by
    have := (abs_le.mp he).2
    linarith
  have hdlo : 1 - u ≤ 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  have hdhi : 1 + d ≤ 1 + u := by
    have := (abs_le.mp hd).2
    linarith
  have hmin : 0 ≤ 1 - u := by
    have hD : 0 ≤ N * (N + 3) := mul_nonneg hN (by linarith)
    have hDm : 1 ≤ C + 1 + N * (N + 3) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hDm) hu]
  have he0 : 0 ≤ 1 + e := hmin.trans helo
  have hqlo : (1 - u) ^ 2 ≤ (1 + e) * (1 + d) := by
    calc
      (1 - u) ^ 2 = (1 - u) * (1 - u) := by ring
      _ ≤ (1 + e) * (1 - u) := mul_le_mul_of_nonneg_right helo hmin
      _ ≤ (1 + e) * (1 + d) := mul_le_mul_of_nonneg_left hdlo he0
  have hqhi : (1 + e) * (1 + d) ≤ (1 + u) ^ 2 := by
    calc
      (1 + e) * (1 + d) ≤ (1 + u) * (1 + d) :=
        mul_le_mul_of_nonneg_right hehi (hmin.trans hdlo)
      _ ≤ (1 + u) * (1 + u) :=
        mul_le_mul_of_nonneg_left hdhi (by linarith)
      _ = (1 + u) ^ 2 := by ring
  have hqloS : (1 - 2 * u) * S ≤ S * ((1 + e) * (1 + d)) := by
    have h := mul_le_mul_of_nonneg_right hqlo (le_of_lt hS)
    nlinarith [mul_nonneg (sq_nonneg u) (le_of_lt hS)]
  have hqhiS : S * ((1 + e) * (1 + d)) ≤
      (1 + 2 * u + u ^ 2) * S := by
    have h := mul_le_mul_of_nonneg_right hqhi (le_of_lt hS)
    nlinarith
  let B : ℝ := (N + 2) * u + (C + 1) * u ^ 2
  have habs : |S * (1 + e) * (1 + d) - r| ≤ B * S := by
    rw [abs_le]
    constructor <;> dsimp [B] <;> nlinarith [mul_nonneg (sq_nonneg u) (le_of_lt hS)]
  have hcoef : B ≤ (N + 3) * u * (1 - N * u) := by
    have h : 0 ≤ u * (1 - (C + 1 + N * (N + 3)) * u) :=
      mul_nonneg hu (by linarith)
    dsimp [B]
    nlinarith
  have hcoefS := mul_le_mul_of_nonneg_right hcoef (le_of_lt hS)
  have hrmul := mul_le_mul_of_nonneg_left hrlo
    (mul_nonneg (by linarith : 0 ≤ N + 3) hu)
  nlinarith [habs]

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
  let C : ℝ := (n + 1 : ℝ) * (4 : ℝ) ^ n
  let D : ℝ := C + 1 + (n : ℝ) * (n + 3 : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hN : 0 ≤ (n : ℝ) := by positivity
  have hD : 0 < D := by
    dsimp [D]
    have h : 0 ≤ (n : ℝ) * (n + 3 : ℝ) := by positivity
    linarith
  have hDge : (n : ℝ) ≤ D := by
    dsimp [D]
    have h : 0 ≤ (n : ℝ) * (n + 2 : ℝ) := by positivity
    linarith
  have hDone : 1 ≤ D := by
    dsimp [D]
    have h : 0 ≤ (n : ℝ) * (n + 3 : ℝ) := by positivity
    linarith
  have hsmall : ∀ᶠ t in l, u t < 1 / D :=
    hu.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / D))
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hS : 0 < p07ExpSum x := by
    unfold p07ExpSum
    exact Finset.sum_pos (fun i hi => Real.exp_pos (x i))
      (Finset.univ_nonempty)
  let g : Fin n → ℝ := p07ExactSoftmax x
  have hgpos : ∀ i, 0 < g i := by
    intro i
    dsimp [g, p07ExactSoftmax]
    exact div_pos (Real.exp_pos _) hS
  have hgnorm : 0 < ‖g‖ := by
    let i : Fin n := ⟨0, hn⟩
    have hi := norm_le_pi_norm g i
    have hgi : 0 < ‖g i‖ := norm_pos_iff.mpr (ne_of_gt (hgpos i))
    exact lt_of_lt_of_le hgi hi
  refine ⟨fun _ => 0, Asymptotics.isBigO_zero _ _, ?_⟩
  filter_upwards [hsmall] with t ht
  have hu0 : 0 ≤ u t := (abs_nonneg (divError t ⟨0, hn⟩)).trans (hdiv t ⟨0, hn⟩)
  have huD : D * u t < 1 := by
    have hh := (lt_div_iff₀ hD).mp ht
    nlinarith
  have hu1 : u t ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hDone hu0
    nlinarith
  have hnu : (n : ℝ) * u t < 1 := by
    have hh := mul_le_mul_of_nonneg_right hDge hu0
    nlinarith
  have hmodel : ∀ a b : ℝ, ∃ δ : ℝ,
      |δ| ≤ u t ∧ (run t).fp.fl_add a b = (a + b) * (1 + δ) := by
    intro a b
    obtain ⟨δ, hδ, hfl⟩ := (run t).fp.model_add a b
    exact ⟨δ, by simpa [(run t).unit_eq] using hδ, hfl⟩
  have hrbound := p07_recursive_bounds (u t) hu0 hu1
    (run t).fp.fl_add hmodel n (fun i => Real.exp (x i))
    (fun i => le_of_lt (Real.exp_pos (x i))) (run t).expError
    (fun i => by simpa [(run t).unit_eq] using (run t).expError_le i)
  let r : ℝ := p07RecursiveComputedExpSum (run t)
  have hrbound' : (1 - u t) ^ n * p07ExpSum x ≤ r ∧
      r ≤ (1 + u t) ^ n * p07ExpSum x := by
    simpa [r, p07RecursiveComputedExpSum, p07ComputedExp,
      p07ExpSum] using hrbound
  have hpow := p07_pow_bounds n (u t) hu0 hu1
  have hrlo : (1 - (n : ℝ) * u t) * p07ExpSum x ≤ r :=
    (mul_le_mul_of_nonneg_right hpow.1 (le_of_lt hS)).trans hrbound'.1
  have hrhi : r ≤ (1 + (n : ℝ) * u t + C * (u t) ^ 2) * p07ExpSum x := by
    calc
      r ≤ (1 + u t) ^ n * p07ExpSum x := hrbound'.2
      _ ≤ (1 + (n : ℝ) * u t + C * (u t) ^ 2) * p07ExpSum x := by
        exact mul_le_mul_of_nonneg_right (by simpa [C] using hpow.2) (le_of_lt hS)
  have hrpos : 0 < r :=
    lt_of_lt_of_le (mul_pos (by linarith) hS) hrlo
  have hvec : ‖(fun i : Fin n =>
      p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i)‖ ≤
      ((n + 3 : ℝ) * u t) * ‖g‖ := by
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hu0) (norm_nonneg g))).2
    intro i
    let a : ℝ := Real.exp (x i)
    let e : ℝ := (run t).expError i
    let d : ℝ := divError t i
    have ha : 0 < a := Real.exp_pos _
    have he : |e| ≤ u t := by simpa [e, (run t).unit_eq] using (run t).expError_le i
    have hd : |d| ≤ u t := hdiv t i
    have hratio := p07_ratio_error (n : ℝ) C (u t) (p07ExpSum x) r e d
      hN hC hu0 (le_of_lt huD) hS hrlo hrhi he hd
    have hratio' : |(p07ExpSum x * (1 + e) * (1 + d) - r) / r| ≤
        (n + 3 : ℝ) * u t := by
      rw [abs_div, abs_of_pos hrpos]
      exact (div_le_iff₀ hrpos).2 hratio
    have hag : 0 ≤ a / p07ExpSum x := le_of_lt (div_pos ha hS)
    have hident : p07ComputedSoftmax (run t) (divError t) i -
        p07ExactSoftmax x i =
        (a / p07ExpSum x) *
          ((p07ExpSum x * (1 + e) * (1 + d) - r) / r) := by
      dsimp [p07ComputedSoftmax, p07ExactSoftmax, p07ComputedExp, r,
        a, e, d]
      field_simp [ne_of_gt hS, ne_of_gt hrpos]
      rw [sub_div, div_self (ne_of_gt hrpos)]
    have hscalar : |p07ComputedSoftmax (run t) (divError t) i -
        p07ExactSoftmax x i| ≤
        ((n + 3 : ℝ) * u t) * (a / p07ExpSum x) := by
      rw [hident, abs_mul, abs_of_nonneg hag]
      nlinarith [mul_le_mul_of_nonneg_left hratio' hag]
    have hgi : a / p07ExpSum x ≤ ‖g‖ := by
      have hh := norm_le_pi_norm g i
      simpa [g, p07ExactSoftmax, a, Real.norm_eq_abs,
        abs_of_pos hS] using hh
    have hh := mul_le_mul_of_nonneg_left hgi
      (mul_nonneg (by positivity : 0 ≤ (n + 3 : ℝ)) hu0)
    simpa [Real.norm_eq_abs] using hscalar.trans hh
  have hgoal :
      ‖(fun i : Fin n => p07ComputedSoftmax (run t) (divError t) i -
          p07ExactSoftmax x i)‖ / ‖g‖ ≤ (n + 3 : ℝ) * u t :=
    (div_le_iff₀ hgnorm).2 hvec
  simpa [g] using hgoal

end VSCLReuse

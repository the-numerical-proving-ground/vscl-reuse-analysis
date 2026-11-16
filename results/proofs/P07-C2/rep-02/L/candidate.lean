import VSCLReuse.P07.Definitions
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace VSCLReuse

open scoped BigOperators

private theorem recursiveSum_bounds {n : ℕ} (fp : StandardAddModel)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hu : fp.u < 1) :
    (1 - fp.u) ^ (n-1) * (∑ i, v i) ≤ recursiveSum fp.fl_add n v ∧
    recursiveSum fp.fl_add n v ≤ (1 + fp.u) ^ (n-1) * (∑ i, v i) := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [recursiveSum]
    · have hv' : ∀ i : Fin n, 0 ≤ v i.castSucc := fun i => hv i.castSucc
      obtain ⟨hlo, hup⟩ := ih (fun i => v i.castSucc) hv'
      obtain ⟨δ, hδ, heq⟩ := fp.model_add
        (recursiveSum fp.fl_add n (fun i => v i.castSucc)) (v (Fin.last n))
      have hδlo : 1 - fp.u ≤ 1 + δ := by have := (abs_le.mp hδ).1; linarith
      have hδhi : 1 + δ ≤ 1 + fp.u := by have := (abs_le.mp hδ).2; linarith
      have hbase : 0 ≤ 1 - fp.u := by linarith
      have hplus : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hδpos : 0 ≤ 1 + δ := by linarith
      have hpowlo : 0 ≤ (1 - fp.u)  ^ (n-1) := pow_nonneg hbase _
      have hpowhi : 1 ≤ (1 + fp.u)  ^ (n-1) := one_le_pow₀ (by linarith [fp.u_nonneg])
      have hns : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
      have hpowlo_step : (1 - fp.u)^n = (1 - fp.u)^(n-1) * (1-fp.u) := by
        conv_lhs => rw [← hns, pow_succ]
      have hpowhi_step : (1 + fp.u)^n = (1 + fp.u)^(n-1) * (1+fp.u) := by
        conv_lhs => rw [← hns, pow_succ]
      have hsumlo : 0 ≤ ∑ i : Fin n, v i.castSucc := Finset.sum_nonneg (fun i _ => hv i.castSucc)
      have hvl : 0 ≤ v (Fin.last n) := hv _
      have hsum : (∑ i : Fin (n + 1), v i) =
          (∑ i : Fin n, v i.castSucc) + v (Fin.last n) := Fin.sum_univ_castSucc v
      have hrec : recursiveSum fp.fl_add (n+1) v =
          (recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n)) * (1+δ) := by
        simp [recursiveSum, hn, heq]
      rw [hrec, hsum]
      constructor
      · have hpowlo1 : (1 - fp.u)^(n-1) ≤ 1 := pow_le_one₀ hbase (by linarith [fp.u_nonneg])
        have h1 : (1 - fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n) ≤
            recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n) := by linarith
        have h2 : (1 - fp.u)^(n-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n)) ≤
            (1 - fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith [hpowlo1])) hvl]
        calc
          (1 - fp.u)^((n+1)-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n))
              = ((1 - fp.u)^(n-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n))) * (1-fp.u) := by simp only [Nat.add_sub_cancel_right]; rw [hpowlo_step]; ring
          _ ≤ ((1 - fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n)) * (1-fp.u) := mul_le_mul_of_nonneg_right h2 hbase
          _ ≤ (recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n)) * (1-fp.u) := mul_le_mul_of_nonneg_right h1 hbase
          _ ≤ (recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n)) * (1+δ) := by
            apply mul_le_mul_of_nonneg_left hδlo
            linarith [hlo, mul_nonneg hpowlo hsumlo]
      · have h1 : recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n) ≤
            (1 + fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n) := by linarith
        have h2 : (1 + fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n) ≤
            (1 + fp.u)^(n-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n)) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith [hpowhi])) hvl]
        calc
          (recursiveSum fp.fl_add n (fun i => v i.castSucc) + v (Fin.last n)) * (1+δ)
              ≤ ((1 + fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n)) * (1+δ) := mul_le_mul_of_nonneg_right h1 hδpos
          _ ≤ ((1 + fp.u)^(n-1) * (∑ i : Fin n, v i.castSucc) + v (Fin.last n)) * (1+fp.u) := by
            apply mul_le_mul_of_nonneg_left hδhi
            nlinarith [mul_nonneg (pow_nonneg hplus (n-1)) hsumlo]
          _ ≤ ((1 + fp.u)^(n-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n))) * (1+fp.u) := mul_le_mul_of_nonneg_right h2 hplus
          _ = (1+fp.u)^((n+1)-1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n)) := by simp only [Nat.add_sub_cancel_right]; rw [hpowhi_step]; ring

private theorem p07_sum_bounds {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
    {u : ℝ} (run : P07BasicSumExecution x u) (hu : u < 1) :
    (1-u)^n * p07ExpSum x ≤ p07RecursiveComputedExpSum run ∧
    p07RecursiveComputedExpSum run ≤ (1+u)^n * p07ExpSum x := by
  have hu0 : 0 ≤ u := run.unit_eq ▸ run.fp.u_nonneg
  have hv : ∀ i, 0 ≤ p07ComputedExp run i := by
    intro i
    have he := Real.exp_pos (x i)
    have he' := run.expError_le i
    have hδ : 0 ≤ 1 + run.expError i := by
      have := (abs_le.mp he').1
      linarith
    exact mul_nonneg he.le hδ
  obtain ⟨hlo, hhi⟩ := recursiveSum_bounds run.fp
    (p07ComputedExp run) hv (by simpa [run.unit_eq] using hu)
  have hlocal_lo : ∀ i, Real.exp (x i) * (1-u) ≤ p07ComputedExp run i := by
    intro i
    unfold p07ComputedExp
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := (abs_le.mp (run.expError_le i)).1
    linarith
  have hlocal_hi : ∀ i, p07ComputedExp run i ≤ Real.exp (x i) * (1+u) := by
    intro i
    unfold p07ComputedExp
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have := (abs_le.mp (run.expError_le i)).2
    linarith
  have hsumlo : p07ExpSum x * (1-u) ≤ p07ExactComputedExpSum run := by
    unfold p07ExpSum p07ExactComputedExpSum
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hlocal_lo i)
  have hsumhi : p07ExactComputedExpSum run ≤ p07ExpSum x * (1+u) := by
    unfold p07ExpSum p07ExactComputedExpSum
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => hlocal_hi i)
  have hminus : 0 ≤ (1-u)^(n-1) := pow_nonneg (by linarith) _
  have hplus : 0 ≤ (1+u)^(n-1) := pow_nonneg (by linarith) _
  have hns : n-1+1=n := Nat.sub_add_cancel hn
  have hpowlo_eq : (1-u)^n = (1-u)^(n-1) * (1-u) := by
    conv_lhs => rw [← hns, pow_succ]
  have hpowhi_eq : (1+u)^n = (1+u)^(n-1) * (1+u) := by
    conv_lhs => rw [← hns, pow_succ]
  constructor
  · calc
      (1-u)^n * p07ExpSum x = (1-u)^(n-1) * (p07ExpSum x * (1-u)) := by
        rw [hpowlo_eq]
        ring
      _ ≤ (1-u)^(n-1) * p07ExactComputedExpSum run :=
        mul_le_mul_of_nonneg_left hsumlo hminus
      _ ≤ p07RecursiveComputedExpSum run := by
        simpa [p07RecursiveComputedExpSum, p07ExactComputedExpSum, run.unit_eq] using hlo
  · calc
      p07RecursiveComputedExpSum run ≤ (1+u)^(n-1) * p07ExactComputedExpSum run := by
        simpa [p07RecursiveComputedExpSum, p07ExactComputedExpSum, run.unit_eq] using hhi
      _ ≤ (1+u)^(n-1) * (p07ExpSum x * (1+u)) :=
        mul_le_mul_of_nonneg_left hsumhi hplus
      _ = (1+u)^n * p07ExpSum x := by
        rw [hpowhi_eq]
        ring

private theorem p07_upper_poly_deriv (n : ℕ) :
    HasDerivAt (fun z : ℝ => (1+(n+3:ℝ)*z)*(1-z)^n-(1+z)^2) 1 0 := by
  have hz : HasDerivAt (fun z : ℝ => z) 1 0 := by
    simpa using hasDerivAt_id (0 : ℝ)
  have hm : HasDerivAt (fun z : ℝ => 1-z) (-1) 0 := hz.const_sub 1
  have hp : HasDerivAt (fun z : ℝ => 1+z) 1 0 := hz.const_add 1
  have hf : HasDerivAt (fun z : ℝ => 1+(n+3:ℝ)*z) (n+3:ℝ) 0 := by
    convert (hz.const_mul (n+3:ℝ)).const_add 1 using 1 <;> norm_num
  convert (hf.mul (hm.pow n)).sub (hp.pow 2) using 1 <;> simp <;> ring

private theorem p07_lower_poly_deriv (n : ℕ) :
    HasDerivAt (fun z : ℝ => (1-z)^2-(1-(n+3:ℝ)*z)*(1+z)^n) 1 0 := by
  have hz : HasDerivAt (fun z : ℝ => z) 1 0 := by
    simpa using hasDerivAt_id (0 : ℝ)
  have hm : HasDerivAt (fun z : ℝ => 1-z) (-1) 0 := hz.const_sub 1
  have hp : HasDerivAt (fun z : ℝ => 1+z) 1 0 := hz.const_add 1
  have hf : HasDerivAt (fun z : ℝ => 1-(n+3:ℝ)*z) (-(n+3:ℝ)) 0 := by
    convert (hz.const_mul (n+3:ℝ)).const_sub 1 using 1 <;> norm_num
  convert (hm.pow 2).sub (hf.mul (hp.pow n)) using 1 <;> simp <;> ring

private theorem p07_nonneg_eventually {f : ℝ → ℝ}
    (hf : HasDerivAt f 1 0) (hf0 : f 0 = 0) :
    ∀ᶠ z in nhds (0:ℝ), 0 ≤ z → 0 ≤ f z := by
  have hs : ∀ᶠ z in nhdsWithin (0:ℝ) (Set.Ioi 0),
      0 < z⁻¹ * (f z - f 0) := by
    have ht : ∀ᶠ y in nhds (1:ℝ), 0 < y := eventually_gt_nhds (by norm_num)
    have := hf.tendsto_slope_zero_right.eventually ht
    simpa [smul_eq_mul] using this
  have hs' := eventually_nhdsWithin_iff.mp hs
  filter_upwards [hs'] with z hz hznonneg
  rcases lt_or_eq_of_le hznonneg with hzpos | hz0
  · have hinv : 0 < z⁻¹ := inv_pos.mpr hzpos
    have hdiff : 0 < f z - f 0 :=
      (mul_pos_iff_of_pos_left hinv).mp (hz hzpos)
    rw [hf0] at hdiff
    linarith
  · subst z
    simp [hf0]

private theorem p07_scalar_bound (n : ℕ) {z S H e a b : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hS : 0 < S) (he : 0 ≤ e)
    (hHlo : (1-z)^n * S ≤ H) (hHhi : H ≤ (1+z)^n * S)
    (ha : |a| ≤ z) (hb : |b| ≤ z)
    (hsmall : 0 ≤ 1-(n+3:ℝ)*z)
    (hpolyhi : (1+z)^2 ≤ (1+(n+3:ℝ)*z)*(1-z)^n)
    (hpolylo : (1-(n+3:ℝ)*z)*(1+z)^n ≤ (1-z)^2) :
    |e*(1+a)/H*(1+b) - e/S| ≤ (n+3:ℝ)*z*(e/S) := by
  have h1z : 0 ≤ 1-z := by linarith
  have hpz : 0 ≤ 1+z := by linarith
  have hpowlo : 0 < (1-z)^n := pow_pos (by linarith) _
  have hpowhi : 0 ≤ (1+z)^n := pow_nonneg hpz _
  have hH : 0 < H := lt_of_lt_of_le (mul_pos hpowlo hS) hHlo
  have ha_lo : 1-z ≤ 1+a := by have := (abs_le.mp ha).1; linarith
  have ha_hi : 1+a ≤ 1+z := by have := (abs_le.mp ha).2; linarith
  have hb_lo : 1-z ≤ 1+b := by have := (abs_le.mp hb).1; linarith
  have hb_hi : 1+b ≤ 1+z := by have := (abs_le.mp hb).2; linarith
  have ha_nonneg : 0 ≤ 1+a := by linarith
  have hb_nonneg : 0 ≤ 1+b := by linarith
  have hAlo : (1-z)^2 ≤ (1+a)*(1+b) := by
    calc
      (1-z)^2 = (1-z)*(1-z) := by ring
      _ ≤ (1+a)*(1+b) := by gcongr
  have hAhi : (1+a)*(1+b) ≤ (1+z)^2 := by
    calc
      (1+a)*(1+b) ≤ (1+z)*(1+z) := by gcongr
      _ = (1+z)^2 := by ring
  have hratio_lo : (1-(n+3:ℝ)*z)/S ≤ ((1+a)*(1+b))/H := by
    apply (div_le_div_iff₀ hS hH).2
    calc
      (1-(n+3:ℝ)*z)*H ≤ (1-(n+3:ℝ)*z)*((1+z)^n*S) :=
        mul_le_mul_of_nonneg_left hHhi hsmall
      _ ≤ (1-z)^2*S := by
        calc
          _ = ((1-(n+3:ℝ)*z)*(1+z)^n)*S := by ring
          _ ≤ (1-z)^2*S := mul_le_mul_of_nonneg_right hpolylo hS.le
      _ ≤ ((1+a)*(1+b))*S := mul_le_mul_of_nonneg_right hAlo hS.le
  have hratio_hi : ((1+a)*(1+b))/H ≤ (1+(n+3:ℝ)*z)/S := by
    apply (div_le_div_iff₀ hH hS).2
    have hc : 0 ≤ 1+(n+3:ℝ)*z := by positivity
    calc
      ((1+a)*(1+b))*S ≤ (1+z)^2*S :=
        mul_le_mul_of_nonneg_right hAhi hS.le
      _ ≤ ((1+(n+3:ℝ)*z)*(1-z)^n)*S :=
        mul_le_mul_of_nonneg_right hpolyhi hS.le
      _ = (1+(n+3:ℝ)*z)*((1-z)^n*S) := by ring
      _ ≤ (1+(n+3:ℝ)*z)*H := mul_le_mul_of_nonneg_left hHlo hc
  apply abs_le.mpr
  constructor
  · have h := mul_le_mul_of_nonneg_left hratio_lo he
    have hnonneg : 0 ≤ (n+3:ℝ)*z*(e/S) := by positivity
    ring_nf at h ⊢
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hratio_hi he
    ring_nf at h ⊢
    nlinarith

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
  refine ⟨fun _ => 0, ?_, ?_⟩
  · simpa using Asymptotics.isBigO_zero (l := l) (fun t : ι => (u t)^2)
  have hS : 0 < p07ExpSum x := by
    unfold p07ExpSum
    apply Finset.sum_pos
    · intro i _
      exact Real.exp_pos _
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hnormpos : 0 < ‖(fun i : Fin n => p07ExactSoftmax x i)‖ := by
    have hi : 0 < p07ExactSoftmax x ⟨0, hn⟩ :=
      div_pos (Real.exp_pos _) hS
    exact lt_of_lt_of_le (norm_pos_iff.mpr (ne_of_gt hi))
      (norm_le_pi_norm (fun i : Fin n => p07ExactSoftmax x i) ⟨0, hn⟩)
  have hsmall_ev : ∀ᶠ t in l, 0 ≤ 1-(n+3:ℝ)*u t := by
    have hc : 0 < (n+3:ℝ) := by positivity
    have hlt : ∀ᶠ t in l, u t < 1/(n+3:ℝ) :=
      Filter.Tendsto.eventually_lt_const (by positivity) hu
    filter_upwards [hlt] with t ht
    have hmul := mul_lt_mul_of_pos_left ht hc
    have hdiv : (n+3:ℝ) * (1/(n+3:ℝ)) = 1 := by
      field_simp
    rw [hdiv] at hmul
    linarith
  have hu1_ev : ∀ᶠ t in l, u t < 1 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) hu
  have hpolyhi_ev : ∀ᶠ t in l,
      (1+u t)^2 ≤ (1+(n+3:ℝ)*u t)*(1-u t)^n := by
    have h := hu.eventually (p07_nonneg_eventually
      (p07_upper_poly_deriv n) (by simp))
    filter_upwards [h] with t ht
    have hu0 : 0 ≤ u t := (run t).unit_eq ▸ (run t).fp.u_nonneg
    exact sub_nonneg.mp (ht hu0)
  have hpolylo_ev : ∀ᶠ t in l,
      (1-(n+3:ℝ)*u t)*(1+u t)^n ≤ (1-u t)^2 := by
    have h := hu.eventually (p07_nonneg_eventually
      (p07_lower_poly_deriv n) (by simp))
    filter_upwards [h] with t ht
    have hu0 : 0 ≤ u t := (run t).unit_eq ▸ (run t).fp.u_nonneg
    exact sub_nonneg.mp (ht hu0)
  filter_upwards [hsmall_ev, hu1_ev, hpolyhi_ev, hpolylo_ev] with
    t hsmall hu1 hpolyhi hpolylo
  have hu0 : 0 ≤ u t := (run t).unit_eq ▸ (run t).fp.u_nonneg
  obtain ⟨hHlo, hHhi⟩ := p07_sum_bounds hn x (run t) hu1
  have hC : 0 ≤ (n+3:ℝ)*u t := by positivity
  have hnorm : ‖(fun i : Fin n =>
      p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i)‖ ≤
      (n+3:ℝ)*u t * ‖(fun i : Fin n => p07ExactSoftmax x i)‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).2
    intro i
    rw [Real.norm_eq_abs]
    have hi : 0 ≤ p07ExactSoftmax x i :=
      (div_pos (Real.exp_pos _) hS).le
    have hscalar :
        |p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i| ≤
          (n+3:ℝ)*u t*p07ExactSoftmax x i := by
      simpa [p07ComputedSoftmax, p07ComputedExp, p07ExactSoftmax] using
        (p07_scalar_bound n hu0 hu1 hS (Real.exp_pos _).le
          hHlo hHhi ((run t).expError_le i) (hdiv t i)
          hsmall hpolyhi hpolylo)
    exact hscalar.trans (mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hi] using
        (norm_le_pi_norm (fun j : Fin n => p07ExactSoftmax x j) i)) hC)
  have hquot := (div_le_iff₀ hnormpos).2
    (by simpa [mul_comm] using hnorm)
  simpa [mul_comm] using hquot

end VSCLReuse

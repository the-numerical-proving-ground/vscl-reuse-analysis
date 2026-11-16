import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

private def p07C : ℕ → ℝ
  | 0 => 0
  | n + 1 => 2 * p07C n + (n : ℝ) + 3

private theorem p07C_nonneg (n : ℕ) : 0 ≤ p07C n := by
  induction n with
  | zero => simp [p07C]
  | succ n ih => simp only [p07C]; positivity

private theorem p07_recursive_error
    (n : ℕ) (v e : Fin n → ℝ) (fp : StandardAddModel)
    (hu : fp.u ≤ 1) (he : ∀ i, 0 ≤ e i)
    (hv : ∀ i, |v i - e i| ≤ fp.u * e i) :
    |recursiveSum fp.fl_add n v - ∑ i, e i| ≤
      ((n : ℝ) * fp.u + p07C n * fp.u ^ 2) * ∑ i, e i := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
    let S : ℝ := ∑ i : Fin n, e i.castSucc
    let E : ℝ := e (Fin.last n)
    let R : ℝ := recursiveSum fp.fl_add n (fun i => v i.castSucc)
    let W : ℝ := v (Fin.last n)
    let U : ℝ := fp.u
    let A : ℝ := (n : ℝ) * U + p07C n * U ^ 2
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => he i.castSucc)
    have hE : 0 ≤ E := he (Fin.last n)
    have hU : 0 ≤ U := fp.u_nonneg
    have hA : 0 ≤ A := by
      dsimp [A]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hU)
        (mul_nonneg (p07C_nonneg n) (sq_nonneg U))
    have hD : |R - S| ≤ A * S := by
      exact ih (fun i => v i.castSucc) (fun i => e i.castSucc)
        (fun i => he i.castSucc) (fun i => hv i.castSucc)
    have hW : |W - E| ≤ U * E := hv (Fin.last n)
    have hsum : (∑ i : Fin (n+1), e i) = S + E := by
      simp only [Fin.sum_univ_castSucc, S, E]
    by_cases hn : n = 0
    · subst n
      have hbound : |v (Fin.last 0) - e (Fin.last 0)| ≤ fp.u * e (Fin.last 0) := hv _
      have hcoef : fp.u * e (Fin.last 0) ≤
          ((1 : ℝ) * fp.u + p07C 1 * fp.u ^ 2) * e (Fin.last 0) := by
        simp only [p07C]
        nlinarith [mul_nonneg (sq_nonneg fp.u) hE]
      simpa [recursiveSum, p07C] using hbound.trans hcoef
    · obtain ⟨d, hd, hfl⟩ := fp.model_add R W
      have hrec : recursiveSum fp.fl_add (n+1) v = (R+W)*(1+d) := by
        simp [recursiveSum, hn, R, W, hfl]
      have hdU : |d| ≤ U := hd
      have hR : |R| ≤ S + A*S := by
        calc |R| = |(R-S)+S| := by ring
          _ ≤ |R-S| + |S| := abs_add_le _ _
          _ ≤ A*S + S := by rw [abs_of_nonneg hS]; gcongr
          _ = S + A*S := by ring
      have hWabs : |W| ≤ E + U*E := by
        calc |W| = |(W-E)+E| := by ring
          _ ≤ |W-E| + |E| := abs_add_le _ _
          _ ≤ U*E + E := by rw [abs_of_nonneg hE]; gcongr
          _ = E + U*E := by ring
      have hRW : |R+W| ≤ (S+E)+A*S+U*E := by
        calc |R+W| ≤ |R|+|W| := abs_add_le _ _
          _ ≤ (S+A*S)+(E+U*E) := add_le_add hR hWabs
          _ = (S+E)+A*S+U*E := by ring
      have hraw : |(R+W)*(1+d)-(S+E)| ≤
          A*S+U*E+U*((S+E)+A*S+U*E) := by
        have hid : (R+W)*(1+d)-(S+E) = (R-S)+(W-E)+d*(R+W) := by ring
        rw [hid]
        calc |(R-S)+(W-E)+d*(R+W)|
            ≤ |R-S|+|W-E|+|d*(R+W)| := by
              calc _ ≤ |(R-S)+(W-E)| + |d*(R+W)| := abs_add_le _ _
                   _ ≤ _ := by gcongr; exact abs_add_le _ _
          _ ≤ A*S+U*E+U*((S+E)+A*S+U*E) := by
              rw [abs_mul]
              gcongr
      have hnum : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hfin : A*S+U*E+U*((S+E)+A*S+U*E) ≤
          (((n+1 : ℕ) : ℝ)*U + p07C (n+1)*U^2)*(S+E) := by
        dsimp [A]
        simp only [p07C]
        have hu3 : U^3 ≤ U^2 := by nlinarith [sq_nonneg U]
        -- Distribute into nonnegative coefficient inequalities.
        have hleft : (p07C n * U^2 + (n : ℝ)*U^2 + p07C n * U^3) * S ≤
            (2*p07C n + (n : ℝ) + 3)*U^2*S := by
          have hc := p07C_nonneg n
          nlinarith [mul_nonneg (mul_nonneg hc (sub_nonneg.mpr hu3)) hS]
        have hright : (2*U+U^2)*E ≤
            (((n : ℝ)+1)*U + (2*p07C n + (n : ℝ)+3)*U^2)*E := by
          have hc := p07C_nonneg n
          nlinarith [mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ (n : ℝ)-1) hU) hE,
            mul_nonneg (mul_nonneg (by nlinarith : 0 ≤ 2*p07C n+(n:ℝ)+2) (sq_nonneg U)) hE]
        calc
          _ = (((n:ℝ)+1)*U+(p07C n*U^2+(n:ℝ)*U^2+p07C n*U^3))*S
              + (2*U+U^2)*E := by ring
          _ ≤ (((n:ℝ)+1)*U+(2*p07C n+(n:ℝ)+3)*U^2)*S
              + (((n:ℝ)+1)*U+(2*p07C n+(n:ℝ)+3)*U^2)*E := by
                apply add_le_add
                · nlinarith [hleft]
                · exact hright
          _ ≤ (((n+1:ℕ):ℝ)*U+(2*p07C n+(n:ℝ)+3)*U^2)*(S+E) := by
                push_cast
                nlinarith [mul_nonneg hU hS]

      rw [hsum, hrec]
      exact hraw.trans hfin

private theorem p07_ratio_bound
    (N u a b q : ℝ) (hN : 0 ≤ N) (hu : 0 ≤ u) (hu4 : u ≤ 1/4)
    (ha : |a| ≤ u) (hb : |b| ≤ u)
    (hq : |q| ≤ (N+1/4)*u)
    (hsmall : (N+3)*(N+1/4)*u ≤ 1/4) :
    |(1+a)*(1+b)/(1+q)-1| ≤ (N+3)*u := by
  let B := (N+1/4)*u
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqB : -B ≤ q := by
    have := (abs_le.mp hq).1
    dsimp [B]
    linarith
  have hden : 0 < 1+q := by
    have hBsmall : B ≤ 1/4 := by
      have hfac : 1 ≤ N+3 := by linarith
      have := mul_le_mul_of_nonneg_right hfac hB
      dsimp [B] at *
      nlinarith
    linarith
  have hab : |a*b| ≤ u^2 := by
    rw [abs_mul]
    simpa [pow_two] using mul_le_mul ha hb (abs_nonneg _) hu
  have hnum : |a+b+a*b-q| ≤ (N+5/2)*u := by
    have htri : |a+b+a*b-q| ≤ |a|+|b|+|a*b|+|q| := by
      calc
        _ ≤ |a+b+a*b|+|q| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a+b+a*b) (-q)
        _ ≤ (|a|+|b|)+|a*b|+|q| := by
          gcongr
          calc |a+b+a*b| ≤ |a+b|+|a*b| := abs_add_le _ _
               _ ≤ (|a|+|b|)+|a*b| := by gcongr; exact abs_add_le _ _
    nlinarith [sq_nonneg u]
  have hcross : (N+3)*B*u ≤ u/4 := by
    have := mul_le_mul_of_nonneg_right hsmall hu
    dsimp [B]
    nlinarith
  have hdenmul : -(N+3)*u*B ≤ (N+3)*u*q := by
    have hc : 0 ≤ (N+3)*u := by positivity
    simpa only [mul_neg, neg_mul] using mul_le_mul_of_nonneg_left hqB hc
  have htarget : |a+b+a*b-q| ≤ (N+3)*u*(1+q) := by
    nlinarith
  have hident : (1+a)*(1+b)/(1+q)-1 = (a+b+a*b-q)/(1+q) := by
    field_simp
    ring
  rw [hident, abs_div, abs_of_pos hden]
  exact (div_le_iff₀ hden).2 htarget

private theorem p07_softmax_identity
    (S R E a b q : ℝ) (hS : S ≠ 0) (hden : 1+q ≠ 0)
    (hR : R = S*(1+q)) :
    E*(1+a)/R*(1+b)-E/S =
      (E/S)*((1+a)*(1+b)/(1+q)-1) := by
  subst R
  field_simp

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
  let C : ℝ := p07C n
  let K : ℝ := (n : ℝ) + C + 10
  have hC : 0 ≤ C := p07C_nonneg n
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [Nat.cast_nonneg (α := ℝ) n, hC]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKsq : K ≤ K ^ 2 := by nlinarith [mul_nonneg (le_of_lt hKpos) (sub_nonneg.mpr hK)]
  have hS : 0 < p07ExpSum x := by
    unfold p07ExpSum
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    positivity
  have hgnorm : 0 < ‖(fun i : Fin n => p07ExactSoftmax x i)‖ := by
    let i : Fin n := ⟨0, hn⟩
    have hi : 0 < p07ExactSoftmax x i := by
      unfold p07ExactSoftmax
      exact div_pos (Real.exp_pos _) hS
    have hle := norm_le_pi_norm (fun i : Fin n => p07ExactSoftmax x i) i
    exact lt_of_lt_of_le (norm_pos_iff.mpr (ne_of_gt hi)) hle
  have hev : ∀ᶠ t in l, u t < 1 / (4 * K ^ 2) := by
    exact hu.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (4 * K ^ 2)))
  refine ⟨(fun _ => 0), ?_, ?_⟩
  · exact Asymptotics.isBigO_zero _ _
  filter_upwards [hev] with t ht
  let U : ℝ := u t
  let R : ℝ := p07RecursiveComputedExpSum (run t)
  let S : ℝ := p07ExpSum x
  let q : ℝ := (R-S)/S
  have hU : 0 ≤ U := by
    dsimp [U]
    rw [← (run t).unit_eq]
    exact (run t).fp.u_nonneg
  have hscale : 4 * K ^ 2 * U ≤ 1 := by
    have hk : 0 < 4 * K ^ 2 := by positivity
    have := (lt_div_iff₀ hk).mp ht
    dsimp [U]
    nlinarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  have hU4 : U ≤ 1/4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hK2) hU]
  have hU1 : U ≤ 1 := by linarith
  have hCK : C ≤ K := by dsimp [K]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hCu : C * U ≤ 1/4 := by
    have hc2 : C ≤ K^2 := le_trans hCK hKsq
    have := mul_le_mul_of_nonneg_right hc2 hU
    nlinarith
  have hcoef1 : (n : ℝ) + 3 ≤ K := by dsimp [K]; nlinarith
  have hcoef2 : (n : ℝ) + 1/4 ≤ K := by dsimp [K]; nlinarith
  have hcoef0 : 0 ≤ (n : ℝ) + 1/4 := by positivity
  have hcoeff : ((n : ℝ)+3)*((n : ℝ)+1/4) ≤ K^2 := by
    have := mul_le_mul hcoef1 hcoef2 hcoef0 (le_of_lt hKpos)
    nlinarith
  have hsmall : ((n : ℝ)+3)*((n : ℝ)+1/4)*U ≤ 1/4 := by
    have := mul_le_mul_of_nonneg_right hcoeff hU
    nlinarith
  have hexp (i : Fin n) :
      |p07ComputedExp (run t) i - Real.exp (x i)| ≤ U * Real.exp (x i) := by
    unfold p07ComputedExp
    have he := (run t).expError_le i
    have hpos : 0 ≤ Real.exp (x i) := le_of_lt (Real.exp_pos _)
    calc
      |Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i)|
          = Real.exp (x i) * |(run t).expError i| := by
            rw [show Real.exp (x i) * (1 + (run t).expError i) - Real.exp (x i) =
              Real.exp (x i) * (run t).expError i by ring, abs_mul,
              abs_of_nonneg hpos]
      _ ≤ U * Real.exp (x i) := by
            simpa [U, mul_comm] using mul_le_mul_of_nonneg_left he hpos
  have hsum : |R-S| ≤ ((n : ℝ)*U+C*U^2)*S := by
    have hrec := p07_recursive_error n (p07ComputedExp (run t))
      (fun i => Real.exp (x i)) (run t).fp
      (by simpa [(run t).unit_eq, U] using hU1)
      (fun i => le_of_lt (Real.exp_pos _))
      (by intro i; simpa [(run t).unit_eq, U] using hexp i)
    simpa [R, S, C, U, p07RecursiveComputedExpSum, p07ExpSum, (run t).unit_eq] using hrec
  have hqraw : |q| ≤ (n : ℝ)*U+C*U^2 := by
    dsimp [q]
    rw [abs_div, abs_of_pos hS]
    apply (div_le_iff₀ hS).2
    simpa [R, S] using hsum
  have hq : |q| ≤ ((n : ℝ)+1/4)*U := by
    have hc2 := mul_le_mul_of_nonneg_right hCu hU
    nlinarith [hqraw]
  have hB : ((n : ℝ)+1/4)*U ≤ 1/4 := by
    have hfac : ((n : ℝ)+1/4) ≤ ((n : ℝ)+3) := by linarith
    have hn3 : 1 ≤ (n : ℝ)+3 := by exact_mod_cast (show 1 ≤ n+3 by omega)
    have hleft := mul_le_mul_of_nonneg_right hfac hU
    have hright := mul_le_mul_of_nonneg_right hn3 (mul_nonneg hcoef0 hU)
    nlinarith [hsmall]
  have hden : 0 < 1+q := by
    have := (abs_le.mp hq).1
    nlinarith
  have hReq : R = S*(1+q) := by
    have hS0 : S ≠ 0 := ne_of_gt hS
    dsimp [q]
    field_simp [hS0]
    ring
  have hpoint (i : Fin n) :
      ‖p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i‖ ≤
        ((n : ℝ)+3)*U * ‖p07ExactSoftmax x i‖ := by
    have ha : |(run t).expError i| ≤ U := by
      simpa [U, (run t).unit_eq] using (run t).expError_le i
    have hb : |divError t i| ≤ U := hdiv t i
    have hr := p07_ratio_bound (n : ℝ) U ((run t).expError i) (divError t i) q
      (Nat.cast_nonneg _) hU hU4 ha hb hq hsmall
    have hid := p07_softmax_identity S R (Real.exp (x i))
      ((run t).expError i) (divError t i) q (ne_of_gt hS) (ne_of_gt hden) hReq
    have heq : p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i =
        p07ExactSoftmax x i *
          ((1+(run t).expError i)*(1+divError t i)/(1+q)-1) := by
      simpa [p07ComputedSoftmax, p07ComputedExp, p07ExactSoftmax, R, S] using hid
    calc
      _ = ‖p07ExactSoftmax x i‖ *
            |(1+(run t).expError i)*(1+divError t i)/(1+q)-1| := by
              rw [heq, norm_mul]; simp only [Real.norm_eq_abs]
      _ ≤ ‖p07ExactSoftmax x i‖ * (((n : ℝ)+3)*U) :=
        mul_le_mul_of_nonneg_left hr (norm_nonneg _)
      _ = ((n : ℝ)+3)*U * ‖p07ExactSoftmax x i‖ := by ring
  have hnorm :
      ‖(fun i : Fin n => p07ComputedSoftmax (run t) (divError t) i -
        p07ExactSoftmax x i)‖ ≤
      ((n : ℝ)+3)*U * ‖(fun i : Fin n => p07ExactSoftmax x i)‖ := by
    have hc : 0 ≤ ((n : ℝ)+3)*U := by positivity
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).2
    intro i
    exact (hpoint i).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ i) hc)
  simpa [U, Nat.cast_add] using (div_le_iff₀ hgnorm).2 hnorm

end VSCLReuse

import VSCLReuse.P07.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p07_sum_nonneg {n : ℕ} (v : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i) : 0 ≤ ∑ i, v i := by
  exact Finset.sum_nonneg (fun i _ => hv i)

private lemma p07_recursive_envelope
    (fp : StandardAddModel) (u : ℝ) (hunit : fp.u = u)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (n : ℕ) (v w : Fin n → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hwlo : ∀ i, (1 - u) * v i ≤ w i)
    (hwhi : ∀ i, w i ≤ (1 + u) * v i) :
    (1 - u) ^ n * (∑ i, v i) ≤ recursiveSum fp.fl_add n w ∧
      recursiveSum fp.fl_add n w ≤ (1 + u) ^ n * (∑ i, v i) := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simpa [recursiveSum, Fin.sum_univ_one] using
        (show (1-u) * v 0 ≤ w 0 ∧ w 0 ≤ (1+u) * v 0 from
          ⟨hwlo 0, hwhi 0⟩)
    · have hrec := ih (fun i => v i.castSucc) (fun i => w i.castSucc)
          (fun i => hv i.castSucc) (fun i => hwlo i.castSucc)
          (fun i => hwhi i.castSucc)
      obtain ⟨hδ, hadd⟩ := fp.model_add
        (recursiveSum fp.fl_add n (fun i => w i.castSucc)) (w (Fin.last n))
      have hδlo : 1 - u ≤ 1 + hδ := by
        have := (abs_le.mp (hunit ▸ hadd.1)).1
        linarith
      have hδhi : 1 + hδ ≤ 1 + u := by
        have := (abs_le.mp (hunit ▸ hadd.1)).2
        linarith
      have hbase : 0 ≤ 1 - u := by linarith
      have hbase' : 0 ≤ 1 + u := by linarith
      have hsum : 0 ≤ ∑ i : Fin n, v i.castSucc :=
        p07_sum_nonneg _ (fun i => hv i.castSucc)
      have hlast : 0 ≤ v (Fin.last n) := hv _
      have hlowpow : (1-u)^(n+1) ≤ (1-u)^n := by
        rw [pow_succ]
        nlinarith [pow_nonneg hbase n]
      have hlowlast : (1-u)^(n+1) ≤ (1-u)^2 := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [show m + 1 + 1 = m + 2 by omega, pow_add]
        have hpow : (1-u)^m ≤ 1 := pow_le_one₀ hbase (by linarith)
        nlinarith [pow_nonneg hbase 2]
      have huppow : (1+u)^n ≤ (1+u)^(n+1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg hbase' n]
      have huplast : 1+u ≤ (1+u)^(n+1) := by
        rw [pow_succ]
        have hpow : 1 ≤ (1+u)^n := one_le_pow₀ (by linarith)
        nlinarith
      have huplast2 : (1+u)^2 ≤ (1+u)^(n+1) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [show m + 1 + 1 = m + 2 by omega, pow_add]
        have hpow : 1 ≤ (1+u)^m := one_le_pow₀ (by linarith)
        nlinarith [pow_nonneg hbase' 2]
      rw [Fin.sum_univ_castSucc]
      simp only [recursiveSum, dif_neg hn, hadd.2]
      constructor
      · have h0 : 0 ≤ (1-u)^n * (∑ i : Fin n, v i.castSucc) :=
          mul_nonneg (pow_nonneg hbase _) hsum
        have h1 : 0 ≤ w (Fin.last n) :=
          le_trans (mul_nonneg hbase hlast) (hwlo _)
        have hnonneg : 0 ≤ recursiveSum fp.fl_add n (fun i => w i.castSucc) +
            w (Fin.last n) := by linarith [hrec.1]
        calc
          (1-u)^(n+1) * ((∑ i : Fin n, v i.castSucc) + v (Fin.last n))
              ≤ (1-u)^(n+1) * (∑ i : Fin n, v i.castSucc) +
                  (1-u)^2 * v (Fin.last n) := by
                    rw [mul_add]
                    gcongr
          _ = ((1-u)^n * (∑ i : Fin n, v i.castSucc) +
                  (1-u) * v (Fin.last n)) * (1-u) := by
                    rw [pow_succ]
                    ring
          _ ≤ (recursiveSum fp.fl_add n (fun i => w i.castSucc) +
                  w (Fin.last n)) * (1-u) := by
                    gcongr
                    · exact hrec.1
                    · exact hwlo _
          _ ≤ (recursiveSum fp.fl_add n (fun i => w i.castSucc) + w (Fin.last n)) *
                  (1+hδ) := by gcongr
      · have hnonneg : 0 ≤ recursiveSum fp.fl_add n (fun i => w i.castSucc) +
            w (Fin.last n) := by
          have : 0 ≤ (1-u)^n * (∑ i : Fin n, v i.castSucc) :=
            mul_nonneg (pow_nonneg hbase _) hsum
          have : 0 ≤ w (Fin.last n) :=
            le_trans (mul_nonneg hbase hlast) (hwlo _)
          linarith [hrec.1]
        calc
          (recursiveSum fp.fl_add n (fun i => w i.castSucc) + w (Fin.last n)) *
              (1+hδ)
              ≤ (recursiveSum fp.fl_add n (fun i => w i.castSucc) + w (Fin.last n)) *
                  (1+u) := by gcongr
          _ ≤ ((1+u)^n * (∑ i : Fin n, v i.castSucc) +
                  (1+u) * v (Fin.last n)) * (1+u) := by
                  gcongr
                  · exact hrec.2
                  · exact hwhi _
          _ = (1+u)^(n+1) * (∑ i : Fin n, v i.castSucc) +
                  (1+u)^2 * v (Fin.last n) := by
                    rw [pow_succ]
                    ring
          _ ≤ (1+u)^(n+1) *
                ((∑ i : Fin n, v i.castSucc) + v (Fin.last n)) := by
                  rw [mul_add]
                  gcongr

private lemma p07_nat_le_four_pow (n : ℕ) : n ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 4 ^ n := pow_pos (by omega) _
    omega

private lemma p07_pow_upper (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + u) ^ n ≤ 1 + (n : ℝ) * u + (4 : ℝ) ^ n * u ^ 2 := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    have hC : (n : ℝ) ≤ (4 : ℝ)^n := by
      exact_mod_cast p07_nat_le_four_pow n
    have hu3 : u ^ 3 ≤ u ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hu1 (sq_nonneg u)]
    have hC0 : 0 ≤ (4 : ℝ)^n := pow_nonneg (by norm_num) _
    calc
      (1 + u) ^ (n+1) = (1+u)^n * (1+u) := by rw [pow_succ]
      _ ≤ (1 + (n : ℝ)*u + (4 : ℝ)^n*u^2) * (1+u) := by
        exact mul_le_mul_of_nonneg_right ih (by linarith)
      _ = 1 + (↑(n+1) : ℝ)*u + ((4 : ℝ)^n + n)*u^2 + (4 : ℝ)^n*u^3 := by
        push_cast
        ring
      _ ≤ 1 + (↑(n+1) : ℝ)*u + (2*(4 : ℝ)^n + n)*u^2 := by
        have := mul_le_mul_of_nonneg_left hu3 hC0
        nlinarith
      _ ≤ 1 + (↑(n+1) : ℝ)*u + (4 : ℝ)^(n+1)*u^2 := by
        rw [pow_succ]
        have hcoeff : 2*(4:ℝ)^n + (n:ℝ) ≤ (4:ℝ)^n * 4 := by linarith
        gcongr
        simpa [pow_succ] using hcoeff

private lemma p07_pow_lower (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - (n : ℝ)*u ≤ (1-u)^n := by
  have h := one_add_mul_le_pow (a := -u) (by linarith : (-2 : ℝ) ≤ -u) n
  convert h using 1 <;> ring

private lemma p07_sum_error {n : ℕ} (x : Fin n → ℝ) (u : ℝ)
    (run : P07BasicSumExecution x u) (hu1 : u ≤ 1) :
    |p07RecursiveComputedExpSum run - p07ExpSum x| ≤
      ((n : ℝ)*u + (4:ℝ)^n*u^2) * p07ExpSum x ∧
    (1-(n:ℝ)*u) * p07ExpSum x ≤ p07RecursiveComputedExpSum run := by
  have hu0 : 0 ≤ u := run.unit_eq ▸ run.fp.u_nonneg
  have henv := p07_recursive_envelope run.fp u run.unit_eq hu0 hu1 n
    (fun i => Real.exp (x i)) (p07ComputedExp run)
    (fun i => (Real.exp_pos (x i)).le)
    (fun i => by
      have he := (abs_le.mp (run.expError_le i)).1
      unfold p07ComputedExp
      calc
        (1-u) * Real.exp (x i) = Real.exp (x i) * (1-u) := by ring
        _ ≤ Real.exp (x i) * (1+run.expError i) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
    (fun i => by
      have he := (abs_le.mp (run.expError_le i)).2
      unfold p07ComputedExp
      calc
        Real.exp (x i) * (1+run.expError i) ≤ Real.exp (x i) * (1+u) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = (1+u) * Real.exp (x i) := by ring)
  have hs0 : 0 ≤ p07ExpSum x := by
    unfold p07ExpSum
    exact Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le)
  have hlow : (1-(n:ℝ)*u)*p07ExpSum x ≤ p07RecursiveComputedExpSum run := by
    calc
      _ ≤ (1-u)^n*p07ExpSum x := by
        exact mul_le_mul_of_nonneg_right (p07_pow_lower n hu0 hu1) hs0
      _ ≤ p07RecursiveComputedExpSum run := by
        simpa [p07ExpSum, p07RecursiveComputedExpSum] using henv.1
  have hupp : p07RecursiveComputedExpSum run ≤
      (1+(n:ℝ)*u+(4:ℝ)^n*u^2)*p07ExpSum x := by
    calc
      _ ≤ (1+u)^n*p07ExpSum x := by
        simpa [p07ExpSum, p07RecursiveComputedExpSum] using henv.2
      _ ≤ _ := mul_le_mul_of_nonneg_right (p07_pow_upper n hu0 hu1) hs0
  constructor
  · apply abs_le.mpr
    constructor
    · have hnonneg : 0 ≤ (4:ℝ)^n*u^2*p07ExpSum x := by positivity
      nlinarith
    · nlinarith
  · exact hlow

private lemma p07_scalar_bound
    (N C s r a e d u : ℝ)
    (hN : 0 ≤ N) (hC : 0 ≤ C) (hs : 0 < s) (ha : 0 ≤ a)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hsmall : N*u ≤ 1/2)
    (he : |e| ≤ u) (hd : |d| ≤ u)
    (herr : |r-s| ≤ (N*u+C*u^2)*s)
    (hlow : (1-N*u)*s ≤ r) :
    |a*(1+e)/r*(1+d)-a/s| ≤
      (a/s)*((N+3)*u+((C+1)*(1+2*N)+2*N*(N+2))*u^2) := by
  have hrhalf : s/2 ≤ r := by
    calc
      s/2 = (1/2:ℝ)*s := by ring
      _ ≤ (1-N*u)*s :=
        mul_le_mul_of_nonneg_right (by linarith) hs.le
      _ ≤ r := hlow
  have hr : 0 < r := by linarith
  have hs2r : s ≤ 2*r := by linarith
  have hnu : 0 ≤ N*u := mul_nonneg hN hu0
  have hsD : s ≤ r*(1+2*N*u) := by
    have hmul : N*u*s ≤ N*u*(2*r) :=
      mul_le_mul_of_nonneg_left hs2r hnu
    nlinarith [hlow]
  have hed : |e*d| ≤ u^2 := by
    rw [abs_mul]
    calc
      |e| * |d| ≤ u * |d| := mul_le_mul_of_nonneg_right he (abs_nonneg _)
      _ ≤ u*u := mul_le_mul_of_nonneg_left hd hu0
      _ = u^2 := by ring
  have hlocal : |e+d+e*d| ≤ 2*u+u^2 := by
    have h1 := abs_add_le (e+d) (e*d)
    have h2 := abs_add_le e d
    linarith
  let A : ℝ := (N+2)*u+(C+1)*u^2
  let D : ℝ := 1+2*N*u
  let K : ℝ := (C+1)*(1+2*N)+2*N*(N+2)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hnum : |s*(1+e)*(1+d)-r| ≤ s*A := by
    calc
      |s*(1+e)*(1+d)-r| = |s*(e+d+e*d)-(r-s)| := by
        congr 1
        ring
      _ ≤ |s*(e+d+e*d)|+|s-r| := by
        simpa using abs_sub_le (s*(e+d+e*d)) 0 (r-s)
      _ = |s*(e+d+e*d)|+|r-s| := by rw [abs_sub_comm s r]
      _ ≤ s*(2*u+u^2)+(N*u+C*u^2)*s := by
        rw [abs_mul, abs_of_pos hs]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlocal hs.le) herr
      _ = s*A := by dsimp [A]; ring
  have hratio : |(s*(1+e)*(1+d)-r)/r| ≤ A*D := by
    rw [abs_div, abs_of_pos hr]
    apply (div_le_iff₀ hr).2
    calc
      |s*(1+e)*(1+d)-r| ≤ s*A := hnum
      _ ≤ (r*D)*A := mul_le_mul_of_nonneg_right hsD hA0
      _ = A*D*r := by ring
  have hpoly : A*D ≤ (N+3)*u+K*u^2 := by
    have hident : (N+3)*u+K*u^2-A*D =
        u+2*N*(C+1)*u^2*(1-u) := by dsimp [A,D,K]; ring
    have hnonneg : 0 ≤ u+2*N*(C+1)*u^2*(1-u) := by
      have : 0 ≤ 1-u := by linarith
      positivity
    linarith
  have hid : a*(1+e)/r*(1+d)-a/s =
      (a/s)*((s*(1+e)*(1+d)-r)/r) := by
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg ha hs.le)]
  exact (mul_le_mul_of_nonneg_left (hratio.trans hpoly) (div_nonneg ha hs.le))

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
  let N : ℝ := n
  let C : ℝ := (4:ℝ)^n
  let K : ℝ := (C+1)*(1+2*N)+2*N*(N+2)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hN : 0 ≤ N := hNpos.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : 0 < p07ExpSum x := by
    unfold p07ExpSum
    exact Finset.sum_pos (fun i _ => Real.exp_pos (x i))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have heps : (0:ℝ) < 1/(2*N) := by positivity
  have hev1 : ∀ᶠ t in l, u t ≤ 1 := hu.eventually_le_const (by norm_num)
  have hev2 : ∀ᶠ t in l, u t ≤ 1/(2*N) := hu.eventually_le_const heps
  refine ⟨fun t => K*(u t)^2,
    Asymptotics.isBigO_const_mul_self K (fun t => (u t)^2) l, ?_⟩
  filter_upwards [hev1, hev2] with t hut1 hut2
  have hu0 : 0 ≤ u t := (run t).unit_eq ▸ (run t).fp.u_nonneg
  have hsmall : N*u t ≤ 1/2 := by
    calc
      N*u t ≤ N*(1/(2*N)) := mul_le_mul_of_nonneg_left hut2 hN
      _ = 1/2 := by field_simp
  have hsum := p07_sum_error x (u t) (run t) hut1
  let g : Fin n → ℝ := fun i => p07ExactSoftmax x i
  let diff : Fin n → ℝ := fun i =>
    p07ComputedSoftmax (run t) (divError t) i - p07ExactSoftmax x i
  let B : ℝ := (N+3)*u t+K*(u t)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgpos : 0 < ‖g‖ := by
    let i : Fin n := ⟨0, hn⟩
    have hgi : 0 < g i := by
      dsimp [g, p07ExactSoftmax]
      exact div_pos (Real.exp_pos _) hs
    have hle : ‖g i‖ ≤ ‖g‖ := norm_le_pi_norm g i
    rw [Real.norm_eq_abs, abs_of_pos hgi] at hle
    exact lt_of_lt_of_le hgi hle
  have hdiff : ‖diff‖ ≤ B*‖g‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg g))).2
    intro i
    have hcoord := p07_scalar_bound N C (p07ExpSum x)
      (p07RecursiveComputedExpSum (run t)) (Real.exp (x i))
      ((run t).expError i) (divError t i) (u t)
      hN hC hs (Real.exp_pos _).le hu0 hut1 hsmall
      ((run t).expError_le i) (hdiv t i) hsum.1 hsum.2
    have hgi : 0 ≤ g i := by
      dsimp [g, p07ExactSoftmax]
      exact div_nonneg (Real.exp_pos _).le hs.le
    have hgi_le : g i ≤ ‖g‖ := by
      have h := norm_le_pi_norm g i
      simpa [Real.norm_eq_abs, abs_of_nonneg hgi] using h
    have hpoint : |diff i| ≤ g i * B := by
      simpa only [diff, g, B, p07ComputedSoftmax, p07ExactSoftmax,
        p07ComputedExp, N, C, K] using hcoord
    calc
      ‖diff i‖ = |diff i| := Real.norm_eq_abs _
      _ ≤ g i * B := hpoint
      _ ≤ ‖g‖ * B := mul_le_mul_of_nonneg_right hgi_le hB
      _ = B * ‖g‖ := by ring
  change ‖diff‖ / ‖g‖ ≤ (n+3:ℝ)*u t+|K*(u t)^2|
  rw [abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]
  change ‖diff‖ / ‖g‖ ≤ B
  exact (div_le_iff₀ hgpos).2 (by nlinarith [hdiff])

end VSCLReuse

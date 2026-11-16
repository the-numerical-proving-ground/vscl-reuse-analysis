import VSCLReuse.P18.Definitions

namespace VSCLReuse

set_option maxHeartbeats 2000000

private def p18CoeffGood (u : ℝ) (k : ℕ) (c : ℝ) : Prop :=
  1 - (k : ℝ) * u ≤ c ∧ c ≤ 1 / (1 - (k : ℝ) * u)

private theorem p18_coeff_good_zero (u : ℝ) : p18CoeffGood u 0 1 := by
  simp [p18CoeffGood]

private theorem p18_coeff_good_mul (u : ℝ) (k : ℕ) (c δ : ℝ)
    (hu : 0 ≤ u) (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hc : p18CoeffGood u k c) (hδ : |δ| ≤ u) :
    p18CoeffGood u (k + 1) (c * (1 + δ)) := by
  unfold p18CoeffGood at *
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1
  have hδhi : δ ≤ u := (abs_le.mp hδ).2
  have hku : (k : ℝ) * u < 1 := by
    have : (k : ℝ) * u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      push_cast; nlinarith
    linarith
  have hp : 0 < 1 - (k : ℝ) * u := by linarith
  have hp' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have hcpos : 0 ≤ c := by nlinarith [hc.1]
  have hfac : 0 ≤ 1 + δ := by
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have hu1 : u < 1 := by
      nlinarith [mul_nonneg (show 0 ≤ ((k + 1 : ℕ) : ℝ) - 1 by linarith) hu]
    linarith
  have hu1 : u < 1 := by
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith [mul_nonneg (show 0 ≤ ((k + 1 : ℕ) : ℝ) - 1 by linarith) hu]
  constructor
  · have h : (1 - (k : ℝ) * u) * (1 - u) ≤ c * (1 + δ) := by
      have h1 : (1 - (k : ℝ) * u) * (1 - u) ≤ c * (1 - u) := by
        exact mul_le_mul_of_nonneg_right hc.1 (by linarith)
      have h2 : c * (1 - u) ≤ c * (1 + δ) := by nlinarith
      linarith
    push_cast at *
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * u by positivity) hu]
  · have h : c * (1 + δ) ≤ (1 / (1 - (k : ℝ) * u)) * (1 + u) := by
      nlinarith [mul_nonneg (show 0 ≤ (1 / (1 - (k : ℝ) * u)) - c by linarith) hfac]
    apply (le_div_iff₀ hp').2
    have hrec : (1 / (1 - (k : ℝ) * u)) * (1 - (k : ℝ) * u) = 1 := by field_simp
    have hnon : 0 ≤ 1 + u := by positivity
    have hkey : (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤ 1 - (k : ℝ) * u := by
      push_cast
      nlinarith [sq_nonneg u]
    have := mul_le_mul_of_nonneg_left hkey (show 0 ≤ 1 / (1 - (k : ℝ) * u) by positivity)
    push_cast at *
    nlinarith

private theorem p18_coeff_good_div (u : ℝ) (k : ℕ) (c δ : ℝ)
    (hu : 0 ≤ u) (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hc : p18CoeffGood u k c) (hδ : |δ| ≤ u) :
    p18CoeffGood u (k + 1) (c / (1 + δ)) := by
  unfold p18CoeffGood at *
  have hδlo : -u ≤ δ := (abs_le.mp hδ).1
  have hδhi : δ ≤ u := (abs_le.mp hδ).2
  have hden : 0 < 1 + δ := by
    have h1 : u < 1 := by
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith [mul_nonneg (show 0 ≤ ((k + 1 : ℕ) : ℝ) - 1 by linarith) hu]
    linarith
  have hp : 0 < 1 - (k : ℝ) * u := by
    push_cast at hk
    have : 0 ≤ u := hu
    nlinarith
  have hp' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  constructor
  · apply (le_div_iff₀ hden).2
    have hc0 : 0 ≤ c := by linarith [hc.1]
    have h : (1 - ((k + 1 : ℕ) : ℝ) * u) * (1 + δ) ≤
        (1 - (k : ℝ) * u) * (1 + u) := by
      have h0 : 0 ≤ 1 - ((k + 1 : ℕ) : ℝ) * u := le_of_lt hp'
      have hleft := mul_nonneg h0 (show 0 ≤ u - δ by linarith)
      have hright := mul_nonneg (show 0 ≤ u by exact hu)
        (show 0 ≤ 1 + u by positivity)
      push_cast at *
      nlinarith
    push_cast at *
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * u by positivity) hu]
  · apply (div_le_iff₀ hden).2
    have hrec : (1 / (1 - (k : ℝ) * u)) * (1 - (k : ℝ) * u) = 1 := by field_simp
    have hkey : 1 - ((k + 1 : ℕ) : ℝ) * u ≤
        (1 - (k : ℝ) * u) * (1 - u) := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) * u by positivity) hu]
    have hmul := mul_le_mul_of_nonneg_left hkey (show 0 ≤ 1 / (1 - (k : ℝ) * u) by positivity)
    have h : c ≤ (1 + δ) / (1 - ((k + 1 : ℕ) : ℝ) * u) := by
      apply (le_div_iff₀ hp').2
      nlinarith
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

private theorem p18_coeff_good_mono (u : ℝ) (k l : ℕ) (c : ℝ)
    (hu : 0 ≤ u) (hkl : k ≤ l) (hl : (l : ℝ) * u < 1)
    (hc : p18CoeffGood u k c) : p18CoeffGood u l c := by
  unfold p18CoeffGood at *
  have hkreal : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
  have hku : (k : ℝ) * u ≤ (l : ℝ) * u := mul_le_mul_of_nonneg_right hkreal hu
  have hkp : 0 < 1 - (k : ℝ) * u := by linarith
  have hlp : 0 < 1 - (l : ℝ) * u := by linarith
  constructor
  · linarith [hc.1]
  · calc
      c ≤ 1 / (1 - (k : ℝ) * u) := hc.2
      _ ≤ 1 / (1 - (l : ℝ) * u) := by
        apply one_div_le_one_div_of_le hlp
        linarith

private theorem p18_coeff_good_abs (u : ℝ) (k : ℕ) (c : ℝ)
    (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1)
    (hc : p18CoeffGood u k c) : |c - 1| ≤ p18Gamma u k := by
  unfold p18CoeffGood at hc
  unfold p18Gamma
  have hku : 0 ≤ (k : ℝ) * u := by positivity
  have hp : 0 < 1 - (k : ℝ) * u := by linarith
  have hrec : 1 / (1 - (k : ℝ) * u) - 1 =
      (k : ℝ) * u / (1 - (k : ℝ) * u) := by field_simp; ring
  rw [abs_le]
  constructor
  · have hquot : (k : ℝ) * u ≤ (k : ℝ) * u / (1 - (k : ℝ) * u) := by
      apply (le_div_iff₀ hp).2
      nlinarith [mul_nonneg hku hku]
    linarith [hc.1]
  · linarith [hc.2]

private theorem p18_rounded_fold_stable (fp : P18FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (b : ℝ)
    (hk : P18GammaValid fp.u k) :
    ∃ (r : ℝ) (c : Fin k → ℝ),
      p18CoeffGood fp.u k r ∧
      (∀ t, p18CoeffGood fp.u k (c t)) ∧
      b =
        (Fin.foldl k (fun s t => fp.fl_sub s (fp.fl_mul (a t) (x t))) b) * r +
          ∑ t : Fin k, a t * x t * c t := by
  induction k with
  | zero =>
      refine ⟨1, fun t => t.elim0, p18_coeff_good_zero fp.u, ?_, ?_⟩
      · intro t; exact t.elim0
      · simp
  | succ k ih =>
      have hk' : P18GammaValid fp.u k := by
        unfold P18GammaValid at *
        have hnon : 0 ≤ fp.u := fp.u_nonneg
        push_cast at hk
        nlinarith
      let aa : Fin k → ℝ := fun t => a t.castSucc
      let xx : Fin k → ℝ := fun t => x t.castSucc
      obtain ⟨r, c, hr, hc, heq⟩ := ih aa xx hk'
      let s : ℝ := Fin.foldl k
        (fun v t => fp.fl_sub v (fp.fl_mul (aa t) (xx t))) b
      obtain ⟨δm, hδm, hm⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨δs, hδs, hs⟩ := fp.model_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      let r' := r / (1 + δs)
      let c' : Fin (k + 1) → ℝ :=
        Fin.snoc c (r * (1 + δm))
      refine ⟨r', c', ?_, ?_, ?_⟩
      · exact p18_coeff_good_div fp.u k r δs fp.u_nonneg hk hr hδs
      · intro t
        refine Fin.lastCases ?_ ?_ t
        · simpa [c'] using
            p18_coeff_good_mul fp.u k r δm fp.u_nonneg hk hr hδm
        · intro t
          simpa [c'] using
            p18_coeff_good_mono fp.u k (k + 1) (c t) fp.u_nonneg
              (Nat.le_succ k) hk (hc t)
      · rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
        simp only [c', Fin.snoc_castSucc, Fin.snoc_last]
        change b = fp.fl_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) * r' +
          ((∑ t : Fin k, a t.castSucc * x t.castSucc * c t) +
            a (Fin.last k) * x (Fin.last k) * (r * (1 + δm)))
        rw [hs, hm]
        have hden : 1 + δs ≠ 0 := by
          have h1 : fp.u < 1 := by
            unfold P18GammaValid at hk
            have hle : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
            nlinarith [mul_nonneg (show 0 ≤ ((k + 1 : ℕ) : ℝ) - 1 by linarith) fp.u_nonneg]
          have := (abs_le.mp hδs).1
          linarith
        dsimp [r']
        field_simp [hden]
        dsimp [aa, xx, s] at heq
        nlinarith [heq]

private theorem p18_rounded_solve_row (fp : P18FPModel) (n k : ℕ)
    (a x : Fin k → ℝ) (b diag sol : ℝ)
    (hvalid : P18GammaValid fp.u n) (hk : k + 1 ≤ n)
    (hdiag : diag ≠ 0)
    (hsol : sol = fp.fl_div
      (Fin.foldl k (fun s t => fp.fl_sub s (fp.fl_mul (a t) (x t))) b) diag) :
    ∃ (cd : ℝ) (c : Fin k → ℝ),
      |cd - 1| ≤ p18Gamma fp.u n ∧
      (∀ t, |c t - 1| ≤ p18Gamma fp.u n) ∧
      b = diag * sol * cd + ∑ t : Fin k, a t * x t * c t := by
  have hkvalid : P18GammaValid fp.u k := by
    unfold P18GammaValid at *
    have hr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_trans (Nat.le_succ k) hk)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - k by linarith) fp.u_nonneg]
  obtain ⟨r, c, hr, hc, heq⟩ := p18_rounded_fold_stable fp k a x b hkvalid
  let s := Fin.foldl k (fun v t => fp.fl_sub v (fp.fl_mul (a t) (x t))) b
  obtain ⟨δ, hδ, hfl⟩ := fp.model_div s diag hdiag
  let cd := r / (1 + δ)
  have hk1 : ((k + 1 : ℕ) : ℝ) * fp.u < 1 := by
    unfold P18GammaValid at hvalid
    have hr : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - (k + 1 : ℕ) by linarith) fp.u_nonneg]
  have hdn : 1 + δ ≠ 0 := by
    have hu1 : fp.u < 1 := by
      have hr : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith [mul_nonneg (show 0 ≤ ((k + 1 : ℕ) : ℝ) - 1 by linarith) fp.u_nonneg]
    have := (abs_le.mp hδ).1
    linarith
  have hgood : p18CoeffGood fp.u (k + 1) cd :=
    p18_coeff_good_div fp.u k r δ fp.u_nonneg hk1 hr hδ
  have hgdn : p18CoeffGood fp.u n cd :=
    p18_coeff_good_mono fp.u (k + 1) n cd fp.u_nonneg hk hvalid hgood
  refine ⟨cd, c, p18_coeff_good_abs fp.u n cd fp.u_nonneg hvalid hgdn, ?_, ?_⟩
  · intro t
    have hgood' : p18CoeffGood fp.u n (c t) :=
      p18_coeff_good_mono fp.u k n (c t) fp.u_nonneg
        (Nat.le_trans (Nat.le_succ k) hk) hvalid (hc t)
    exact p18_coeff_good_abs fp.u n (c t) fp.u_nonneg hvalid hgood'
  · rw [hfl] at hsol
    dsimp [cd]
    have hcancel : diag * (s / diag * (1 + δ)) * (r / (1 + δ)) = s * r := by
      field_simp [hdiag, hdn]
    rw [hsol, hcancel]
    nlinarith [heq]

private noncomputable def p18ForwardRow (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl i.val
      (fun s t => fp.fl_sub s
        (fp.fl_mul (L i ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
      (b i)) (L i i)

private theorem p18_forward_row_congr (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b x y : Fin n → ℝ) (i : Fin n)
    (hxy : ∀ j : Fin n, j.val < i.val → x j = y j) :
    p18ForwardRow fp n L b x i = p18ForwardRow fp n L b y i := by
  unfold p18ForwardRow
  have hf :
      (fun s (t : Fin i.val) => fp.fl_sub s
        (fp.fl_mul (L i ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩))) =
      (fun s (t : Fin i.val) => fp.fl_sub s
        (fp.fl_mul (L i ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩))) := by
    funext s t
    have ht : (⟨t.val, by omega⟩ : Fin n).val < i.val := t.isLt
    rw [hxy _ ht]
  rw [hf]

private theorem p18_forward_steps_properties (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := p18ForwardSubSteps fp n L b k hk x
      (∀ i : Fin n, i.val < n - k → y i = x i) ∧
      (∀ i : Fin n, n - k ≤ i.val → y i = p18ForwardRow fp n L b y i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro i hi; rfl
      · intro i hi; omega
  | succ k ih =>
      intro hk x
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) => fp.fl_sub acc
          (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hstep : p18ForwardSubSteps fp n L b (k + 1) hk x =
          p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' := by
        rfl
      let y := p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      obtain ⟨hprev, hrows⟩ := ih (Nat.le_of_succ_le hk) x'
      rw [hstep]
      constructor
      · intro i hi
        have hi' : i.val < n - k := by omega
        rw [hprev i hi']
        have hne : i ≠ ik := by
          intro heq
          subst i
          dsimp [ik] at hi
          omega
        simp [x', Function.update_of_ne hne]
      · intro i hi
        by_cases hlate : n - k ≤ i.val
        · exact hrows i hlate
        · have hieq : i = ik := by
            apply Fin.ext
            dsimp [ik]
            omega
          subst i
          have hik : ik.val < n - k := by dsimp [ik]; omega
          have hyik : y ik = fp.fl_div s (L ik ik) := by
            simpa only [y, x', Function.update_self] using hprev ik hik
          have hxy : ∀ j : Fin n, j.val < ik.val → x j = y j := by
            intro j hj
            have hj' : j.val < n - k := by dsimp [ik] at hj; omega
            have hne : j ≠ ik := by
              intro heq; subst j; exact (Nat.lt_irrefl _) hj
            calc
              x j = x' j := by simp [x', Function.update_of_ne hne]
              _ = y j := (hprev j hj').symm
          change y ik = p18ForwardRow fp n L b y ik
          rw [hyik]
          have hrow := p18_forward_row_congr fp n L b x y ik hxy
          rw [← hrow]
          unfold p18ForwardRow
          congr 1

private noncomputable def p18BackRow (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl (n - i.val - 1)
      (fun s t => fp.fl_sub s
        (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
          (x ⟨i.val + 1 + t.val, by omega⟩)))
      (b i)) (U i i)

private theorem p18_back_row_congr (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b x y : Fin n → ℝ) (i : Fin n)
    (hxy : ∀ j : Fin n, i.val < j.val → x j = y j) :
    p18BackRow fp n U b x i = p18BackRow fp n U b y i := by
  unfold p18BackRow
  have hf :
      (fun s (t : Fin (n - i.val - 1)) => fp.fl_sub s
        (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
          (x ⟨i.val + 1 + t.val, by omega⟩))) =
      (fun s (t : Fin (n - i.val - 1)) => fp.fl_sub s
        (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
          (y ⟨i.val + 1 + t.val, by omega⟩))) := by
    funext s t
    rw [hxy _ (by change i.val < i.val + 1 + t.val; omega)]
  rw [hf]

private theorem p18_back_steps_properties (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := p18BackSubSteps fp n U b k hk x
      (∀ i : Fin n, k ≤ i.val → y i = x i) ∧
      (∀ i : Fin n, i.val < k → y i = p18BackRow fp n U b y i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro i hi; rfl
      · intro i hi; omega
  | succ k ih =>
      intro hk x
      let ik : Fin n := ⟨k, hk⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) => fp.fl_sub acc
          (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
            (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hstep : p18BackSubSteps fp n U b (k + 1) hk x =
          p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' := by
        rfl
      let y := p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      obtain ⟨hprev, hrows⟩ := ih (Nat.le_of_succ_le hk) x'
      rw [hstep]
      constructor
      · intro i hi
        have hi' : k ≤ i.val := by omega
        rw [hprev i hi']
        have hne : i ≠ ik := by
          intro heq; subst i; dsimp [ik] at hi; omega
        simp [x', Function.update_of_ne hne]
      · intro i hi
        by_cases hbefore : i.val < k
        · exact hrows i hbefore
        · have hieq : i = ik := by
            apply Fin.ext
            dsimp [ik]
            omega
          subst i
          have hik : k ≤ ik.val := by dsimp [ik]; omega
          have hyik : y ik = fp.fl_div s (U ik ik) := by
            simpa only [y, x', Function.update_self] using hprev ik hik
          have hxy : ∀ j : Fin n, ik.val < j.val → x j = y j := by
            intro j hj
            have hj' : k ≤ j.val := by dsimp [ik] at hj; omega
            have hne : j ≠ ik := by
              intro heq; subst j; exact (Nat.lt_irrefl _) hj
            calc
              x j = x' j := by simp [x', Function.update_of_ne hne]
              _ = y j := (hprev j hj').symm
          change y ik = p18BackRow fp n U b y ik
          rw [hyik]
          have hrow := p18_back_row_congr fp n U b x y ik hxy
          rw [← hrow]
          unfold p18BackRow
          congr 1

private theorem p18_sum_split (n : ℕ) (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i +
        ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ := by
  let g : ℕ → ℝ := fun t => if h : t < n then f ⟨t, h⟩ else 0
  have hbase : (∑ j : Fin n, f j) = ∑ t ∈ Finset.range n, g t := by
    simpa [g] using (Finset.sum_fin_eq_sum_range f)
  have hlow : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
      ∑ t ∈ Finset.range i.val, g t := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    have hti : t < i.val := Finset.mem_range.mp ht
    have htn : t < n := by omega
    simp [g, hti, htn]
  have hhigh : (∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩) =
      ∑ t ∈ Finset.range (n - i.val - 1), g (i.val + 1 + t) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    have hti : t < n - i.val - 1 := Finset.mem_range.mp ht
    have htn : i.val + 1 + t < n := by omega
    simp [g, hti, htn]
  have hcenter : g i.val = f i := by simp [g, i.isLt]
  have hn : n = i.val + 1 + (n - i.val - 1) := by omega
  rw [hbase, hlow, hhigh]
  conv_lhs => rw [hn, Finset.sum_range_add, Finset.sum_range_succ]
  simp [hcenter, Nat.add_assoc]

private theorem p18_forward_row_error (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hvalid : P18GammaValid fp.u n) (hdiag : L i i ≠ 0)
    (hlower : ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hrow : x i = p18ForwardRow fp n L b x i) :
    ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p18Gamma fp.u n * |L i j|) ∧
      (∑ j : Fin n, (L i j + e j) * x j) = b i := by
  let a : Fin i.val → ℝ := fun t => L i ⟨t.val, by omega⟩
  let v : Fin i.val → ℝ := fun t => x ⟨t.val, by omega⟩
  obtain ⟨cd, c, hcd, hc, heq⟩ :=
    p18_rounded_solve_row fp n i.val a v (b i) (L i i) (x i)
      hvalid (by omega) hdiag (by simpa [p18ForwardRow, a, v] using hrow)
  let e : Fin n → ℝ := fun j =>
    if h : j.val < i.val then L i j * (c ⟨j.val, h⟩ - 1)
    else if j = i then L i j * (cd - 1) else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < i.val
    · have hh : |c ⟨j.val, hj⟩ - 1| ≤ p18Gamma fp.u n := hc _
      have he : e j = L i j * (c ⟨j.val, hj⟩ - 1) := by
        have hjFin : j < i := hj
        simp [e, hjFin]
      rw [he, abs_mul]
      nlinarith [abs_nonneg (L i j)]
    · by_cases hji : j = i
      · subst j
        have hh := hcd
        have he : e i = L i i * (cd - 1) := by
          simp [e]
        rw [he, abs_mul]
        nlinarith [abs_nonneg (L i i)]
      · have he : e j = 0 := by
          have hjFin : ¬j < i := hj
          simp [e, hjFin, hji]
        rw [he, abs_zero]
        have hgamma : 0 ≤ p18Gamma fp.u n := by
          unfold p18Gamma P18GammaValid at *
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
        exact mul_nonneg hgamma (abs_nonneg _)
  · rw [p18_sum_split n i (fun j => (L i j + e j) * x j)]
    have hlow :
        (∑ t : Fin i.val,
          (L i ⟨t.val, by omega⟩ + e ⟨t.val, by omega⟩) *
            x ⟨t.val, by omega⟩) =
          ∑ t : Fin i.val, a t * v t * c t := by
      apply Finset.sum_congr rfl
      intro t ht
      have htt : (⟨t.val, by omega⟩ : Fin n).val < i.val := t.isLt
      simp only [e, dif_pos htt]
      dsimp [a, v]
      ring
    have hcenter : (L i i + e i) * x i = L i i * x i * cd := by
      have he : e i = L i i * (cd - 1) := by
        simp [e]
      rw [he]
      ring
    have hhigh :
        (∑ t : Fin (n - i.val - 1),
          (L i ⟨i.val + 1 + t.val, by omega⟩ +
            e ⟨i.val + 1 + t.val, by omega⟩) *
            x ⟨i.val + 1 + t.val, by omega⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      let j : Fin n := ⟨i.val + 1 + t.val, by omega⟩
      have hgt : i.val < j.val := by dsimp [j]; omega
      have hnot : ¬j.val < i.val := by omega
      have hne : j ≠ i := by intro he; subst j; omega
      have hL : L i j = 0 := hlower j hgt
      have he : e j = 0 := by
        change (if h : j.val < i.val then L i j * (c ⟨j.val, h⟩ - 1)
          else if j = i then L i j * (cd - 1) else 0) = 0
        simp [hnot, hne]
      change (L i j + e j) * x j = 0
      rw [hL, he]
      ring
    rw [hlow, hcenter, hhigh]
    nlinarith [heq]

private theorem p18_back_row_error (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hvalid : P18GammaValid fp.u n) (hdiag : U i i ≠ 0)
    (hupper : ∀ j : Fin n, j.val < i.val → U i j = 0)
    (hrow : x i = p18BackRow fp n U b x i) :
    ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p18Gamma fp.u n * |U i j|) ∧
      (∑ j : Fin n, (U i j + e j) * x j) = b i := by
  let k := n - i.val - 1
  let a : Fin k → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
  let v : Fin k → ℝ := fun t => x ⟨i.val + 1 + t.val, by omega⟩
  obtain ⟨cd, c, hcd, hc, heq⟩ :=
    p18_rounded_solve_row fp n k a v (b i) (U i i) (x i)
      hvalid (by dsimp [k]; omega) hdiag
      (by simpa [p18BackRow, k, a, v] using hrow)
  let e : Fin n → ℝ := fun j =>
    if h : i.val < j.val then
      U i j * (c ⟨j.val - i.val - 1, by dsimp [k]; omega⟩ - 1)
    else if j = i then U i j * (cd - 1) else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    by_cases hj : i.val < j.val
    · have hh : |c ⟨j.val - i.val - 1, by dsimp [k]; omega⟩ - 1| ≤
          p18Gamma fp.u n := hc _
      have he : e j = U i j * (c ⟨j.val - i.val - 1, by dsimp [k]; omega⟩ - 1) := by
        have hjFin : i < j := hj
        simp [e, hjFin]
      rw [he, abs_mul]
      nlinarith [abs_nonneg (U i j)]
    · by_cases hji : j = i
      · subst j
        have he : e i = U i i * (cd - 1) := by simp [e]
        rw [he, abs_mul]
        nlinarith [abs_nonneg (U i i)]
      · have he : e j = 0 := by
          have hjFin : ¬i < j := hj
          simp [e, hjFin, hji]
        rw [he, abs_zero]
        have hgamma : 0 ≤ p18Gamma fp.u n := by
          unfold p18Gamma P18GammaValid at *
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
        exact mul_nonneg hgamma (abs_nonneg _)
  · rw [p18_sum_split n i (fun j => (U i j + e j) * x j)]
    have hlow :
        (∑ t : Fin i.val,
          (U i ⟨t.val, by omega⟩ + e ⟨t.val, by omega⟩) *
            x ⟨t.val, by omega⟩) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      let j : Fin n := ⟨t.val, by omega⟩
      have hlt : j.val < i.val := by dsimp [j]; exact t.isLt
      have hnot : ¬i.val < j.val := by omega
      have hne : j ≠ i := by intro he; subst j; omega
      have hU : U i j = 0 := hupper j hlt
      have he : e j = 0 := by
        change (if h : i.val < j.val then
          U i j * (c ⟨j.val - i.val - 1, by dsimp [k]; omega⟩ - 1)
          else if j = i then U i j * (cd - 1) else 0) = 0
        simp [hnot, hne]
      change (U i j + e j) * x j = 0
      rw [hU, he]
      ring
    have hcenter : (U i i + e i) * x i = U i i * x i * cd := by
      have he : e i = U i i * (cd - 1) := by simp [e]
      rw [he]
      ring
    have hhigh :
        (∑ t : Fin k,
          (U i ⟨i.val + 1 + t.val, by omega⟩ +
            e ⟨i.val + 1 + t.val, by omega⟩) *
            x ⟨i.val + 1 + t.val, by omega⟩) =
          ∑ t : Fin k, a t * v t * c t := by
      apply Finset.sum_congr rfl
      intro t ht
      let j : Fin n := ⟨i.val + 1 + t.val, by omega⟩
      have hgt : i.val < j.val := by dsimp [j]; omega
      have he : e j = U i j * (c t - 1) := by
        have hindex : (⟨j.val - i.val - 1, by dsimp [k]; omega⟩ : Fin k) = t := by
          apply Fin.ext
          dsimp [j]
          omega
        have hgtFin : i < j := hgt
        simp [e, hgtFin, hindex]
      change (U i j + e j) * x j = a t * v t * c t
      rw [he]
      dsimp [a, v]
      ring
    rw [hlow, hcenter, hhigh]
    nlinarith [heq]

private theorem p18_forward_stable (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ)
    (hvalid : P18GammaValid fp.u n)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0) :
    ∃ ΔL : P18Matrix n n,
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      (∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * (p18ForwardSub fp n L b j) = b i) := by
  let y := p18ForwardSub fp n L b
  have hprops := p18_forward_steps_properties fp n L b n (le_refl n) (fun _ => 0)
  have hrow : ∀ i, y i = p18ForwardRow fp n L b y i := by
    intro i
    exact hprops.2 i (by omega)
  have hlocal : ∀ i : Fin n, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p18Gamma fp.u n * |L i j|) ∧
      (∑ j : Fin n, (L i j + e j) * y j) = b i := by
    intro i
    exact p18_forward_row_error fp n L b y i hvalid (hdiag i) (hlower i) (hrow i)
  choose e hb heq using hlocal
  refine ⟨fun i j => e i j, hb, ?_⟩
  intro i
  exact heq i

private theorem p18_back_stable (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ)
    (hvalid : P18GammaValid fp.u n)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∃ ΔU : P18Matrix n n,
      (∀ i j, |ΔU i j| ≤ p18Gamma fp.u n * |U i j|) ∧
      (∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * (p18BackSub fp n U b j) = b i) := by
  let y := p18BackSub fp n U b
  have hprops := p18_back_steps_properties fp n U b n (le_refl n) (fun _ => 0)
  have hrow : ∀ i, y i = p18BackRow fp n U b y i := by
    intro i
    exact hprops.2 i (by omega)
  have hlocal : ∀ i : Fin n, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p18Gamma fp.u n * |U i j|) ∧
      (∑ j : Fin n, (U i j + e j) * y j) = b i := by
    intro i
    exact p18_back_row_error fp n U b y i hvalid (hdiag i) (hupper i) (hrow i)
  choose e hb heq using hlocal
  refine ⟨fun i j => e i j, hb, ?_⟩
  intro i
  exact heq i

private theorem p18_norm_nonneg {m n : ℕ} (A : P18Matrix m n) :
    0 ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  positivity

private theorem p18_norm_add_le {m n : ℕ} (A B : P18Matrix m n) :
    p18EntryNorm (A + B) ≤ p18EntryNorm A + p18EntryNorm B := by
  unfold p18EntryNorm
  simp only [Matrix.add_apply]
  calc
    (∑ i : Fin m, ∑ j : Fin n, |A i j + B i j|)
        ≤ ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |A i j|) +
        (∑ i : Fin m, ∑ j : Fin n, |B i j|) := by
          simp only [Finset.sum_add_distrib]

private theorem p18_norm_entry_le {m n : ℕ} (A B : P18Matrix m n)
    (c : ℝ) (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p18EntryNorm A ≤ c * p18EntryNorm B := by
  unfold p18EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |A i j|)
        ≤ ∑ i : Fin m, ∑ j : Fin n, c * |B i j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact h i j
    _ = c * (∑ i : Fin m, ∑ j : Fin n, |B i j|) := by
          simp only [Finset.mul_sum]

private theorem p18_norm_mul_le {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18EntryNorm (A * B) ≤ p18EntryNorm A * p18EntryNorm B := by
  have hrow : ∀ k : Fin n, (∑ j : Fin p, |B k j|) ≤ p18EntryNorm B := by
    intro k
    unfold p18EntryNorm
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin n => ∑ j : Fin p, |B i j|)
      (by intro i hi; positivity) (Finset.mem_univ k)
  unfold p18EntryNorm
  simp only [Matrix.mul_apply]
  calc
    (∑ i : Fin m, ∑ j : Fin p, |∑ k : Fin n, A i k * B k j|)
        ≤ ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |A i k| * |B k j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          simpa only [abs_mul] using
            (Finset.abs_sum_le_sum_abs (fun k : Fin n => A i k * B k j) Finset.univ)
    _ = ∑ i : Fin m, ∑ k : Fin n, |A i k| * (∑ j : Fin p, |B k j|) := by
          congr 1
          funext i
          rw [Finset.sum_comm]
          congr 1
          funext k
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin m, ∑ k : Fin n, |A i k| * p18EntryNorm B := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _)
    _ = (∑ i : Fin m, ∑ k : Fin n, |A i k|) * p18EntryNorm B := by
          simp only [Finset.sum_mul]

private theorem p18_norm_add3_le {m n : ℕ}
    (A B C : P18Matrix m n) :
    p18EntryNorm (A + B + C) ≤
      p18EntryNorm A + p18EntryNorm B + p18EntryNorm C := by
  exact le_trans (p18_norm_add_le (A + B) C)
    (add_le_add_left (p18_norm_add_le A B) _)

private theorem p18_bound_arith (l d v g eta : ℝ) :
    (g * l) * ((1 + eta) * d) * ((1 + g) * v) +
      l * (eta * d) * ((1 + g) * v) + l * d * (g * v) =
      l * d * v * (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
  ring

private theorem p18_combined_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      ΔL * (D + ΔD) * (p18Transpose L + ΔU) +
        L * ΔD * (p18Transpose L + ΔU) + L * D * ΔU := by
  change (L + ΔL) * (D + ΔD) * (p18Transpose L + ΔU) -
    L * D * p18Transpose L = _
  noncomm_ring

private theorem p18_combined_norm_bound (fp : P18FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (heta : 0 ≤ eta)
    (hvalid : P18GammaValid fp.u n)
    (hL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18EntryNorm L * p18EntryNorm D *
        p18EntryNorm (p18Transpose L) *
        (p18Gamma fp.u n * (1 + eta) * (1 + p18Gamma fp.u n) +
          eta * (1 + p18Gamma fp.u n) + p18Gamma fp.u n) := by
  let g := p18Gamma fp.u n
  let l := p18EntryNorm L
  let d := p18EntryNorm D
  let v := p18EntryNorm (p18Transpose L)
  have hg : 0 ≤ g := by
    dsimp [g, p18Gamma, P18GammaValid] at *
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hl : 0 ≤ l := p18_norm_nonneg L
  have hd : 0 ≤ d := p18_norm_nonneg D
  have hv : 0 ≤ v := p18_norm_nonneg (p18Transpose L)
  have hdL : p18EntryNorm ΔL ≤ g * l := p18_norm_entry_le ΔL L g hL
  have hdU : p18EntryNorm ΔU ≤ g * v :=
    p18_norm_entry_le ΔU (p18Transpose L) g hU
  have hDsum : p18EntryNorm (D + ΔD) ≤ (1 + eta) * d := by
    calc
      p18EntryNorm (D + ΔD) ≤ d + p18EntryNorm ΔD := p18_norm_add_le D ΔD
      _ ≤ (1 + eta) * d := by dsimp [d] at *; nlinarith
  have hUsum : p18EntryNorm (p18Transpose L + ΔU) ≤ (1 + g) * v := by
    calc
      p18EntryNorm (p18Transpose L + ΔU) ≤ v + p18EntryNorm ΔU :=
        p18_norm_add_le (p18Transpose L) ΔU
      _ ≤ (1 + g) * v := by nlinarith
  have hterm1 :
      p18EntryNorm (ΔL * (D + ΔD) * (p18Transpose L + ΔU)) ≤
        (g * l) * ((1 + eta) * d) * ((1 + g) * v) := by
    calc
      p18EntryNorm (ΔL * (D + ΔD) * (p18Transpose L + ΔU)) ≤
          p18EntryNorm (ΔL * (D + ΔD)) *
            p18EntryNorm (p18Transpose L + ΔU) := p18_norm_mul_le _ _
      _ ≤ (p18EntryNorm ΔL * p18EntryNorm (D + ΔD)) *
          p18EntryNorm (p18Transpose L + ΔU) := by
            exact mul_le_mul_of_nonneg_right (p18_norm_mul_le _ _)
              (p18_norm_nonneg _)
      _ ≤ (g * l) * ((1 + eta) * d) * ((1 + g) * v) := by
            gcongr <;> first | exact hdL | exact hDsum | exact hUsum |
              exact (p18_norm_nonneg _) | nlinarith [hg, hl, hd, hv, heta]
  have hterm2 :
      p18EntryNorm (L * ΔD * (p18Transpose L + ΔU)) ≤
        l * (eta * d) * ((1 + g) * v) := by
    calc
      p18EntryNorm (L * ΔD * (p18Transpose L + ΔU)) ≤
          p18EntryNorm (L * ΔD) *
            p18EntryNorm (p18Transpose L + ΔU) := p18_norm_mul_le _ _
      _ ≤ (l * p18EntryNorm ΔD) *
          p18EntryNorm (p18Transpose L + ΔU) := by
            exact mul_le_mul_of_nonneg_right (p18_norm_mul_le _ _)
              (p18_norm_nonneg _)
      _ ≤ l * (eta * d) * ((1 + g) * v) := by
            gcongr <;> first | exact hD | exact hUsum |
              exact (p18_norm_nonneg _) | nlinarith [hg, hl, hd, hv, heta]
  have hterm3 : p18EntryNorm (L * D * ΔU) ≤ l * d * (g * v) := by
    calc
      p18EntryNorm (L * D * ΔU) ≤ p18EntryNorm (L * D) * p18EntryNorm ΔU :=
        p18_norm_mul_le _ _
      _ ≤ (l * d) * (g * v) := by
        gcongr <;> first | exact (p18_norm_mul_le L D) | exact hdU |
          exact (p18_norm_nonneg _) | nlinarith [hg, hl, hd, hv, heta]
  rw [p18_combined_expand]
  calc
    p18EntryNorm
        (ΔL * (D + ΔD) * (p18Transpose L + ΔU) +
            L * ΔD * (p18Transpose L + ΔU) + L * D * ΔU) ≤
        p18EntryNorm (ΔL * (D + ΔD) * (p18Transpose L + ΔU)) +
          p18EntryNorm (L * ΔD * (p18Transpose L + ΔU)) +
          p18EntryNorm (L * D * ΔU) := by
            exact p18_norm_add3_le _ _ _
    _ ≤ (g * l) * ((1 + eta) * d) * ((1 + g) * v) +
          l * (eta * d) * ((1 + g) * v) + l * d * (g * v) := by
            exact add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = l * d * v * (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
          exact p18_bound_arith l d v g eta

private theorem p18_combined_le_solve_factor (fp : P18FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (heta : 0 ≤ eta) (hvalid : P18GammaValid fp.u n)
    (hL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18SolveBackwardFactor fp n eta L D := by
  let q := p18EntryNorm L * p18EntryNorm D *
    p18EntryNorm (p18Transpose L) *
    (p18Gamma fp.u n * (1 + eta) * (1 + p18Gamma fp.u n) +
      eta * (1 + p18Gamma fp.u n) + p18Gamma fp.u n)
  have hbase : p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤ q :=
    p18_combined_norm_bound fp n eta L D ΔL ΔD ΔU heta hvalid hL hD hU
  have hq : 0 ≤ q := le_trans (p18_norm_nonneg _) hbase
  have hpow : 1 ≤ ((n : ℝ) ^ 6) ∨ n = 0 := by
    cases n with
    | zero => exact Or.inr rfl
    | succ n =>
        left
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact one_le_pow₀ hn
  cases hpow with
  | inl hpow =>
      have hscale : q ≤ ((n : ℝ) ^ 6) * q := by
        nlinarith [mul_nonneg (show 0 ≤ ((n : ℝ) ^ 6) - 1 by linarith) hq]
      calc
        p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤ q := hbase
        _ ≤ ((n : ℝ) ^ 6) * q := hscale
        _ = p18SolveBackwardFactor fp n eta L D := by
          unfold p18SolveBackwardFactor q
          ring
  | inr hn =>
      subst n
      have hqzero : q = 0 := by simp [q, p18EntryNorm]
      simpa [p18SolveBackwardFactor, hqzero] using hbase

/-- P18-C3: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p18_c3_ldlt_solve_backward_stability
    (fp : P18FPModel) (n : ℕ) (A L D E0 : P18Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p18LDLT L D = A + E0)
    (hE0 : p18EntryNorm E0 ≤ factorEta * p18EntryNorm A)
    (hDsolve : P18BlockSolveStable n D
      (p18ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P18Matrix n n),
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      p18EntryNorm ΔD ≤ eta * p18EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p18Gamma fp.u n * |p18Transpose L i j|) ∧
      F = p18TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p18BackSub fp n (p18Transpose L) z j = b i) ∧
      p18EntryNorm F ≤
        p18TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P18-C3-H001
  let y := p18ForwardSub fp n L b
  let U := p18Transpose L
  let x := p18BackSub fp n U z
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    p18_forward_stable fp n L b hvalid hdiag hlower
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have hUdiag : ∀ i, U i i ≠ 0 := by
    intro i
    simpa [U, p18Transpose] using hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p18_back_stable fp n U z hvalid hUdiag hUupper
  let F := p18TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, ?_, rfl, ?_, ?_⟩
  · exact hΔU
  · have hforwardVec : (L + ΔL).mulVec y = b := by
      funext i
      change (∑ j : Fin n, (L i j + ΔL i j) * y j) = b i
      exact hforward i
    have hblockVec : (D + ΔD).mulVec z = y := by
      funext i
      change (∑ j : Fin n, (D i j + ΔD i j) * z j) = y i
      exact hblock i
    have hbackVec : (U + ΔU).mulVec x = z := by
      funext i
      change (∑ j : Fin n, (U i j + ΔU i j) * x j) = z i
      exact hback i
    have hprod : ((L + ΔL) * (D + ΔD) * (U + ΔU)).mulVec x = b := by
      rw [← Matrix.mulVec_mulVec, hbackVec]
      rw [← Matrix.mulVec_mulVec, hblockVec, hforwardVec]
    have hAf : A + F = (L + ΔL) * (D + ΔD) * (U + ΔU) := by
      have hf : L * D * U = A + E0 := by
        simpa [p18LDLT, U] using hfactor
      change A + (E0 + ((L + ΔL) * (D + ΔD) * (U + ΔU) - L * D * U)) = _
      rw [hf]
      abel
    intro i
    have hi := congrFun hprod i
    change (∑ j : Fin n, ((L + ΔL) * (D + ΔD) * (U + ΔU)) i j * x j) = b i at hi
    rw [← hAf] at hi
    simpa only [Matrix.add_apply, x, U] using hi
  · have hsolve := p18_combined_le_solve_factor fp n eta L D ΔL ΔD ΔU
      heta hvalid hΔL hΔD hΔU
    calc
      p18EntryNorm F = p18EntryNorm
          (E0 + p18CombinedBackwardError L D ΔL ΔD ΔU) := rfl
      _ ≤ p18EntryNorm E0 +
          p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) :=
        p18_norm_add_le _ _
      _ ≤ factorEta * p18EntryNorm A +
          p18SolveBackwardFactor fp n eta L D :=
        add_le_add hE0 hsolve
      _ = p18TotalBackwardBound fp n eta factorEta A L D := rfl

end VSCLReuse

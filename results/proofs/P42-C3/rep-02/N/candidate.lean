import VSCLReuse.P42.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p42_gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P42GammaValid u n) : 0 ≤ p42Gamma u n := by
  unfold p42Gamma P42GammaValid at *
  have hn : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  exact div_nonneg hn (le_of_lt (sub_pos.mpr hv))

private lemma p42_gamma_valid_of_le (u : ℝ) {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : P42GammaValid u n) : P42GammaValid u m := by
  unfold P42GammaValid at *
  have h : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  exact lt_of_le_of_lt h hv

private lemma p42_gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P42GammaValid u (n + 1)) :
    p42Gamma u n + u + p42Gamma u n * u ≤ p42Gamma u (n + 1) := by
  have hvn := p42_gamma_valid_of_le u hu (Nat.le_succ n) hv
  have h₁ : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvn
  have h₂ : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr hv
  have hnum : 0 ≤ (n : ℝ) * u + u := add_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
  unfold p42Gamma
  have hcast : ((n + 1 : ℕ) : ℝ) * u = (n : ℝ) * u + u := by push_cast; ring
  rw [hcast]
  have h₂' : 0 < 1 - ((n : ℝ) * u + u) := by rw [← hcast]; exact h₂
  have hcalc :
      (n : ℝ) * u / (1 - (n : ℝ) * u) + u +
        ((n : ℝ) * u / (1 - (n : ℝ) * u)) * u =
      ((n : ℝ) * u + u) / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  rw [hcalc]
  apply (div_le_div_iff₀ h₁ h₂').2
  nlinarith [mul_nonneg hnum hu]

private lemma p42_gamma_le (u : ℝ) {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : P42GammaValid u n) :
    p42Gamma u m ≤ p42Gamma u n := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hv' := p42_gamma_valid_of_le u hu (Nat.le_succ n) hv
      have hstep := p42_gamma_step u n hu hv
      have hnonneg := p42_gamma_nonneg u n hu hv'
      have hmn' := ih hv'
      nlinarith [mul_nonneg hnonneg hu]

private lemma p42_error_update (u G H e d : ℝ)
    (_hu : 0 ≤ u) (hG : 0 ≤ G) (he : |e| ≤ G) (hd : |d| ≤ u)
    (hstep : G + u + G * u ≤ H) :
    |e + d + e * d| ≤ H := by
  have hmul : |e * d| ≤ G * u := by
    rw [abs_mul]
    exact mul_le_mul he hd (abs_nonneg _) hG
  calc
    |e + d + e * d| ≤ |e| + |d| + |e * d| := by
      calc
        _ ≤ |e + d| + |e * d| := abs_add_le _ _
        _ ≤ (|e| + |d|) + |e * d| := by gcongr; exact abs_add_le _ _
        _ = _ := by ring
    _ ≤ G + u + G * u := by gcongr
    _ ≤ H := hstep

private lemma p42_fold_backward (fp : P42FPModel) (n : ℕ)
    (v : Fin n → ℝ) (a : ℝ) (hv : P42GammaValid fp.u n) :
    ∃ ea : ℝ, ∃ μ : Fin n → ℝ,
      |ea| ≤ p42Gamma fp.u n ∧
      (∀ j, |μ j| ≤ p42Gamma fp.u n) ∧
      Fin.foldl n (fun acc j => fp.fl_add acc (v j)) a =
        a * (1 + ea) + ∑ j : Fin n, v j * (1 + μ j) := by
  induction n generalizing a with
  | zero =>
      refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · simpa using p42_gamma_nonneg fp.u 0 fp.u_nonneg hv
      · intro j; exact j.elim0
      · simp
  | succ n ih =>
      have hvn : P42GammaValid fp.u n :=
        p42_gamma_valid_of_le fp.u fp.u_nonneg (Nat.le_succ n) hv
      obtain ⟨ea, μ, hea, hμ, hprev⟩ :=
        ih (fun j => v j.castSucc) a hvn
      let prev := Fin.foldl n (fun acc j => fp.fl_add acc (v j.castSucc)) a
      obtain ⟨d, hd, hfl⟩ := fp.model_add prev (v (Fin.last n))
      let nextE := ea + d + ea * d
      let nextM : Fin (n + 1) → ℝ :=
        Fin.snoc (fun j => μ j + d + μ j * d) d
      have hstep := p42_gamma_step fp.u n fp.u_nonneg hv
      have hE : |nextE| ≤ p42Gamma fp.u (n + 1) :=
        p42_error_update fp.u (p42Gamma fp.u n)
          (p42Gamma fp.u (n + 1)) ea d fp.u_nonneg
          (p42_gamma_nonneg fp.u n fp.u_nonneg hvn) hea hd hstep
      have hM : ∀ j, |nextM j| ≤ p42Gamma fp.u (n + 1) := by
        intro j
        refine Fin.lastCases ?_ ?_ j
        · simp only [nextM, Fin.snoc_last]
          
          have hnonneg := p42_gamma_nonneg fp.u n fp.u_nonneg hvn
          nlinarith [mul_nonneg hnonneg fp.u_nonneg]
        · intro k
          simp only [nextM, Fin.snoc_castSucc]
          exact p42_error_update fp.u (p42Gamma fp.u n)
            (p42Gamma fp.u (n + 1)) (μ k) d fp.u_nonneg
            (p42_gamma_nonneg fp.u n fp.u_nonneg hvn) (hμ k) hd hstep
      refine ⟨nextE, nextM, hE, hM, ?_⟩
      have hsum :
          (∑ j : Fin n, v j.castSucc * (1 + μ j)) * (1 + d) =
          ∑ j : Fin n, v j.castSucc * (1 + (μ j + d + μ j * d)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hfirst :
          (a * (1 + ea)) * (1 + d) = a * (1 + nextE) := by
        dsimp [nextE]
        ring
      rw [Fin.foldl_succ_last]
      change fp.fl_add prev (v (Fin.last n)) = _
      rw [hfl]
      rw [Fin.sum_univ_castSucc]
      simp only [nextM, Fin.snoc_castSucc, Fin.snoc_last]
      have hprev' : prev = a * (1 + ea) + ∑ j : Fin n, v j.castSucc * (1 + μ j) := hprev
      rw [hprev']
      rw [add_mul, add_mul, hfirst, hsum]
      ring

private lemma p42_recursive_backward (fp : P42FPModel) (b : ℕ)
    (v : Fin b → ℝ) (hb : 0 < b)
    (hv : P42GammaValid fp.u (b - 1)) :
    ∃ μ : Fin b → ℝ,
      (∀ j, |μ j| ≤ p42Gamma fp.u (b - 1)) ∧
      p42RecursiveSum fp b v = ∑ j : Fin b, v j * (1 + μ j) := by
  cases b with
  | zero => omega
  | succ n =>
      obtain ⟨ea, μ, hea, hμ, hfold⟩ :=
        p42_fold_backward fp n (fun j => v j.succ) (v 0) (by simpa using hv)
      refine ⟨Fin.cons ea μ, ?_, ?_⟩
      · intro j
        refine Fin.cases ?_ ?_ j
        · simpa using hea
        · intro k
          simpa using hμ k
      · unfold p42RecursiveSum
        rw [Fin.foldl_succ]
        rw [fp.fl_add_zero]
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact hfold

private lemma p42_sum_halves (r : ℕ) (f : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f ⟨i.val, by
        have := i.isLt
        simp [pow_succ]
        omega⟩) +
      (∑ i : Fin (2 ^ r), f ⟨i.val + 2 ^ r, by
        have := i.isLt
        simp [pow_succ]
        omega⟩) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  calc
    (∑ i : Fin (2 ^ (r + 1)), f i) =
        ∑ i : Fin (2 ^ r + 2 ^ r), f ((Fin.castOrderIso hpow.symm) i) := by
      simpa using (Equiv.sum_comp (Fin.castOrderIso hpow.symm).toEquiv f).symm
    _ = _ := by
      rw [Fin.sum_univ_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        congr 1
        apply Fin.ext
        simp


private lemma p42_pairwise_backward (fp : P42FPModel) (r : ℕ)
    (v : Fin (2 ^ r) → ℝ) (hv : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → ℝ,
      (∀ i, |μ i| ≤ p42Gamma fp.u r) ∧
      p42PairwiseSum fp r v = ∑ i : Fin (2 ^ r), v i * (1 + μ i) := by
  induction r with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i
        simpa using p42_gamma_nonneg fp.u 0 fp.u_nonneg hv
      · simp [p42PairwiseSum]
  | succ r ih =>
      let left : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val, by
        have := i.isLt
        simp [pow_succ]
        omega⟩
      let right : Fin (2 ^ r) → ℝ := fun i => v ⟨i.val + 2 ^ r, by
        have := i.isLt
        simp [pow_succ]
        omega⟩
      have hvr : P42GammaValid fp.u r :=
        p42_gamma_valid_of_le fp.u fp.u_nonneg (Nat.le_succ r) hv
      obtain ⟨μl, hμl, hl⟩ := ih left hvr
      obtain ⟨μr, hμr, hr⟩ := ih right hvr
      let lv := p42PairwiseSum fp r left
      let rv := p42PairwiseSum fp r right
      obtain ⟨d, hd, hfl⟩ := fp.model_add lv rv
      let ml : Fin (2 ^ r) → ℝ := fun i => μl i + d + μl i * d
      let mr : Fin (2 ^ r) → ℝ := fun i => μr i + d + μr i * d
      have hstep := p42_gamma_step fp.u r fp.u_nonneg hv
      have hml (i) : |ml i| ≤ p42Gamma fp.u (r + 1) := by
        exact p42_error_update fp.u (p42Gamma fp.u r)
          (p42Gamma fp.u (r + 1)) (μl i) d fp.u_nonneg
          (p42_gamma_nonneg fp.u r fp.u_nonneg hvr) (hμl i) hd hstep
      have hmr (i) : |mr i| ≤ p42Gamma fp.u (r + 1) := by
        exact p42_error_update fp.u (p42Gamma fp.u r)
          (p42Gamma fp.u (r + 1)) (μr i) d fp.u_nonneg
          (p42_gamma_nonneg fp.u r fp.u_nonneg hvr) (hμr i) hd hstep
      have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
        rw [pow_succ]
        omega
      let μ : Fin (2 ^ (r + 1)) → ℝ :=
        fun i => Fin.append ml mr (Fin.cast hpow i)
      have hμleft (i : Fin (2 ^ r)) :
          μ ⟨i.val, by
            have := i.isLt
            simp [pow_succ]
            omega⟩ = ml i := by
        have heq : Fin.cast hpow ⟨i.val, by
            have := i.isLt
            simp [pow_succ]
            omega⟩ = Fin.castAdd (2 ^ r) i := Fin.ext rfl
        calc
          μ ⟨i.val, by
              have := i.isLt
              simp [pow_succ]
              omega⟩ = Fin.append ml mr (Fin.castAdd (2 ^ r) i) :=
            congrArg (Fin.append ml mr) heq
          _ = ml i := Fin.append_left ml mr i
      have hμright (i : Fin (2 ^ r)) :
          μ ⟨i.val + 2 ^ r, by
            have := i.isLt
            simp [pow_succ]
            omega⟩ = mr i := by
        have heq : Fin.cast hpow ⟨i.val + 2 ^ r, by
            have := i.isLt
            simp [pow_succ]
            omega⟩ = Fin.natAdd (2 ^ r) i := by
              apply Fin.ext
              simp
        calc
          μ ⟨i.val + 2 ^ r, by
              have := i.isLt
              simp [pow_succ]
              omega⟩ = Fin.append ml mr (Fin.natAdd (2 ^ r) i) :=
            congrArg (Fin.append ml mr) heq
          _ = mr i := Fin.append_right ml mr i
      have hμ : ∀ i, |μ i| ≤ p42Gamma fp.u (r + 1) := by
        intro i
        change |Fin.append ml mr (Fin.cast hpow i)| ≤ _
        refine Fin.addCases (motive := fun k => |Fin.append ml mr k| ≤ _)
          ?_ ?_ (Fin.cast hpow i)
        · intro j
          simpa using hml j
        · intro j
          change |Fin.append ml mr (Fin.natAdd (2 ^ r) j)| ≤ _
          simpa only [Fin.append_right] using hmr j
      refine ⟨μ, hμ, ?_⟩
      have hsum :
          (∑ i : Fin (2 ^ (r + 1)), v i * (1 + μ i)) =
          (∑ i : Fin (2 ^ r), left i * (1 + ml i)) +
          (∑ i : Fin (2 ^ r), right i * (1 + mr i)) := by
        rw [p42_sum_halves]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [left, hμleft]
        · apply Finset.sum_congr rfl
          intro i hi
          simp only [right, hμright]
      have hls :
          (∑ i : Fin (2 ^ r), left i * (1 + μl i)) * (1 + d) =
          ∑ i : Fin (2 ^ r), left i * (1 + ml i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [ml]
        ring
      have hrs :
          (∑ i : Fin (2 ^ r), right i * (1 + μr i)) * (1 + d) =
          ∑ i : Fin (2 ^ r), right i * (1 + mr i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [mr]
        ring
      change fp.fl_add lv rv = _
      rw [hfl, hsum]
      have hl' : lv = ∑ i : Fin (2 ^ r), left i * (1 + μl i) := hl
      have hr' : rv = ∑ i : Fin (2 ^ r), right i * (1 + μr i) := hr
      rw [hl', hr', add_mul, hls, hrs]

/-- Theorem 3.1, recursive-block and pairwise-outer specialization. -/
theorem p42_c3_fabsum_backward_error
    (fp : P42FPModel) (b r : ℕ)
    (x : Fin (2 ^ r) → Fin b → ℝ)
    (hb : 0 < b)
    (hbvalid : P42GammaValid fp.u (b - 1))
    (hrvalid : P42GammaValid fp.u r) :
    ∃ μ : Fin (2 ^ r) → Fin b → ℝ,
      (∀ i j, |μ i j| ≤
        p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
          p42Gamma fp.u (b - 1) * p42Gamma fp.u r) ∧
      p42FABsum fp b r x =
        ∑ i : Fin (2 ^ r), ∑ j : Fin b, x i j * (1 + μ i j) := by
  -- PROOF_START P42-C3-H001
  let μf : Fin (2 ^ r) → Fin b → ℝ := fun i =>
    Classical.choose (p42_recursive_backward fp b (x i) hb hbvalid)
  have hfb (i : Fin (2 ^ r)) (j : Fin b) :
      |μf i j| ≤ p42Gamma fp.u (b - 1) :=
    (Classical.choose_spec (p42_recursive_backward fp b (x i) hb hbvalid)).1 j
  have hfeq (i : Fin (2 ^ r)) :
      p42RecursiveSum fp b (x i) = ∑ j : Fin b, x i j * (1 + μf i j) :=
    (Classical.choose_spec (p42_recursive_backward fp b (x i) hb hbvalid)).2
  obtain ⟨μa, hab, haeq⟩ :=
    p42_pairwise_backward fp r (fun i => p42RecursiveSum fp b (x i)) hrvalid
  let μ : Fin (2 ^ r) → Fin b → ℝ :=
    fun i j => μf i j + μa i + μf i j * μa i
  refine ⟨μ, ?_, ?_⟩
  · intro i j
    exact p42_error_update (p42Gamma fp.u r)
      (p42Gamma fp.u (b - 1))
      (p42Gamma fp.u (b - 1) + p42Gamma fp.u r +
        p42Gamma fp.u (b - 1) * p42Gamma fp.u r)
      (μf i j) (μa i)
      (p42_gamma_nonneg fp.u r fp.u_nonneg hrvalid)
      (p42_gamma_nonneg fp.u (b - 1) fp.u_nonneg hbvalid)
      (hfb i j) (hab i) le_rfl
  · unfold p42FABsum
    rw [haeq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfeq i, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [μ]
    ring

end VSCLReuse

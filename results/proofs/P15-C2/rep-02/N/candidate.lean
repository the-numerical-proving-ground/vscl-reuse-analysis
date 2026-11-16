import VSCLReuse.P15.Definitions

namespace VSCLReuse

private def p15CoeffInterval (u : ℝ) (k : ℕ) (c : ℝ) : Prop :=
  1 - (k : ℝ) * u ≤ c ∧ c ≤ 1 / (1 - (k : ℝ) * u)

private theorem p15_coeff_interval_one (u : ℝ) :
    p15CoeffInterval u 0 1 := by
  simp [p15CoeffInterval]

private theorem p15_coeff_interval_mono {u : ℝ} (hu : 0 ≤ u)
    {k l : ℕ} (hkl : k ≤ l) (hl : (l : ℝ) * u < 1)
    {c : ℝ} (hc : p15CoeffInterval u k c) :
    p15CoeffInterval u l c := by
  have hkr : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hku : (k : ℝ) * u ≤ (l : ℝ) * u := mul_le_mul_of_nonneg_right hkr hu
  have hkpos : 0 < 1 - (k : ℝ) * u := by linarith
  have hlpos : 0 < 1 - (l : ℝ) * u := by linarith
  rcases hc with ⟨hc₁, hc₂⟩
  constructor
  · linarith
  · exact hc₂.trans (one_div_le_one_div_of_le hlpos (by linarith))

private theorem p15_interval_mul_step (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (hc₁ : 1 - a ≤ c) (hc₂ : c ≤ 1 / (1 - a))
    (hd₁ : -b ≤ d) (hd₂ : d ≤ b) :
    1 - a - b ≤ c * (1 + d) ∧
      c * (1 + d) ≤ 1 / (1 - a - b) := by
  have hapos : 0 < 1 - a := by linarith
  have hbpos : 0 ≤ 1 - b := by linarith
  have hdpos : 0 ≤ 1 + d := by linarith
  have hden : 0 < 1 - a - b := by linarith
  constructor
  · nlinarith [mul_nonneg ha hb,
      mul_nonneg (by linarith : 0 ≤ c - (1 - a)) hdpos,
      mul_nonneg hbpos (by linarith : 0 ≤ b - d)]
  · have haux : (1 + b) / (1 - a) ≤ 1 / (1 - a - b) := by
      apply (le_div_iff₀ hden).2
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hapos).2
      nlinarith [mul_nonneg hb (by linarith : 0 ≤ a + b)]
    have hc3 : c * (1 + d) ≤ (1 / (1 - a)) * (1 + b) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / (1 - a) - c) hdpos,
        mul_nonneg (by positivity : 0 ≤ 1 / (1 - a)) (by linarith : 0 ≤ b - d)]
    calc
      c * (1 + d) ≤ (1 / (1 - a)) * (1 + b) := hc3
      _ = (1 + b) / (1 - a) := by ring
      _ ≤ 1 / (1 - a - b) := haux

private theorem p15_interval_div_step (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b < 1)
    (hc₁ : 1 - a ≤ c) (hc₂ : c ≤ 1 / (1 - a))
    (hd₁ : -b ≤ d) (hd₂ : d ≤ b) :
    1 - a - b ≤ c / (1 + d) ∧
      c / (1 + d) ≤ 1 / (1 - a - b) := by
  have hapos : 0 < 1 - a := by linarith
  have hdpos : 0 < 1 + d := by linarith
  have hden : 0 < 1 - a - b := by linarith
  constructor
  · apply (le_div_iff₀ hdpos).2
    nlinarith [mul_nonneg hb (by linarith : 0 ≤ a + b),
      mul_nonneg (by linarith : 0 ≤ 1 - a - b) (by linarith : 0 ≤ b - d)]
  · apply (div_le_iff₀ hdpos).2
    have haux : 1 / (1 - a) * (1 - a - b) ≤ 1 - b := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hapos).2
      nlinarith [mul_nonneg ha hb]
    have hh : c * (1 - a - b) ≤ 1 + d := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / (1 - a) - c)
        (by linarith : 0 ≤ 1 - a - b)]
    calc
      c ≤ (1 + d) / (1 - a - b) := (le_div_iff₀ hden).2 hh
      _ = 1 / (1 - a - b) * (1 + d) := by ring

private theorem p15_coeff_mul_step {u : ℝ} (hu : 0 ≤ u)
    {k : ℕ} (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    {c d : ℝ} (hc : p15CoeffInterval u k c) (hd : |d| ≤ u) :
    p15CoeffInterval u (k + 1) (c * (1 + d)) := by
  have ha : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd₁ : -u ≤ d := (abs_le.mp hd).1
  have hd₂ : d ≤ u := (abs_le.mp hd).2
  have hs : (k : ℝ) * u + u < 1 := by
    simpa [Nat.cast_add, add_mul] using hk
  have h := p15_interval_mul_step ((k : ℝ) * u) u c d ha hu hs hc.1 hc.2 hd₁ hd₂
  simpa [p15CoeffInterval, Nat.cast_add, add_mul, sub_sub] using h

private theorem p15_coeff_div_step {u : ℝ} (hu : 0 ≤ u)
    {k : ℕ} (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    {c d : ℝ} (hc : p15CoeffInterval u k c) (hd : |d| ≤ u) :
    p15CoeffInterval u (k + 1) (c / (1 + d)) := by
  have ha : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hd₁ : -u ≤ d := (abs_le.mp hd).1
  have hd₂ : d ≤ u := (abs_le.mp hd).2
  have hs : (k : ℝ) * u + u < 1 := by
    simpa [Nat.cast_add, add_mul] using hk
  have h := p15_interval_div_step ((k : ℝ) * u) u c d ha hu hs hc.1 hc.2 hd₁ hd₂
  simpa [p15CoeffInterval, Nat.cast_add, add_mul, sub_sub] using h

private theorem p15_coeff_gamma {u : ℝ} (hu : 0 ≤ u)
    {k : ℕ} (hk : (k : ℝ) * u < 1)
    {c : ℝ} (hc : p15CoeffInterval u k c) :
    |c - 1| ≤ p15Gamma u k := by
  have hnonneg : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hden : 0 < 1 - (k : ℝ) * u := by linarith
  have hgam : (k : ℝ) * u ≤ p15Gamma u k := by
    unfold p15Gamma
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg ((k : ℝ) * u)]
  have htop : 1 / (1 - (k : ℝ) * u) - 1 = p15Gamma u k := by
    unfold p15Gamma
    field_simp
    ring
  apply abs_le.mpr
  constructor
  · linarith [hc.1]
  · linarith [hc.2]

private theorem p15_fold_backward (fp : P15FPModel) (k : ℕ)
    (a x : Fin k → ℝ) (b : ℝ)
    (hk : (k : ℝ) * fp.u < 1) :
    ∃ (c : ℝ) (d : Fin k → ℝ),
      p15CoeffInterval fp.u k c ∧
      (∀ j, p15CoeffInterval fp.u k (d j)) ∧
      b = c * Fin.foldl k
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) b +
          ∑ j : Fin k, d j * (a j * x j) := by
  induction k with
  | zero =>
      refine ⟨1, Fin.elim0, p15_coeff_interval_one _, ?_, ?_⟩
      · intro j; exact j.elim0
      · simp
  | succ k ih =>
      have hk0 : (k : ℝ) * fp.u < 1 := by
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) fp.u_nonneg) hk
      let a₀ : Fin k → ℝ := fun j => a j.castSucc
      let x₀ : Fin k → ℝ := fun j => x j.castSucc
      obtain ⟨c, d, hc, hd, heq⟩ := ih a₀ x₀ hk0
      let s : ℝ := Fin.foldl k
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a₀ j) (x₀ j))) b
      let t : ℝ := a (Fin.last k) * x (Fin.last k)
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨δ, hδ, hsub⟩ := fp.model_sub s
        (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      have hone : 1 + δ ≠ 0 := by
        have hδlo := (abs_le.mp hδ).1
        have hu : fp.u < 1 := by
          have hle : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
          nlinarith [mul_nonneg (sub_nonneg.mpr hle) fp.u_nonneg]
        linarith
      refine ⟨c / (1 + δ), Fin.snoc d (c * (1 + μ)),
        p15_coeff_div_step fp.u_nonneg hk hc hδ, ?_, ?_⟩
      · intro j
        induction j using Fin.lastCases with
        | last =>
            simpa using p15_coeff_mul_step fp.u_nonneg hk hc hμ
        | cast j =>
            simpa using p15_coeff_interval_mono fp.u_nonneg
              (Nat.le_succ k) hk (hd j)
      · have hfold : Fin.foldl (k + 1)
            (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) b =
            fp.fl_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) := by
            rw [Fin.foldl_succ_last]
        rw [hfold, hsub, hmul, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have hident : c / (1 + δ) * ((s - t * (1 + μ)) * (1 + δ)) +
            (∑ j : Fin k, d j * (a₀ j * x₀ j)) +
            c * (1 + μ) * t = c * s +
              ∑ j : Fin k, d j * (a₀ j * x₀ j) := by
          field_simp
          ring
        convert heq.trans hident.symm using 1
        simp [a₀, x₀, t, s, add_assoc]

private theorem p15_steps_preserve (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (j : Fin n)
    (hj : j.val < n - k) :
    p15ForwardSubSteps fp n L b k hk x j = x j := by
  induction k generalizing x with
  | zero => simp [p15ForwardSubSteps]
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hj0 : j.val < n - k := by omega
      have hneq : j ≠ ik := by
        intro h
        have : j.val = n - k - 1 := congrArg Fin.val h
        omega
      change p15ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' j = x j
      rw [ih x' (Nat.le_of_succ_le hk) hj0]
      simp [x', hneq]

private noncomputable def p15LocalFold (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b q : Fin n → ℝ) (j : Fin n) : ℝ :=
  Fin.foldl j.val
    (fun acc (t : Fin j.val) =>
      fp.fl_sub acc (fp.fl_mul (L j ⟨t.val, by omega⟩)
        (q ⟨t.val, by omega⟩))) (b j)

private theorem p15_steps_equation (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (j : Fin n)
    (hj : n - k ≤ j.val) :
    let q := p15ForwardSubSteps fp n L b k hk x
    q j = fp.fl_div (p15LocalFold fp n L b q j) (L j j) := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let q : Fin n → ℝ := p15ForwardSubSteps fp n L b k
        (Nat.le_of_succ_le hk) x'
      change q j = fp.fl_div (p15LocalFold fp n L b q j) (L j j)
      by_cases hji : j = ik
      · rw [hji]
        have hik : ik.val < n - k := by dsimp [ik]; omega
        have hpres : q ik = x' ik :=
          p15_steps_preserve fp n L b x' k (Nat.le_of_succ_le hk) ik hik
        have hlow : ∀ t : Fin count,
            q ⟨t.val, by dsimp [count] at t ⊢; omega⟩ =
              x ⟨t.val, by dsimp [count] at t ⊢; omega⟩ := by
          intro t
          have ht : t.val < n - k := by dsimp [count] at t ⊢; omega
          calc
            q ⟨t.val, by dsimp [count] at t ⊢; omega⟩ =
                x' ⟨t.val, by dsimp [count] at t ⊢; omega⟩ := by
              simpa [q] using p15_steps_preserve fp n L b x' k
                (Nat.le_of_succ_le hk)
                ⟨t.val, by dsimp [count] at t ⊢; omega⟩ ht
            _ = x ⟨t.val, by dsimp [count] at t ⊢; omega⟩ := by
              have hneq : (⟨t.val, by dsimp [count] at t ⊢; omega⟩ : Fin n) ≠ ik := by
                intro heq
                have hv := congrArg Fin.val heq
                dsimp [ik, count] at hv
                exact Nat.ne_of_lt t.isLt hv
              simp [x', hneq]
        have hfold : p15LocalFold fp n L b q ik = s := by
          unfold p15LocalFold s
          have hcount : ik.val = count := rfl
          simp only [hcount]
          congr 1
          funext acc t
          simpa only [Fin.val_cast] using congrArg
            (fun z : ℝ => fp.fl_sub acc (fp.fl_mul
              (L ik ⟨t.val, by dsimp [count] at t ⊢; omega⟩) z)) (hlow t)
        rw [hpres, hfold]
        simp [x']
      · have hgt : n - k ≤ j.val := by
          have : j.val ≠ n - k - 1 := by
            intro heq
            apply hji
            apply Fin.ext
            simpa [ik] using heq
          omega
        exact ih x' (Nat.le_of_succ_le hk) hgt

private theorem p15_sum_lower {n : ℕ} (k : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin k.val, f ⟨t.val, by omega⟩) + f k := by
  let g : ℕ → ℝ := fun i => if h : i < n then f ⟨i, h⟩ else 0
  have htail : ∑ i ∈ Finset.Ico (k.val + 1) n, g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k.val < i := by simp only [Finset.mem_Ico] at hi; omega
    have hin : i < n := (Finset.mem_Ico.mp hi).2
    simp [g, hin, hzero ⟨i, hin⟩ hki]
  have hsplit := Finset.sum_range_add_sum_Ico g (Nat.succ_le_of_lt k.isLt)
  rw [htail, add_zero, Finset.sum_range_succ] at hsplit
  have hfull : (∑ j : Fin n, f j) = ∑ i ∈ Finset.range n, g i := by
    simpa [g] using (Finset.sum_fin_eq_sum_range f)
  have hpre : (∑ t : Fin k.val, f ⟨t.val, by omega⟩) =
      ∑ i ∈ Finset.range k.val, g i := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k.val := Finset.mem_range.mp hi
    have hin : i < n := lt_trans hik k.isLt
    simp [g, hik, hin]
  have hkval : g k.val = f k := by simp [g, k.isLt]
  rw [hfull, hpre, ← hkval]
  exact hsplit.symm

private theorem p15_row_backward (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ k, L k k ≠ 0)
    (hlower : ∀ k j : Fin n, k.val < j.val → L k j = 0)
    (hvalid : P15GammaValid fp.u n) (k : Fin n) :
    let q := p15ForwardSub fp n L b
    ∃ delta : Fin n → ℝ,
      (∀ j, |delta j| ≤ p15Gamma fp.u n * |L k j|) ∧
      (∑ j : Fin n, (L k j + delta j) * q j) = b k := by
  let q := p15ForwardSub fp n L b
  let a : Fin k.val → ℝ := fun t => L k ⟨t.val, by omega⟩
  let x : Fin k.val → ℝ := fun t => q ⟨t.val, by omega⟩
  let s := p15LocalFold fp n L b q k
  have hk : (k.val : ℝ) * fp.u < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt k.isLt)
        fp.u_nonneg) hvalid
  have hksucc : ((k.val + 1 : ℕ) : ℝ) * fp.u < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt k.isLt)
        fp.u_nonneg) hvalid
  obtain ⟨c, d, hc, hd, heq⟩ := p15_fold_backward fp k.val a x (b k) hk
  have hfold : Fin.foldl k.val
      (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) (b k) = s := rfl
  rw [hfold] at heq
  have hq : q k = fp.fl_div s (L k k) := by
    simpa [q, s, p15ForwardSub] using
      p15_steps_equation fp n L b (fun _ => 0) n (le_refl n) k (by simp)
  obtain ⟨ν, hν, hdiv⟩ := fp.model_div s (L k k) (hdiag k)
  rw [hdiv] at hq
  have hνpos : 0 < 1 + ν := by
    have hνlo := (abs_le.mp hν).1
    have hu : fp.u < 1 := by
      have hn : (1 : ℝ) ≤ n := by
        have hn0 : 1 ≤ n := Nat.succ_le_of_lt
          (lt_of_le_of_lt (Nat.zero_le _) k.isLt)
        exact_mod_cast hn0
      have hvalid' : (n : ℝ) * fp.u < 1 := hvalid
      nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 1) fp.u_nonneg]
    linarith
  have hνne : 1 + ν ≠ 0 := ne_of_gt hνpos
  let e := c / (1 + ν)
  have he : p15CoeffInterval fp.u (k.val + 1) e :=
    p15_coeff_div_step fp.u_nonneg hksucc hc hν
  have hdiag_eq : c * s = e * (L k k * q k) := by
    have hh : L k k * q k = s * (1 + ν) := by
      rw [hq]
      field_simp [hdiag k]
    rw [hh]
    dsimp [e]
    field_simp [hνne]
  let delta : Fin n → ℝ := fun j =>
    if h : j.val < k.val then (d ⟨j.val, h⟩ - 1) * L k j
    else if j = k then (e - 1) * L k j else 0
  refine ⟨delta, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < k.val
    · have hdj : p15CoeffInterval fp.u n (d ⟨j.val, hj⟩) :=
        p15_coeff_interval_mono fp.u_nonneg (Nat.le_of_lt k.isLt) hvalid
          (hd ⟨j.val, hj⟩)
      have hγ := p15_coeff_gamma fp.u_nonneg hvalid hdj
      simpa only [delta, dif_pos hj, abs_mul] using
        mul_le_mul_of_nonneg_right hγ (abs_nonneg (L k j))
    · by_cases heqj : j = k
      · subst j
        have hen : p15CoeffInterval fp.u n e :=
          p15_coeff_interval_mono fp.u_nonneg (Nat.succ_le_of_lt k.isLt)
            hvalid he
        have hγ := p15_coeff_gamma fp.u_nonneg hvalid hen
        simpa [delta, abs_mul] using
          mul_le_mul_of_nonneg_right hγ (abs_nonneg (L k k))
      · have hγnonneg : 0 ≤ p15Gamma fp.u n := by
          unfold p15Gamma
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
            (le_of_lt (sub_pos.mpr hvalid))
        have hj' : ¬j < k := hj
        simpa [delta, hj', heqj] using
          mul_nonneg hγnonneg (abs_nonneg (L k j))
  · have hzero : ∀ j : Fin n, k.val < j.val →
        (L k j + delta j) * q j = 0 := by
        intro j hj
        have hjnot : ¬j.val < k.val := by omega
        have hjne : j ≠ k := by intro heqj; subst j; omega
        simp [delta, hjne, hlower k j hj]
    rw [p15_sum_lower k _ hzero]
    have hprefix : (∑ t : Fin k.val,
        (L k ⟨t.val, by omega⟩ + delta ⟨t.val, by omega⟩) *
          q ⟨t.val, by omega⟩) =
        ∑ t : Fin k.val, d t * (a t * x t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htk : t.val < k.val := t.isLt
      simp only [delta, dif_pos htk]
      dsimp [a, x]
      ring
    have hdiagterm : (L k k + delta k) * q k = e * (L k k * q k) := by
      have hkk : ¬k.val < k.val := Nat.lt_irrefl _
      simp [delta]
      ring
    rw [hprefix, hdiagterm]
    rw [hdiag_eq] at heq
    linarith [heq]

private theorem p15_rounded_row_perturbation (fp : P15FPModel)
    (m n : ℕ) (X : P15Matrix m n) (R : P15Matrix n n)
    (hdiag : ∀ k, R k k ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n) (i : Fin m) :
    ∃ deltaL : P15Matrix n n,
      (∀ k j, |deltaL k j| ≤ p15Gamma fp.u n * |R j k|) ∧
      (∀ k, ∑ j : Fin n,
        (p15Transpose R k j + deltaL k j) *
          p15RoundedQ fp X R i j = X i k) := by
  classical
  have hd : ∀ k : Fin n, p15Transpose R k k ≠ 0 := by
    intro k
    simpa [p15Transpose] using hdiag k
  have hl : ∀ k j : Fin n, k.val < j.val → p15Transpose R k j = 0 := by
    intro k j hkj
    simpa [p15Transpose] using hupper j k hkj
  have hrow : ∀ k : Fin n, ∃ delta : Fin n → ℝ,
      (∀ j, |delta j| ≤ p15Gamma fp.u n * |p15Transpose R k j|) ∧
      (∑ j : Fin n, (p15Transpose R k j + delta j) *
        p15RoundedQ fp X R i j) = X i k := by
    intro k
    simpa [p15RoundedQ] using
      p15_row_backward fp n (p15Transpose R) (X i) hd hl hvalid k
  let deltaL : P15Matrix n n := fun k => Classical.choose (hrow k)
  refine ⟨deltaL, ?_, ?_⟩
  · intro k j
    simpa [deltaL, p15Transpose] using (Classical.choose_spec (hrow k)).1 j
  · intro k
    exact (Classical.choose_spec (hrow k)).2

private theorem p15_vec_norm_sq_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p15VecNormSq v := by
  unfold p15VecNormSq
  exact Finset.sum_nonneg (fun j _ => sq_nonneg (v j))

private theorem p15_frob_norm_sq_nonneg {m n : ℕ} (A : P15Matrix m n) :
    0 ≤ p15FrobNormSq A := by
  unfold p15FrobNormSq
  exact Finset.sum_nonneg (fun i _ => p15_vec_norm_sq_nonneg (A i))

private theorem p15_frob_bound_of_row_bounds {m n : ℕ}
    (A B : P15Matrix m n) (C : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ i, p15VecNorm (A i) ≤ C * p15VecNorm (B i)) :
    p15FrobNorm A ≤ C * p15FrobNorm B := by
  have hrowsq : ∀ i : Fin m,
      p15VecNormSq (A i) ≤ C ^ 2 * p15VecNormSq (B i) := by
    intro i
    have ha : 0 ≤ p15VecNorm (A i) := Real.sqrt_nonneg _
    have hb : 0 ≤ p15VecNorm (B i) := Real.sqrt_nonneg _
    have ha2 : p15VecNorm (A i) ^ 2 = p15VecNormSq (A i) := by
      exact Real.sq_sqrt (p15_vec_norm_sq_nonneg _)
    have hb2 : p15VecNorm (B i) ^ 2 = p15VecNormSq (B i) := by
      exact Real.sq_sqrt (p15_vec_norm_sq_nonneg _)
    nlinarith [mul_nonneg
      (by linarith [hrow i] : 0 ≤ C * p15VecNorm (B i) - p15VecNorm (A i))
      (by positivity : 0 ≤ C * p15VecNorm (B i) + p15VecNorm (A i))]
  have hsum : p15FrobNormSq A ≤ C ^ 2 * p15FrobNormSq B := by
    unfold p15FrobNormSq
    calc
      ∑ i : Fin m, p15VecNormSq (A i) ≤
          ∑ i : Fin m, C ^ 2 * p15VecNormSq (B i) :=
        Finset.sum_le_sum (fun i _ => hrowsq i)
      _ = C ^ 2 * ∑ i : Fin m, p15VecNormSq (B i) := by rw [Finset.mul_sum]
  have ha : 0 ≤ p15FrobNorm A := Real.sqrt_nonneg _
  have hb : 0 ≤ p15FrobNorm B := Real.sqrt_nonneg _
  have ha2 : p15FrobNorm A ^ 2 = p15FrobNormSq A :=
    Real.sq_sqrt (p15_frob_norm_sq_nonneg A)
  have hb2 : p15FrobNorm B ^ 2 = p15FrobNormSq B :=
    Real.sq_sqrt (p15_frob_norm_sq_nonneg B)
  have hCB : 0 ≤ C * p15FrobNorm B := mul_nonneg hC hb
  have hsq : p15FrobNorm A ^ 2 ≤ (C * p15FrobNorm B) ^ 2 := by
    rw [ha2, mul_pow, hb2]
    exact hsum
  nlinarith

theorem p15_c2_lemma_3_2
    (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P15RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p15FrobNorm (p15RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p15FrobNorm
        (p15Residual (p15RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P15-C2-H001
  let Q := p15RoundedQ fp X R
  let A := p15Residual Q R X
  let C : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hC : 0 ≤ C := by
    dsimp [C]
    have h₁ : 0 ≤ (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n := by positivity
    exact mul_nonneg (mul_nonneg h₁ fp.u_nonneg) hxNorm
  have hrow : ∀ i : Fin m, p15VecNorm (A i) ≤ C * p15VecNorm (Q i) := by
    intro i
    obtain ⟨deltaL, hδ, heq⟩ :=
      p15_rounded_row_perturbation fp m n X R hdiag hupper hvalid i
    exact hperturb i deltaL hδ heq
  have hFrob : p15FrobNorm A ≤ C * p15FrobNorm Q :=
    p15_frob_bound_of_row_bounds A Q C hC hrow
  have hQ : p15FrobNorm Q ≤ Real.sqrt (3 * (n : ℝ)) := hQFrob
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have h3N : 0 ≤ (3 : ℝ) * n := by positivity
  have hr : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs : 0 ≤ Real.sqrt (3 * (n : ℝ)) := Real.sqrt_nonneg _
  have hr2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hN
  have hs2 : Real.sqrt (3 * (n : ℝ)) ^ 2 = 3 * (n : ℝ) := Real.sq_sqrt h3N
  have hconst : (11 : ℝ) / 10 *
      (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) ≤
        2 * (n : ℝ) := by
    have hz : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) :=
      mul_nonneg hr hs
    have hz2 : (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) ^ 2 =
        3 * (n : ℝ) ^ 2 := by
      rw [mul_pow, hr2, hs2]
      ring
    by_contra hh
    have hh' : 2 * (n : ℝ) < (11 : ℝ) / 10 *
        (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) := lt_of_not_ge hh
    have hp : 0 < (11 : ℝ) / 10 *
        (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) - 2 * (n : ℝ) := by
      linarith
    have hp2 : 0 < (11 : ℝ) / 10 *
        (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) + 2 * (n : ℝ) := by
      linarith
    nlinarith [mul_pos hp hp2]
  have hscale : 0 ≤ fp.u * xNorm := mul_nonneg fp.u_nonneg hxNorm
  have hlast : C * Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    have hh := mul_le_mul_of_nonneg_right hconst hscale
    dsimp [C]
    nlinarith [hh]
  calc
    p15FrobNorm (p15Residual (p15RoundedQ fp X R) R X) =
        p15FrobNorm A := rfl
    _ ≤ C * p15FrobNorm Q := hFrob
    _ ≤ C * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQ hC
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := hlast

end VSCLReuse

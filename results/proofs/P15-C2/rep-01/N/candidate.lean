import VSCLReuse.P15.Definitions

namespace VSCLReuse

private lemma p15_den_step (a u D e : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hsmall : a + u < 1)
    (hlo : 1 - a ≤ D) (hhi : D ≤ 1 / (1 - a))
    (he : |e| ≤ u) :
    1 - (a + u) ≤ D * (1 + e) ∧
      D * (1 + e) ≤ 1 / (1 - (a + u)) := by
  have hae : -u ≤ e := (abs_le.mp he).1
  have hbe : e ≤ u := (abs_le.mp he).2
  have h1a : 0 < 1 - a := by linarith
  have h1au : 0 < 1 - (a + u) := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hD : 0 ≤ D := by linarith
  constructor
  · have h := mul_le_mul hlo (by linarith : 1 - u ≤ 1 + e)
        (by linarith : 0 ≤ 1 - u) hD
    nlinarith [mul_nonneg ha hu]
  · have h1 := mul_le_mul_of_nonneg_left (show 1 + e ≤ 1 + u by linarith) hD
    have h2 := mul_le_mul_of_nonneg_right hhi (by linarith : 0 ≤ 1 + u)
    have h3a : (1 + u) / (1 - a) ≤ 1 / (1 - (a + u)) := by
      apply (div_le_div_iff₀ h1a h1au).2
      nlinarith [mul_nonneg ha hu, sq_nonneg u]
    have h3 : (1 / (1 - a)) * (1 + u) ≤ 1 / (1 - (a + u)) := by
      convert h3a using 1; ring
    nlinarith

private lemma p15_coeff_bound (a b u D e : ℝ)
    (ha : 0 ≤ a) (hu : 0 ≤ u) (hab : a + u ≤ b) (hb : b < 1)
    (hlo : 1 - a ≤ D) (hhi : D ≤ 1 / (1 - a))
    (he : |e| ≤ u) :
    |(1 + e) / D - 1| ≤ b / (1 - b) := by
  have hbe := (abs_le.mp he).2
  have hae := (abs_le.mp he).1
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hD : 0 < D := by linarith
  have hqlo : 1 - b ≤ (1 + e) / D := by
    apply (le_div_iff₀ hD).2
    have h1 := mul_le_mul_of_nonneg_left hhi (le_of_lt h1b)
    have h2 : (1 - b) / (1 - a) ≤ 1 - u := by
      apply (div_le_iff₀ h1a).2
      nlinarith [mul_nonneg ha hu]
    have h3 : (1 - b) * D ≤ (1 - b) / (1 - a) := by
      convert h1 using 1; ring
    linarith
  have hqhi : (1 + e) / D ≤ 1 / (1 - b) := by
    apply (div_le_iff₀ hD).2
    have h1 : (1 + e) * (1 - b) ≤ (1 + u) * (1 - b) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt h1b)
    have h2 : (1 + u) * (1 - b) ≤ 1 - a := by
      nlinarith [mul_nonneg ha hu, mul_nonneg hu (show b - a - u ≥ 0 by linarith)]
    have h3 : (1 + e) * (1 - b) ≤ D := by linarith
    have h4 : 1 + e ≤ D / (1 - b) := (le_div_iff₀ h1b).mpr h3
    convert h4 using 1; ring
  have hb0 : 0 ≤ b := by linarith
  have hbB : b ≤ b / (1 - b) := by
    apply (le_div_iff₀ h1b).2
    nlinarith [sq_nonneg b]
  have hBE : 1 / (1 - b) - 1 = b / (1 - b) := by
    field_simp
    ring
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

private def p15FoldRow (fp : P15FPModel) (a y : ℕ → ℝ)
    (b : ℝ) (k : ℕ) : ℝ :=
  Fin.foldl k (fun acc t => fp.fl_sub acc (fp.fl_mul (a t.val) (y t.val))) b

private lemma p15FoldRow_succ (fp : P15FPModel) (a y : ℕ → ℝ)
    (b : ℝ) (k : ℕ) :
    p15FoldRow fp a y b (k + 1) =
      fp.fl_sub (p15FoldRow fp a y b k) (fp.fl_mul (a k) (y k)) := by
  unfold p15FoldRow
  rw [Fin.foldl_succ_last]
  rfl

private lemma p15_fold_backward (fp : P15FPModel) (n : ℕ)
    (a y : ℕ → ℝ) (b : ℝ) (k : ℕ) (hk : k ≤ n)
    (hvalid : P15GammaValid fp.u n) :
    ∃ (D : ℝ) (d : ℕ → ℝ),
      1 - (k : ℝ) * fp.u ≤ D ∧
      D ≤ 1 / (1 - (k : ℝ) * fp.u) ∧
      (∀ j < k, |d j - 1| ≤ p15Gamma fp.u n) ∧
      b = p15FoldRow fp a y b k / D +
        ∑ j ∈ Finset.range k, a j * d j * y j := by
  induction k with
  | zero =>
      refine ⟨1, fun _ => 1, by simp, by simp, ?_, ?_⟩
      · intro j hj
        omega
      · simp [p15FoldRow]
  | succ k ih =>
      have hk0 : k ≤ n := by omega
      obtain ⟨D, d, hlo, hhi, hd, heq⟩ := ih hk0
      let s := p15FoldRow fp a y b k
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul (a k) (y k)
      obtain ⟨alpha, halpha, hsub⟩ := fp.model_sub s (fp.fl_mul (a k) (y k))
      have hu := fp.u_nonneg
      have hkr : (k : ℝ) * fp.u + fp.u ≤ (n : ℝ) * fp.u := by
        have hr : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
          (mul_le_mul_of_nonneg_right hr hu)
      have hksmall : (k : ℝ) * fp.u + fp.u < 1 := lt_of_le_of_lt hkr hvalid
      have hDpos : 0 < D := by
        have hka : 0 ≤ (k : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) hu
        linarith
      have halphapos : 0 < 1 + alpha := by
        have h := (abs_le.mp halpha).1
        have hka : 0 ≤ (k : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) hu
        linarith
      let D' := D * (1 + alpha)
      let d' : ℕ → ℝ := Function.update d k ((1 + mu) / D)
      have hbound := p15_den_step ((k : ℝ) * fp.u) fp.u D alpha
        (mul_nonneg (Nat.cast_nonneg _) hu) hu hksmall hlo hhi halpha
      refine ⟨D', d', ?_, ?_, ?_, ?_⟩
      · simpa only [D', Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbound.1
      · simpa only [D', Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbound.2
      · intro j hj
        by_cases hkj : j = k
        · subst j
          simpa [d', Function.update_self] using
            p15_coeff_bound ((k : ℝ) * fp.u) ((n : ℝ) * fp.u)
              fp.u D mu (mul_nonneg (Nat.cast_nonneg _) hu) hu hkr hvalid
              hlo hhi hmu
        · have hjk : j < k := by omega
          simpa [d', Function.update_of_ne hkj] using hd j hjk
      · rw [p15FoldRow_succ, hsub, hmul, Finset.sum_range_succ]
        simp only [d', Function.update_self]
        have hD' : D' ≠ 0 := ne_of_gt (mul_pos hDpos halphapos)
        have hD : D ≠ 0 := ne_of_gt hDpos
        -- The old coefficients are unchanged by the update at index `k`.
        have hsum : (∑ j ∈ Finset.range k, a j * d' j * y j) =
            ∑ j ∈ Finset.range k, a j * d j * y j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≠ k := by
            have : j < k := Finset.mem_range.mp hj
            omega
          simp [d', Function.update_of_ne hjk]
        rw [hsum]
        calc
          b = s / D + ∑ j ∈ Finset.range k, a j * d j * y j := heq
          _ = (s - a k * y k * (1 + mu)) * (1 + alpha) / (D * (1 + alpha)) +
              ((∑ j ∈ Finset.range k, a j * d j * y j) +
                a k * ((1 + mu) / D) * y k) := by
            field_simp
            ring


private def p15SolveVal (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div (Fin.foldl i.val
    (fun acc (t : Fin i.val) =>
      fp.fl_sub acc (fp.fl_mul (L i ⟨t.val, by omega⟩)
        (x ⟨t.val, by omega⟩))) (b i)) (L i i)

private lemma p15SolveVal_ext (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x y : Fin n → ℝ) (i : Fin n)
    (h : ∀ j : Fin n, j.val < i.val → x j = y j) :
    p15SolveVal fp n L b x i = p15SolveVal fp n L b y i := by
  unfold p15SolveVal
  have hf : (fun acc (t : Fin i.val) =>
      fp.fl_sub acc (fp.fl_mul (L i ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩))) =
      (fun acc (t : Fin i.val) =>
      fp.fl_sub acc (fp.fl_mul (L i ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩))) := by
    funext acc t
    rw [h ⟨t.val, by omega⟩ t.isLt]
  rw [hf]

private lemma p15SolveVal_fold (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x : Fin n → ℝ) (k : Fin n) :
    p15SolveVal fp n L b x k =
      fp.fl_div
        (p15FoldRow fp
          (fun j => if hj : j < n then L k ⟨j, hj⟩ else 0)
          (fun j => if hj : j < n then x ⟨j, hj⟩ else 0)
          (b k) k.val) (L k k) := by
  unfold p15SolveVal p15FoldRow
  congr 1
  congr 1
  funext acc t
  have ht : t.val < n := lt_trans t.isLt k.isLt
  simp [ht]

private lemma p15Steps_succ (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b x : Fin n → ℝ) (k : ℕ)
    (hk : k + 1 ≤ n) :
    p15ForwardSubSteps fp n L b (k + 1) hk x =
      p15ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk)
        (Function.update x (⟨n - k - 1, by omega⟩ : Fin n)
          (p15SolveVal fp n L b x ⟨n - k - 1, by omega⟩)) := by
  rfl

private lemma p15Steps_preserve (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i.val < n - k) :
    p15ForwardSubSteps fp n L b k hk x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      have hiik : i ≠ ik := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [ik] at hv
        omega
      rw [p15Steps_succ]
      have hi0 : i.val < n - k := by omega
      rw [ih (Nat.le_of_succ_le hk) _ hi0]
      change Function.update x ik (p15SolveVal fp n L b x ik) i = x i
      simp [Function.update_of_ne hiik]

private lemma p15Steps_spec (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ)
    (hgood : ∀ i : Fin n, i.val < n - k → x i = p15SolveVal fp n L b x i) :
    ∀ i : Fin n,
      p15ForwardSubSteps fp n L b k hk x i =
        p15SolveVal fp n L b (p15ForwardSubSteps fp n L b k hk x) i := by
  induction k generalizing x with
  | zero =>
      intro i
      simpa [p15ForwardSubSteps] using hgood i (by omega)
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let x' := Function.update x ik (p15SolveVal fp n L b x ik)
      have hgood' : ∀ i : Fin n, i.val < n - k →
          x' i = p15SolveVal fp n L b x' i := by
        intro i hi
        by_cases hii : i = ik
        · subst i
          have hlow : ∀ j : Fin n, j.val < ik.val → x j = x' j := by
            intro j hj
            have hne : j ≠ ik := by
              intro heq
              have hv := congrArg Fin.val heq
              omega
            simp [x', Function.update_of_ne hne]
          simp only [x', Function.update_self]
          exact p15SolveVal_ext fp n L b x x' ik hlow
        · have hlt : i.val < n - (k + 1) := by
            have hv : i.val ≠ ik.val := by
              intro hv
              exact hii (Fin.ext hv)
            dsimp [ik] at hv
            omega
          have hlow : ∀ j : Fin n, j.val < i.val → x j = x' j := by
            intro j hj
            have hne : j ≠ ik := by
              intro heq
              have hv := congrArg Fin.val heq
              dsimp [ik] at hv
              omega
            simp [x', Function.update_of_ne hne]
          have hx : x' i = x i := by simp [x', Function.update_of_ne hii]
          rw [hx, hgood i hlt]
          exact p15SolveVal_ext fp n L b x x' i hlow
      intro i
      rw [p15Steps_succ]
      exact ih (Nat.le_of_succ_le hk) x' hgood' i

private lemma p15ForwardSub_spec (fp : P15FPModel) (n : ℕ)
    (L : P15Matrix n n) (b : Fin n → ℝ) (i : Fin n) :
    p15ForwardSub fp n L b i =
      p15SolveVal fp n L b (p15ForwardSub fp n L b) i := by
  unfold p15ForwardSub
  apply p15Steps_spec
  intro j hj
  omega

private lemma p15_row_factor (fp : P15FPModel) (n k : ℕ)
    (hk : k < n) (hvalid : P15GammaValid fp.u n)
    (a y : ℕ → ℝ) (b diag : ℝ) (hdiag : diag ≠ 0) (ha : a k = diag)
    (hsolve : y k = fp.fl_div (p15FoldRow fp a y b k) diag) :
    ∃ d : ℕ → ℝ,
      (∀ j < k + 1, |d j - 1| ≤ p15Gamma fp.u n) ∧
      b = ∑ j ∈ Finset.range (k + 1), a j * d j * y j := by
  obtain ⟨D, d, hlo, hhi, hd, heq⟩ :=
    p15_fold_backward fp n a y b k (Nat.le_of_lt hk) hvalid
  let s := p15FoldRow fp a y b k
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div s diag hdiag
  let D' := D * (1 + delta)
  let d' := Function.update d k (1 / D')
  have hu := fp.u_nonneg
  have hkr : (k : ℝ) * fp.u + fp.u ≤ (n : ℝ) * fp.u := by
    have hr : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
      (mul_le_mul_of_nonneg_right hr hu)
  have hksmall : (k : ℝ) * fp.u + fp.u < 1 := lt_of_le_of_lt hkr hvalid
  have hDpos : 0 < D := by
    have hka : 0 ≤ (k : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) hu
    linarith
  have hdeltaPos : 0 < 1 + delta := by
    have h := (abs_le.mp hdelta).1
    have hka : 0 ≤ (k : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) hu
    linarith
  have hbound := p15_den_step ((k : ℝ) * fp.u) fp.u D delta
    (mul_nonneg (Nat.cast_nonneg _) hu) hu hksmall hlo hhi hdelta
  have hD'lo : 1 - ((k + 1 : ℕ) : ℝ) * fp.u ≤ D' := by
    simpa only [D', Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbound.1
  have hD'hi : D' ≤ 1 / (1 - ((k + 1 : ℕ) : ℝ) * fp.u) := by
    simpa only [D', Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbound.2
  have hdiagBound : |1 / D' - 1| ≤ p15Gamma fp.u n := by
    have h := p15_coeff_bound (((k + 1 : ℕ) : ℝ) * fp.u)
      ((n : ℝ) * fp.u) 0 D' 0
      (mul_nonneg (Nat.cast_nonneg _) hu) (le_refl 0)
      (by simpa only [add_zero, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hkr)
      hvalid hD'lo hD'hi (by simp)
    simpa [p15Gamma] using h
  refine ⟨d', ?_, ?_⟩
  · intro j hj
    by_cases hjk : j = k
    · subst j
      simpa [d', Function.update_self] using hdiagBound
    · have hjlt : j < k := by omega
      simpa [d', Function.update_of_ne hjk] using hd j hjlt
  · have hDne : D ≠ 0 := ne_of_gt hDpos
    have hD'ne : D' ≠ 0 := ne_of_gt (mul_pos hDpos hdeltaPos)
    have hterm : a k * d' k * y k = s / D := by
      rw [ha, hsolve, hdiv]
      simp only [d', Function.update_self]
      dsimp [D']
      field_simp
    rw [Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range k, a j * d' j * y j) =
        ∑ j ∈ Finset.range k, a j * d j * y j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≠ k := by
        have : j < k := Finset.mem_range.mp hj
        omega
      simp [d', Function.update_of_ne hjk]
    rw [hsum, hterm]
    linarith

private lemma p15_lower_row_sum {n : ℕ} (R : P15Matrix n n)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (q : Fin n → ℝ) (k : Fin n) (d : ℕ → ℝ) :
    (∑ j : Fin n,
      R j k * (if j.val < k.val + 1 then d j.val else 1) * q j) =
    ∑ j ∈ Finset.range (k.val + 1),
      (if hj : j < n then R ⟨j, hj⟩ k else 0) * d j *
        (if hj : j < n then q ⟨j, hj⟩ else 0) := by
  let f : ℕ → ℝ := fun j =>
    if hj : j < n then
      R ⟨j, hj⟩ k * (if j < k.val + 1 then d j else 1) * q ⟨j, hj⟩
    else 0
  have hfin : (∑ j : Fin n,
      R j k * (if j.val < k.val + 1 then d j.val else 1) * q j) =
      ∑ j : Fin n, f j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [f, j.isLt]
  rw [hfin, Fin.sum_univ_eq_sum_range]
  have hsplit : n = (k.val + 1) + (n - (k.val + 1)) := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have htail : (∑ j ∈ Finset.range (n - (k.val + 1)), f (k.val + 1 + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hkj : k.val < k.val + 1 + j := by omega
    by_cases hn : k.val + 1 + j < n
    · have hz := hupper (⟨k.val + 1 + j, hn⟩ : Fin n) k hkj
      simp [f, hn, hz]
    · simp [f, hn]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k.val + 1 := Finset.mem_range.mp hj
  have hjn : j < n := by have hk := k.isLt; omega
  simp only [f, dif_pos hjn, if_pos hjk]

private lemma p15_backward_matrix (fp : P15FPModel) (m n : ℕ)
    (X : P15Matrix m n) (R : P15Matrix n n)
    (hdiag : ∀ k, R k k ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P15GammaValid fp.u n) (i : Fin m) :
    ∃ deltaL : P15Matrix n n,
      (∀ k j, |deltaL k j| ≤ p15Gamma fp.u n * |R j k|) ∧
      (∀ k, ∑ j : Fin n,
        (p15Transpose R k j + deltaL k j) *
          p15RoundedQ fp X R i j = X i k) := by
  let q : Fin n → ℝ := p15RoundedQ fp X R i
  have hrowfac : ∀ k : Fin n, ∃ d : ℕ → ℝ,
      (∀ j < k.val + 1, |d j - 1| ≤ p15Gamma fp.u n) ∧
      X i k = ∑ j : Fin n,
        R j k * (if j.val < k.val + 1 then d j.val else 1) * q j := by
    intro k
    let a : ℕ → ℝ := fun j => if hj : j < n then R ⟨j, hj⟩ k else 0
    let y : ℕ → ℝ := fun j => if hj : j < n then q ⟨j, hj⟩ else 0
    have ha : a k.val = R k k := by simp [a, k.isLt]
    have hsolve : y k.val = fp.fl_div (p15FoldRow fp a y (X i k) k.val) (R k k) := by
      have hq := p15ForwardSub_spec fp n (p15Transpose R) (X i) k
      rw [p15SolveVal_fold] at hq
      simpa [a, y, q, p15RoundedQ, p15Transpose, k.isLt] using hq
    obtain ⟨d, hd, heq⟩ :=
      p15_row_factor fp n k.val k.isLt hvalid a y (X i k) (R k k)
        (hdiag k) ha hsolve
    refine ⟨d, hd, ?_⟩
    rw [p15_lower_row_sum R hupper q k d]
    simpa [a, y] using heq
  classical
  let d : Fin n → ℕ → ℝ := fun k => Classical.choose (hrowfac k)
  have hd (k : Fin n) := Classical.choose_spec (hrowfac k)
  let deltaL : P15Matrix n n := fun k j =>
    R j k * ((if j.val < k.val + 1 then d k j.val else 1) - 1)
  refine ⟨deltaL, ?_, ?_⟩
  · intro k j
    have hgam : 0 ≤ p15Gamma fp.u n := by
      unfold p15Gamma
      have hn : 0 ≤ (n : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
      have hden : 0 ≤ 1 - (n : ℝ) * fp.u := le_of_lt (sub_pos.mpr hvalid)
      exact div_nonneg hn hden
    by_cases hjk : j.val < k.val + 1
    · have hcoef := (hd k).1 j.val hjk
      calc
        |deltaL k j| = |R j k| * |d k j.val - 1| := by
          simp only [deltaL, if_pos hjk, abs_mul]
        _ ≤ |R j k| * p15Gamma fp.u n :=
          mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
        _ = p15Gamma fp.u n * |R j k| := mul_comm _ _
    · simp only [deltaL, if_neg hjk, sub_self, mul_zero, abs_zero]
      exact mul_nonneg hgam (abs_nonneg _)
  · intro k
    have heq := (hd k).2
    calc
      (∑ j : Fin n, (p15Transpose R k j + deltaL k j) * p15RoundedQ fp X R i j) =
          ∑ j : Fin n, R j k * (if j.val < k.val + 1 then d k j.val else 1) * q j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [deltaL, p15Transpose, q]
        ring
      _ = X i k := heq.symm

private lemma p15_norm_aggregate {m n : ℕ}
    (Q A : P15Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, p15VecNorm (A i) ≤ c * p15VecNorm (Q i)) :
    p15FrobNorm A ≤ c * p15FrobNorm Q := by
  have hs : p15FrobNormSq A ≤ c ^ 2 * p15FrobNormSq Q := by
    unfold p15FrobNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have ha : 0 ≤ p15VecNorm (A i) := Real.sqrt_nonneg _
    have hq : 0 ≤ p15VecNorm (Q i) := Real.sqrt_nonneg _
    have hsq := (sq_le_sq₀ ha (mul_nonneg hc hq)).mpr (hrow i)
    have hA : 0 ≤ p15VecNormSq (A i) := Finset.sum_nonneg (fun j hj => sq_nonneg _)
    have hQ : 0 ≤ p15VecNormSq (Q i) := Finset.sum_nonneg (fun j hj => sq_nonneg _)
    calc
      p15VecNormSq (A i) = (p15VecNorm (A i)) ^ 2 :=
        (Real.sq_sqrt hA).symm
      _ ≤ (c * p15VecNorm (Q i)) ^ 2 := hsq
      _ = c ^ 2 * p15VecNormSq (Q i) := by
        rw [mul_pow, show (p15VecNorm (Q i)) ^ 2 = p15VecNormSq (Q i) from Real.sq_sqrt hQ]
  have ha : 0 ≤ p15FrobNorm A := Real.sqrt_nonneg _
  have hq : 0 ≤ p15FrobNorm Q := Real.sqrt_nonneg _
  have hsqA : (p15FrobNorm A) ^ 2 = p15FrobNormSq A := by
    unfold p15FrobNorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _)))
  have hsqQ : (p15FrobNorm Q) ^ 2 = p15FrobNormSq Q := by
    unfold p15FrobNorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => sq_nonneg _)))
  have hsq : (p15FrobNorm A) ^ 2 ≤ (c * p15FrobNorm Q) ^ 2 := by
    calc
      (p15FrobNorm A) ^ 2 = p15FrobNormSq A := hsqA
      _ ≤ c ^ 2 * p15FrobNormSq Q := hs
      _ = (c * p15FrobNorm Q) ^ 2 := by rw [← hsqQ]; ring
  exact (sq_le_sq₀ ha (mul_nonneg hc hq)).mp hsq

private lemma p15_constant_bound (n : ℕ) :
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb : (11 : ℝ) / 10 * Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith
  calc
    (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * Real.sqrt (3 * (n : ℝ)) =
        ((11 : ℝ) / 10 * Real.sqrt 3) * (n : ℝ) ^ 2 := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      calc
        (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * (Real.sqrt 3 * Real.sqrt n) =
            (11 : ℝ) / 10 * Real.sqrt 3 * ((n : ℝ) * (Real.sqrt n) ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hn]; ring
    _ ≤ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)

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
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by dsimp [c]; have hu := fp.u_nonneg; positivity
  have hrow : ∀ i, p15VecNorm (A i) ≤ c * p15VecNorm (Q i) := by
    intro i
    obtain ⟨deltaL, hbound, heq⟩ :=
      p15_backward_matrix fp m n X R hdiag hupper hvalid i
    exact hperturb i deltaL hbound heq
  have hagg := p15_norm_aggregate Q A c hc hrow
  have hQpos : 0 ≤ p15FrobNorm Q := Real.sqrt_nonneg _
  have hconst := p15_constant_bound n
  have hu := fp.u_nonneg
  dsimp [A, Q] at hagg hQFrob
  dsimp [c] at hagg
  calc
    p15FrobNorm (p15Residual (p15RoundedQ fp X R) R X) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p15FrobNorm (p15RoundedQ fp X R) := hagg
    _ ≤ ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob (by positivity)
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hconst) (mul_nonneg hu hxNorm)]

end VSCLReuse
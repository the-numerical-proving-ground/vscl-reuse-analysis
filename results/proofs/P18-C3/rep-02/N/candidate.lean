import VSCLReuse.P18.Definitions

namespace VSCLReuse

private theorem p18_one_plus_bounds {u δ : ℝ} (_hu : 0 ≤ u)
    (hδ : |δ| ≤ u) : 1 - u ≤ 1 + δ ∧ 1 + δ ≤ 1 + u := by
  constructor <;> have h := abs_le.mp hδ <;> linarith

private theorem p18_control_mul {r u c δ : ℝ}
    (hr : 0 ≤ r) (hu : 0 ≤ u) (hru : r + u < 1)
    (hc₁ : 1 - r ≤ c) (hc₂ : c ≤ 1 / (1 - r))
    (hδ : |δ| ≤ u) :
    1 - (r + u) ≤ c * (1 + δ) ∧
      c * (1 + δ) ≤ 1 / (1 - (r + u)) := by
  obtain ⟨hd₁, hd₂⟩ := p18_one_plus_bounds hu hδ
  have hrp : 0 < 1 - r := by linarith
  have hrup : 0 < 1 - (r + u) := by linarith
  have hdp : 0 ≤ 1 + δ := by linarith
  have hcp : 0 ≤ c := by linarith
  have hup : 0 ≤ 1 - u := by linarith
  have hlo : (1 - r) * (1 - u) ≤ c * (1 + δ) := by
    calc
      (1 - r) * (1 - u) ≤ c * (1 - u) := by gcongr
      _ ≤ c * (1 + δ) := by gcongr
  have hhi : c * (1 + δ) ≤ (1 / (1 - r)) * (1 + u) := by
    calc
      c * (1 + δ) ≤ (1 / (1 - r)) * (1 + δ) := by gcongr
      _ ≤ (1 / (1 - r)) * (1 + u) := by gcongr
  constructor
  · nlinarith
  · calc
      c * (1 + δ) ≤ (1 / (1 - r)) * (1 + u) := hhi
      _ ≤ 1 / (1 - (r + u)) := by
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff₀ hrp hrup).2
        nlinarith

private theorem p18_control_div {r u c δ : ℝ}
    (hr : 0 ≤ r) (hu : 0 ≤ u) (hru : r + u < 1)
    (hc₁ : 1 - r ≤ c) (hc₂ : c ≤ 1 / (1 - r))
    (hδ : |δ| ≤ u) :
    1 - (r + u) ≤ c / (1 + δ) ∧
      c / (1 + δ) ≤ 1 / (1 - (r + u)) := by
  obtain ⟨hd₁, hd₂⟩ := p18_one_plus_bounds hu hδ
  have hrp : 0 < 1 - r := by linarith
  have hrup : 0 < 1 - (r + u) := by linarith
  have hdp : 0 < 1 + δ := by linarith
  constructor
  · apply (le_div_iff₀ hdp).2
    have hcl : (1 - (r + u)) * (1 + δ) ≤ c := by
      calc
        (1 - (r + u)) * (1 + δ) ≤
            (1 - (r + u)) * (1 + u) := by gcongr
        _ ≤ 1 - r := by nlinarith
        _ ≤ c := hc₁
    exact hcl
  · apply (div_le_iff₀ hdp).2
    have hcu : c * (1 - r) ≤ 1 := (le_div_iff₀ hrp).1 hc₂
    have hcp : 0 ≤ c := by linarith
    have haux : 1 - (r + u) ≤ (1 - r) * (1 + δ) := by
      calc
        1 - (r + u) ≤ (1 - r) * (1 - u) := by nlinarith
        _ ≤ (1 - r) * (1 + δ) := by gcongr
    rw [div_mul_eq_mul_div, one_mul]
    apply (le_div_iff₀ hrup).2
    calc
      c * (1 - (r + u)) ≤ c * ((1 - r) * (1 + δ)) := by gcongr
      _ = (c * (1 - r)) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := by gcongr
      _ = 1 + δ := by ring

private theorem p18_control_abs {r v q : ℝ}
    (hr : 0 ≤ r) (hrv : r ≤ v) (hv : v < 1)
    (hq₁ : 1 - r ≤ q) (hq₂ : q ≤ 1 / (1 - r)) :
    |q - 1| ≤ v / (1 - v) := by
  have hv₀ : 0 ≤ v := le_trans hr hrv
  have hvp : 0 < 1 - v := by linarith
  have hrp : 0 < 1 - r := by linarith
  apply abs_le.mpr
  constructor
  · have h : r ≤ v / (1 - v) := by
      apply (le_div_iff₀ hvp).2
      nlinarith
    linarith
  · have h : 1 / (1 - r) ≤ 1 / (1 - v) := by
      apply (div_le_div_iff₀ hrp hvp).2
      linarith
    have heq : 1 / (1 - v) - 1 = v / (1 - v) := by
      field_simp
      ring
    linarith

private noncomputable def p18RowFold (fp : P18FPModel) (k : ℕ)
    (a x : ℕ → ℝ) (b : ℝ) : ℝ :=
  Fin.foldl k
    (fun acc j => fp.fl_sub acc (fp.fl_mul (a j.val) (x j.val))) b

private theorem p18_row_fold_backward (fp : P18FPModel) (n k : ℕ)
    (a x : ℕ → ℝ) (b : ℝ)
    (hk : k ≤ n) (hvalid : P18GammaValid fp.u n) :
    ∃ (c : ℝ) (w : ℕ → ℝ),
      b = c * p18RowFold fp k a x b +
        ∑ j ∈ Finset.range k, (w j * a j) * x j ∧
      1 - (k : ℝ) * fp.u ≤ c ∧
      c ≤ 1 / (1 - (k : ℝ) * fp.u) ∧
      (∀ j < k, |w j - 1| ≤ p18Gamma fp.u n) := by
  induction k with
  | zero =>
      refine ⟨1, fun _ => 1, ?_, ?_, ?_, ?_⟩
      · simp [p18RowFold]
      · simp
      · simp
      · simp
  | succ k ih =>
      have hk' : k ≤ n := by omega
      obtain ⟨c, w, heq, hc₁, hc₂, hw⟩ := ih hk'
      let s := p18RowFold fp k a x b
      obtain ⟨δm, hδm, hm⟩ := fp.model_mul (a k) (x k)
      obtain ⟨δs, hδs, hs⟩ := fp.model_sub s (fp.fl_mul (a k) (x k))
      have hr : 0 ≤ (k : ℝ) * fp.u := mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
      have hru : (k : ℝ) * fp.u + fp.u < 1 := by
        have hle : ((k + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) fp.u_nonneg
        simpa [P18GammaValid, Nat.cast_add, add_mul] using lt_of_le_of_lt hle hvalid
      obtain ⟨hc'₁, hc'₂⟩ := p18_control_div hr fp.u_nonneg hru hc₁ hc₂ hδs
      obtain ⟨hw'₁, hw'₂⟩ := p18_control_mul hr fp.u_nonneg hru hc₁ hc₂ hδm
      let w' : ℕ → ℝ := Function.update w k (c * (1 + δm))
      refine ⟨c / (1 + δs), w', ?_, ?_, ?_, ?_⟩
      · rw [p18RowFold, Fin.foldl_succ_last]
        change b = c / (1 + δs) *
          fp.fl_sub s (fp.fl_mul (a k) (x k)) +
          ∑ j ∈ Finset.range (k + 1), (w' j * a j) * x j
        rw [hs, hm, Finset.sum_range_succ]
        have hds : 1 + δs ≠ 0 := by
          have hδ := p18_one_plus_bounds fp.u_nonneg hδs
          exact ne_of_gt (by linarith [hru, hδ.1])
        have hsum : ∑ j ∈ Finset.range k, (w' j * a j) * x j =
            ∑ j ∈ Finset.range k, (w j * a j) * x j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j ≠ k := by
            have := Finset.mem_range.mp hj
            omega
          simp [w', hjk]
        rw [hsum]
        simp only [w', Function.update_self]
        rw [heq]
        field_simp
        ring
      · simpa [Nat.cast_add, add_mul] using hc'₁
      · simpa [Nat.cast_add, add_mul] using hc'₂
      · intro j hj
        by_cases hjk : j = k
        · subst j
          have hle : ((k + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) fp.u_nonneg
          have habs := p18_control_abs
            (add_nonneg hr fp.u_nonneg)
            (by simpa [Nat.cast_add, add_mul] using hle)
            hvalid hw'₁ hw'₂
          simpa [w', Function.update_self, p18Gamma] using habs
        · have hjlt : j < k := by omega
          simpa [w', Function.update, hjk] using hw j hjlt

private theorem p18_row_solve_backward (fp : P18FPModel) (n k : ℕ)
    (a x : ℕ → ℝ) (b diag : ℝ)
    (hk : k + 1 ≤ n) (hdiag : diag ≠ 0)
    (hvalid : P18GammaValid fp.u n) :
    ∃ d : ℕ → ℝ,
      (∀ j < k, |d j| ≤ p18Gamma fp.u n * |a j|) ∧
      |d k| ≤ p18Gamma fp.u n * |diag| ∧
      b = (diag + d k) *
          fp.fl_div (p18RowFold fp k a x b) diag +
        ∑ j ∈ Finset.range k, (a j + d j) * x j := by
  have hk' : k ≤ n := by omega
  obtain ⟨c, w, heq, hc₁, hc₂, hw⟩ :=
    p18_row_fold_backward fp n k a x b hk' hvalid
  let s := p18RowFold fp k a x b
  let xi := fp.fl_div s diag
  obtain ⟨δ, hδ, hxi⟩ := fp.model_div s diag hdiag
  have hr : 0 ≤ (k : ℝ) * fp.u :=
    mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
  have hru : (k : ℝ) * fp.u + fp.u < 1 := by
    have hle : ((k + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) fp.u_nonneg
    simpa [P18GammaValid, Nat.cast_add, add_mul] using lt_of_le_of_lt hle hvalid
  obtain ⟨hq₁, hq₂⟩ :=
    p18_control_div hr fp.u_nonneg hru hc₁ hc₂ hδ
  have hle : (k : ℝ) * fp.u + fp.u ≤ (n : ℝ) * fp.u := by
    have hle' : ((k + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) fp.u_nonneg
    simpa [Nat.cast_add, add_mul] using hle'
  have hq : |c / (1 + δ) - 1| ≤ p18Gamma fp.u n := by
    simpa [p18Gamma] using
      p18_control_abs (add_nonneg hr fp.u_nonneg) hle hvalid hq₁ hq₂
  have hdp : 0 < 1 + δ := by
    have hbound := (p18_one_plus_bounds fp.u_nonneg hδ).1
    linarith
  have hs : s = diag * xi / (1 + δ) := by
    dsimp [xi] at *
    rw [hxi]
    field_simp
  let d : ℕ → ℝ := fun j =>
    if j = k then diag * (c / (1 + δ) - 1)
    else a j * (w j - 1)
  refine ⟨d, ?_, ?_, ?_⟩
  · intro j hj
    have hjk : j ≠ k := by omega
    simp only [d, if_neg hjk, abs_mul]
    calc
      |a j| * |w j - 1| ≤ |a j| * p18Gamma fp.u n := by gcongr; exact hw j hj
      _ = p18Gamma fp.u n * |a j| := by ring
  · simp only [d, if_pos rfl, abs_mul]
    calc
      |diag| * |c / (1 + δ) - 1| ≤ |diag| * p18Gamma fp.u n := by gcongr
      _ = p18Gamma fp.u n * |diag| := by ring
  · have hsum : ∑ j ∈ Finset.range k, (a j + d j) * x j =
        ∑ j ∈ Finset.range k, (w j * a j) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≠ k := by
        have := Finset.mem_range.mp hj
        omega
      simp only [d, if_neg hjk]
      ring
    rw [hsum]
    have hdiag' : diag + d k = diag * (c / (1 + δ)) := by
      simp only [d, if_pos rfl]
      ring
    rw [hdiag']
    calc
      b = c * s + ∑ j ∈ Finset.range k, (w j * a j) * x j := heq
      _ = (diag * (c / (1 + δ))) * xi +
            ∑ j ∈ Finset.range k, (w j * a j) * x j := by
          rw [hs]
          ring

private def p18NatAt {n : ℕ} (v : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then v ⟨j, h⟩ else 0

private theorem p18NatAt_lt {n : ℕ} (v : Fin n → ℝ) (j : ℕ)
    (hj : j < n) : p18NatAt v j = v ⟨j, hj⟩ := by
  simp [p18NatAt, hj]

private theorem p18_forward_steps_preserve (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i.val < n - k) :
    p18ForwardSubSteps fp n L b k hk x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ n := by omega
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      change p18ForwardSubSteps fp n L b k hk' x' i = x i
      rw [ih hk' x' (by omega)]
      have hne : i ≠ ik := by
        intro h
        have := congrArg Fin.val h
        dsimp [ik] at this
        omega
      simp [x', hne]

private theorem p18_forward_steps_rows (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    let y := p18ForwardSubSteps fp n L b k hk x
    ∀ i : Fin n, n - k ≤ i.val →
      y i = fp.fl_div
        (p18RowFold fp i.val (p18NatAt (L i)) (p18NatAt y) (b i))
        (L i i) := by
  induction k generalizing x with
  | zero =>
      intro y i hi
      have := i.isLt
      omega
  | succ k ih =>
      intro y i hi
      have hk' : k ≤ n := by omega
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hy : y = p18ForwardSubSteps fp n L b k hk' x' := by
        rfl
      by_cases hcurrent : i = ik
      · rw [hcurrent]
        have hpres : y ik = x' ik := by
          rw [hy]
          exact p18_forward_steps_preserve fp n L b k hk' x' ik (by dsimp [ik]; omega)
        rw [hpres]
        have hrow : p18RowFold fp ik.val (p18NatAt (L ik))
            (p18NatAt y) (b ik) = s := by
          dsimp [p18RowFold, s]
          simp only [show ik.val = n - k - 1 from rfl]
          congr 1
          funext acc t
          have ht : t.val < n := by
            have := t.isLt
            dsimp [ik] at *
            omega
          have hpre : y ⟨t.val, ht⟩ = x ⟨t.val, ht⟩ := by
            rw [hy, p18_forward_steps_preserve fp n L b k hk' x' ⟨t.val, ht⟩
              (by dsimp [ik] at *; omega)]
            have hne : (⟨t.val, ht⟩ : Fin n) ≠ ik := by
              intro h
              have := congrArg Fin.val h
              dsimp [ik] at this
              omega
            simp [x', hne]
          simp [p18NatAt_lt, ht, hpre]
        simp [x', Function.update_self, hrow]
      · have hi' : n - k ≤ i.val := by
          have hlt : n - k - 1 < i.val := by
            have hle : n - k - 1 ≤ i.val := hi
            have hneq : i.val ≠ n - k - 1 := by
              intro h
              apply hcurrent
              exact Fin.ext h
            omega
          omega
        rw [hy]
        exact ih hk' x' i hi'

private theorem p18_forward_rows (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) (i : Fin n) :
    let y := p18ForwardSub fp n L b
    y i = fp.fl_div
      (p18RowFold fp i.val (p18NatAt (L i)) (p18NatAt y) (b i))
      (L i i) := by
  exact p18_forward_steps_rows fp n L b n (le_refl n) (fun _ => 0) i
    (by simp)

private noncomputable def p18BackRowFold (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b y : Fin n → ℝ) (i : Fin n) : ℝ :=
  p18RowFold fp (n - i.val - 1)
    (fun t => p18NatAt (U i) (i.val + 1 + t))
    (fun t => p18NatAt y (i.val + 1 + t)) (b i)

private theorem p18_back_steps_preserve (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) (i : Fin n) (hi : k ≤ i.val) :
    p18BackSubSteps fp n U b k hk x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ n := by omega
      let ik : Fin n := ⟨k, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      change p18BackSubSteps fp n U b k hk' x' i = x i
      rw [ih hk' x' (by omega)]
      have hne : i ≠ ik := by
        intro h
        have := congrArg Fin.val h
        dsimp [ik] at this
        omega
      simp [x', hne]

private theorem p18_back_steps_rows (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) :
    let y := p18BackSubSteps fp n U b k hk x
    ∀ i : Fin n, i.val < k →
      y i = fp.fl_div (p18BackRowFold fp n U b y i) (U i i) := by
  induction k generalizing x with
  | zero =>
      intro y i hi
      omega
  | succ k ih =>
      intro y i hi
      have hk' : k ≤ n := by omega
      let ik : Fin n := ⟨k, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hy : y = p18BackSubSteps fp n U b k hk' x' := by rfl
      by_cases hcurrent : i = ik
      · rw [hcurrent]
        have hpres : y ik = x' ik := by
          rw [hy]
          exact p18_back_steps_preserve fp n U b k hk' x' ik (by dsimp [ik]; omega)
        rw [hpres]
        have hrow : p18BackRowFold fp n U b y ik = s := by
          dsimp [p18BackRowFold, p18RowFold, s]
          simp only [show ik.val = k from rfl]
          congr 1
          funext acc t
          have ht : k + 1 + t.val < n := by
            have := t.isLt
            omega
          have hpost : y ⟨k + 1 + t.val, ht⟩ =
              x ⟨k + 1 + t.val, ht⟩ := by
            rw [hy, p18_back_steps_preserve fp n U b k hk' x'
              ⟨k + 1 + t.val, ht⟩ (by change k ≤ k + 1 + t.val; omega)]
            have hne : (⟨k + 1 + t.val, ht⟩ : Fin n) ≠ ik := by
              intro h
              have := congrArg Fin.val h
              dsimp [ik] at this
              omega
            simp [x', hne]
          simp [p18NatAt_lt, ht, hpost]
        simp [x', Function.update_self, hrow]
      · have hi' : i.val < k := by
          have hneq : i.val ≠ k := by
            intro h
            apply hcurrent
            exact Fin.ext h
          omega
        rw [hy]
        exact ih hk' x' i hi'

private theorem p18_back_rows (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) (i : Fin n) :
    let y := p18BackSub fp n U b
    y i = fp.fl_div (p18BackRowFold fp n U b y i) (U i i) := by
  exact p18_back_steps_rows fp n U b n (le_refl n) (fun _ => 0) i i.isLt

private theorem p18_sum_split {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin n, f j) =
      (∑ t ∈ Finset.range i.val, p18NatAt f t) + f i +
      ∑ t ∈ Finset.range (n - i.val - 1),
        p18NatAt f (i.val + 1 + t) := by
  have hn : i.val + 1 + (n - i.val - 1) = n := by omega
  rw [Finset.sum_fin_eq_sum_range]
  change (∑ t ∈ Finset.range n, p18NatAt f t) = _
  calc
    (∑ t ∈ Finset.range n, p18NatAt f t) =
        ∑ t ∈ Finset.range (i.val + 1 + (n - i.val - 1)),
          p18NatAt f t :=
      congrArg (fun m => ∑ t ∈ Finset.range m, p18NatAt f t) hn.symm
    _ = _ := by
      rw [Finset.sum_range_add, Finset.sum_range_succ]
      simp [p18NatAt_lt, i.isLt]

private theorem p18_forward_backward_matrix (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    ∃ ΔL : P18Matrix n n,
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      (∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p18ForwardSub fp n L b j = b i) := by
  let y := p18ForwardSub fp n L b
  have hγ : 0 ≤ p18Gamma fp.u n := by
    unfold p18Gamma
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    · have := hvalid
      dsimp [P18GammaValid] at this
      linarith
  have row (i : Fin n) :
      ∃ d : ℕ → ℝ,
        (∀ j < i.val, |d j| ≤ p18Gamma fp.u n * |p18NatAt (L i) j|) ∧
        |d i.val| ≤ p18Gamma fp.u n * |L i i| ∧
        b i = (L i i + d i.val) * y i +
          ∑ j ∈ Finset.range i.val,
            (p18NatAt (L i) j + d j) * p18NatAt y j := by
    obtain ⟨d, hdlo, hddi, heq⟩ :=
      p18_row_solve_backward fp n i.val (p18NatAt (L i))
        (p18NatAt y) (b i) (L i i)
        (by have := i.isLt; omega) (hdiag i) hvalid
    have hy := p18_forward_rows fp n L b i
    dsimp only at hy
    refine ⟨d, hdlo, hddi, ?_⟩
    rw [← hy] at heq
    exact heq
  choose d hdlo hddi heq using row
  let ΔL : P18Matrix n n := fun i j =>
    if j.val < i.val then d i j.val
    else if j = i then d i i.val else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    by_cases hjlo : j.val < i.val
    · simp only [ΔL, if_pos hjlo]
      simpa [p18NatAt_lt (L i) j.val j.isLt] using hdlo i j.val hjlo
    · by_cases hdiag' : j = i
      · subst j
        simpa [ΔL, hjlo] using hddi i
      · simp only [ΔL, if_neg hjlo, if_neg hdiag', abs_zero]
        positivity
  · intro i
    have hsplit := p18_sum_split i (fun j => (L i j + ΔL i j) * y j)
    have hsumlo : (∑ t ∈ Finset.range i.val,
        p18NatAt (fun j => (L i j + ΔL i j) * y j) t) =
        ∑ t ∈ Finset.range i.val,
          (p18NatAt (L i) t + d i t) * p18NatAt y t := by
      apply Finset.sum_congr rfl
      intro t ht
      have hti : t < i.val := Finset.mem_range.mp ht
      have htn : t < n := lt_trans hti i.isLt
      have hΔ : ΔL i ⟨t, htn⟩ = d i t := by
        dsimp [ΔL]
        rw [if_pos (by exact hti)]
      simp [p18NatAt_lt, htn, hΔ]
    have hupper : (∑ t ∈ Finset.range (n - i.val - 1),
        p18NatAt (fun j => (L i j + ΔL i j) * y j) (i.val + 1 + t)) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have htn : i.val + 1 + t < n := by
        have := Finset.mem_range.mp ht
        omega
      let j : Fin n := ⟨i.val + 1 + t, htn⟩
      have hij : i.val < j.val := by dsimp [j]; omega
      have hLi : L i j = 0 := hlower i j hij
      have hΔ : ΔL i j = 0 := by
        dsimp [ΔL]
        rw [if_neg (by omega)]
        rw [if_neg (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)]
      simp [p18NatAt_lt, htn, j, hLi, hΔ]
    rw [hsplit, hsumlo, hupper]
    have hdiag' : ΔL i i = d i i.val := by
      simp [ΔL]
    rw [hdiag']
    simpa [y, add_assoc, add_comm, add_left_comm] using (heq i).symm

private theorem p18_back_backward_matrix (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    ∃ ΔU : P18Matrix n n,
      (∀ i j, |ΔU i j| ≤ p18Gamma fp.u n * |U i j|) ∧
      (∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p18BackSub fp n U b j = b i) := by
  let y := p18BackSub fp n U b
  have hγ : 0 ≤ p18Gamma fp.u n := by
    unfold p18Gamma
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    · have := hvalid
      dsimp [P18GammaValid] at this
      linarith
  have row (i : Fin n) :
      ∃ d : ℕ → ℝ,
        (∀ t < n - i.val - 1,
          |d t| ≤ p18Gamma fp.u n *
            |p18NatAt (U i) (i.val + 1 + t)|) ∧
        |d (n - i.val - 1)| ≤ p18Gamma fp.u n * |U i i| ∧
        b i = (U i i + d (n - i.val - 1)) * y i +
          ∑ t ∈ Finset.range (n - i.val - 1),
            (p18NatAt (U i) (i.val + 1 + t) + d t) *
              p18NatAt y (i.val + 1 + t) := by
    obtain ⟨d, hdhi, hddi, heq⟩ :=
      p18_row_solve_backward fp n (n - i.val - 1)
        (fun t => p18NatAt (U i) (i.val + 1 + t))
        (fun t => p18NatAt y (i.val + 1 + t))
        (b i) (U i i)
        (by have := i.isLt; omega) (hdiag i) hvalid
    have hy := p18_back_rows fp n U b i
    dsimp only at hy
    refine ⟨d, hdhi, hddi, ?_⟩
    rw [p18BackRowFold] at hy
    rw [← hy] at heq
    exact heq
  choose d hdhi hddi heq using row
  let ΔU : P18Matrix n n := fun i j =>
    if i.val < j.val then d i (j.val - i.val - 1)
    else if j = i then d i (n - i.val - 1) else 0
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    by_cases hij : i.val < j.val
    · have ht : j.val - i.val - 1 < n - i.val - 1 := by omega
      have hidx : i.val + 1 + (j.val - i.val - 1) = j.val := by omega
      simp only [ΔU, if_pos hij]
      have hb := hdhi i (j.val - i.val - 1) ht
      simpa [hidx, p18NatAt_lt (U i) j.val j.isLt] using hb
    · by_cases hdiag' : j = i
      · subst j
        simpa [ΔU, hij] using hddi i
      · simp only [ΔU, if_neg hij, if_neg hdiag', abs_zero]
        positivity
  · intro i
    have hsplit := p18_sum_split i (fun j => (U i j + ΔU i j) * y j)
    have hsumlo : (∑ t ∈ Finset.range i.val,
        p18NatAt (fun j => (U i j + ΔU i j) * y j) t) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hti : t < i.val := Finset.mem_range.mp ht
      have htn : t < n := lt_trans hti i.isLt
      let j : Fin n := ⟨t, htn⟩
      have hU : U i j = 0 := hupper i j hti
      have hΔ : ΔU i j = 0 := by
        dsimp [ΔU]
        rw [if_neg (by dsimp [j]; omega)]
        rw [if_neg (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)]
      simp [p18NatAt_lt, htn, j, hU, hΔ]
    have hsumhi : (∑ t ∈ Finset.range (n - i.val - 1),
        p18NatAt (fun j => (U i j + ΔU i j) * y j) (i.val + 1 + t)) =
        ∑ t ∈ Finset.range (n - i.val - 1),
          (p18NatAt (U i) (i.val + 1 + t) + d i t) *
            p18NatAt y (i.val + 1 + t) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htt : t < n - i.val - 1 := Finset.mem_range.mp ht
      have htn : i.val + 1 + t < n := by omega
      let j : Fin n := ⟨i.val + 1 + t, htn⟩
      have hij : i.val < j.val := by dsimp [j]; omega
      have hidx : j.val - i.val - 1 = t := by dsimp [j]; omega
      have hΔ : ΔU i j = d i t := by
        dsimp [ΔU]
        rw [if_pos hij, hidx]
      simp [p18NatAt_lt, htn, j, hΔ]
    rw [hsplit, hsumlo, hsumhi]
    have hdiag' : ΔU i i = d i (n - i.val - 1) := by
      simp [ΔU]
    rw [hdiag']
    simpa [y, add_assoc, add_comm, add_left_comm] using (heq i).symm

private theorem p18_entry_norm_nonneg {m n : ℕ}
    (M : P18Matrix m n) : 0 ≤ p18EntryNorm M := by
  unfold p18EntryNorm
  positivity

private theorem p18_entry_le_norm {m n : ℕ}
    (M : P18Matrix m n) (i : Fin m) (j : Fin n) :
    |M i j| ≤ p18EntryNorm M := by
  unfold p18EntryNorm
  have hrow : |M i j| ≤ ∑ k : Fin n, |M i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (M i k)) (Finset.mem_univ j)
  have htotal : (∑ k : Fin n, |M i k|) ≤
      ∑ l : Fin m, ∑ k : Fin n, |M l k| :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg fun k _ => abs_nonneg (M l k))
      (Finset.mem_univ i)
  exact le_trans hrow htotal

private theorem p18_entry_norm_le {m n : ℕ}
    (M N : P18Matrix m n) (c : ℝ)
    (h : ∀ i j, |M i j| ≤ c * |N i j|) :
    p18EntryNorm M ≤ c * p18EntryNorm N := by
  unfold p18EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |M i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |N i j| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact h i j
    _ = c * (∑ i : Fin m, ∑ j : Fin n, |N i j|) := by
      simp_rw [← Finset.mul_sum]

private theorem p18_entry_norm_add {m n : ℕ}
    (M N : P18Matrix m n) :
    p18EntryNorm (M + N) ≤ p18EntryNorm M + p18EntryNorm N := by
  unfold p18EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |(M + N) i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|M i j| + |N i j|) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simpa using abs_add_le (M i j) (N i j)
    _ = (∑ i : Fin m, ∑ j : Fin n, |M i j|) +
          (∑ i : Fin m, ∑ j : Fin n, |N i j|) := by
      simp_rw [Finset.sum_add_distrib]

private theorem p18_entry_norm_sub {m n : ℕ}
    (M N : P18Matrix m n) :
    p18EntryNorm (M - N) ≤ p18EntryNorm M + p18EntryNorm N := by
  unfold p18EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |(M - N) i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|M i j| + |N i j|) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          simpa using abs_sub (M i j) (N i j)
    _ = (∑ i : Fin m, ∑ j : Fin n, |M i j|) +
          (∑ i : Fin m, ∑ j : Fin n, |N i j|) := by
      simp_rw [Finset.sum_add_distrib]

private theorem p18_entry_norm_mul {n : ℕ}
    (M N : P18Matrix n n) :
    p18EntryNorm (p18MatMul M N) ≤
      (n : ℝ) ^ 3 * p18EntryNorm M * p18EntryNorm N := by
  have hpoint (i j : Fin n) :
      |p18MatMul M N i j| ≤
        (n : ℝ) * (p18EntryNorm M * p18EntryNorm N) := by
    unfold p18MatMul
    calc
      |∑ k : Fin n, M i k * N k j| ≤
          ∑ k : Fin n, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, p18EntryNorm M * p18EntryNorm N := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul (p18_entry_le_norm M i k)
          (p18_entry_le_norm N k j) (abs_nonneg _) (p18_entry_norm_nonneg M)
      _ = (n : ℝ) * (p18EntryNorm M * p18EntryNorm N) := by simp
  unfold p18EntryNorm
  calc
    (∑ i : Fin n, ∑ j : Fin n, |p18MatMul M N i j|) ≤
        ∑ _i : Fin n, ∑ _j : Fin n,
          (n : ℝ) * (p18EntryNorm M * p18EntryNorm N) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact hpoint i j
    _ = (n : ℝ) ^ 3 * p18EntryNorm M * p18EntryNorm N := by
      simp
      ring

private theorem p18_entry_norm_triple {n : ℕ}
    (M N P : P18Matrix n n) :
    p18EntryNorm (p18MatMul (p18MatMul M N) P) ≤
      (n : ℝ) ^ 6 * p18EntryNorm M *
        p18EntryNorm N * p18EntryNorm P := by
  have h₁ := p18_entry_norm_mul M N
  have h₂ := p18_entry_norm_mul (p18MatMul M N) P
  have hn : 0 ≤ (n : ℝ) ^ 3 := by positivity
  have hp := p18_entry_norm_nonneg P
  calc
    p18EntryNorm (p18MatMul (p18MatMul M N) P) ≤
        (n : ℝ) ^ 3 * p18EntryNorm (p18MatMul M N) *
          p18EntryNorm P := h₂
    _ ≤ (n : ℝ) ^ 3 *
          ((n : ℝ) ^ 3 * p18EntryNorm M * p18EntryNorm N) *
          p18EntryNorm P := by gcongr
    _ = (n : ℝ) ^ 6 * p18EntryNorm M *
          p18EntryNorm N * p18EntryNorm P := by ring

private theorem p18_matmul_add_left {n : ℕ}
    (M N P : P18Matrix n n) :
    p18MatMul (M + N) P = p18MatMul M P + p18MatMul N P := by
  ext i j
  simp [p18MatMul, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem p18_matmul_add_right {n : ℕ}
    (M N P : P18Matrix n n) :
    p18MatMul M (N + P) = p18MatMul M N + p18MatMul M P := by
  ext i j
  simp [p18MatMul, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem p18_combined_expansion {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L D) ΔU := by
  unfold p18CombinedBackwardError p18PerturbedLDLT p18LDLT
  rw [p18_matmul_add_left L ΔL (D + ΔD),
    p18_matmul_add_left (p18MatMul L (D + ΔD))
      (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU),
    p18_matmul_add_right L D ΔD,
    p18_matmul_add_left (p18MatMul L D) (p18MatMul L ΔD)
      (p18Transpose L + ΔU),
    p18_matmul_add_right (p18MatMul L D) (p18Transpose L) ΔU]
  abel

private theorem p18_matvec_mul {n : ℕ}
    (M N : P18Matrix n n) (x : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, p18MatMul M N i j * x j) =
      ∑ k : Fin n, M i k * (∑ j : Fin n, N k j * x j) := by
  simp only [p18MatMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem p18_combined_norm_bound (fp : P18FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (heta : 0 ≤ eta)
    (hvalid : P18GammaValid fp.u n)
    (hΔL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hΔD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hΔU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18SolveBackwardFactor fp n eta L D := by
  let g := p18Gamma fp.u n
  let t := (n : ℝ) ^ 6
  let U := p18Transpose L
  have hg : 0 ≤ g := by
    dsimp [g, p18Gamma]
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    · have := hvalid
      dsimp [P18GammaValid] at this
      linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hLnorm : 0 ≤ p18EntryNorm L := p18_entry_norm_nonneg L
  have hDnorm : 0 ≤ p18EntryNorm D := p18_entry_norm_nonneg D
  have hUnorm : 0 ≤ p18EntryNorm U := p18_entry_norm_nonneg U
  have hΔLnorm : p18EntryNorm ΔL ≤ g * p18EntryNorm L :=
    p18_entry_norm_le ΔL L g hΔL
  have hΔUnorm : p18EntryNorm ΔU ≤ g * p18EntryNorm U :=
    p18_entry_norm_le ΔU U g hΔU
  have hDplus : p18EntryNorm (D + ΔD) ≤
      (1 + eta) * p18EntryNorm D := by
    calc
      p18EntryNorm (D + ΔD) ≤
          p18EntryNorm D + p18EntryNorm ΔD := p18_entry_norm_add D ΔD
      _ ≤ p18EntryNorm D + eta * p18EntryNorm D := by gcongr
      _ = (1 + eta) * p18EntryNorm D := by ring
  have hUplus : p18EntryNorm (U + ΔU) ≤
      (1 + g) * p18EntryNorm U := by
    calc
      p18EntryNorm (U + ΔU) ≤
          p18EntryNorm U + p18EntryNorm ΔU := p18_entry_norm_add U ΔU
      _ ≤ p18EntryNorm U + g * p18EntryNorm U := by gcongr
      _ = (1 + g) * p18EntryNorm U := by ring
  have h₁ : p18EntryNorm
      (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU)) ≤
      t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
        (g * (1 + eta) * (1 + g)) := by
    calc
      p18EntryNorm (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU)) ≤
          t * p18EntryNorm ΔL * p18EntryNorm (D + ΔD) *
            p18EntryNorm (U + ΔU) := p18_entry_norm_triple ΔL (D + ΔD) (U + ΔU)
      _ ≤ t * (g * p18EntryNorm L) *
          ((1 + eta) * p18EntryNorm D) *
          ((1 + g) * p18EntryNorm U) := by
            gcongr
            all_goals exact p18_entry_norm_nonneg _
      _ = t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
          (g * (1 + eta) * (1 + g)) := by ring
  have h₂ : p18EntryNorm
      (p18MatMul (p18MatMul L ΔD) (U + ΔU)) ≤
      t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
        (eta * (1 + g)) := by
    calc
      p18EntryNorm (p18MatMul (p18MatMul L ΔD) (U + ΔU)) ≤
          t * p18EntryNorm L * p18EntryNorm ΔD *
            p18EntryNorm (U + ΔU) := p18_entry_norm_triple L ΔD (U + ΔU)
      _ ≤ t * p18EntryNorm L * (eta * p18EntryNorm D) *
          ((1 + g) * p18EntryNorm U) := by
            gcongr
            exact p18_entry_norm_nonneg _
      _ = t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
          (eta * (1 + g)) := by ring
  have h₃ : p18EntryNorm
      (p18MatMul (p18MatMul L D) ΔU) ≤
      t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U * g := by
    calc
      p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) ≤
          t * p18EntryNorm L * p18EntryNorm D *
            p18EntryNorm ΔU := p18_entry_norm_triple L D ΔU
      _ ≤ t * p18EntryNorm L * p18EntryNorm D *
          (g * p18EntryNorm U) := by gcongr
      _ = t * p18EntryNorm L * p18EntryNorm D *
          p18EntryNorm U * g := by ring
  rw [p18_combined_expansion]
  calc
    p18EntryNorm
        (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU) +
          p18MatMul (p18MatMul L ΔD) (U + ΔU) +
          p18MatMul (p18MatMul L D) ΔU) ≤
        p18EntryNorm (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU)) +
        p18EntryNorm (p18MatMul (p18MatMul L ΔD) (U + ΔU)) +
        p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) := by
          calc
            p18EntryNorm
                (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU) +
                  p18MatMul (p18MatMul L ΔD) (U + ΔU) +
                  p18MatMul (p18MatMul L D) ΔU) ≤
                p18EntryNorm
                  (p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU) +
                    p18MatMul (p18MatMul L ΔD) (U + ΔU)) +
                p18EntryNorm (p18MatMul (p18MatMul L D) ΔU) :=
                  p18_entry_norm_add _ _
            _ ≤ _ := by
              gcongr
              exact p18_entry_norm_add _ _
    _ ≤ t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
          (g * (1 + eta) * (1 + g)) +
        t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U *
          (eta * (1 + g)) +
        t * p18EntryNorm L * p18EntryNorm D * p18EntryNorm U * g := by
          exact add_le_add (add_le_add h₁ h₂) h₃
    _ = p18SolveBackwardFactor fp n eta L D := by
      unfold p18SolveBackwardFactor
      dsimp [t, g, U]
      ring

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
  obtain ⟨ΔL, hΔL, hLrow⟩ :=
    p18_forward_backward_matrix fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hDrow⟩ := hDsolve
  have hUdiag : ∀ i, p18Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val →
      p18Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hUrow⟩ :=
    p18_back_backward_matrix fp n (p18Transpose L) z
      hUdiag hUupper hvalid
  let F := p18TotalBackwardError E0 L D ΔL ΔD ΔU
  have hP (i : Fin n) :
      ∑ j : Fin n,
        p18PerturbedLDLT L D ΔL ΔD ΔU i j *
          p18BackSub fp n (p18Transpose L) z j = b i := by
    unfold p18PerturbedLDLT
    rw [p18_matvec_mul]
    have hUrow' (k : Fin n) :
        (∑ j : Fin n, (p18Transpose L + ΔU) k j *
          p18BackSub fp n (p18Transpose L) z j) = z k := hUrow k
    simp_rw [hUrow']
    rw [p18_matvec_mul]
    have hDrow' (k : Fin n) :
        (∑ j : Fin n, (D + ΔD) k j * z j) =
          p18ForwardSub fp n L b k := hDrow k
    simp_rw [hDrow']
    exact hLrow i
  have hAF : A + F = p18PerturbedLDLT L D ΔL ΔD ΔU := by
    ext i j
    have hf : p18LDLT L D i j = A i j + E0 i j :=
      congrArg (fun M : P18Matrix n n => M i j) hfactor
    dsimp [F, p18TotalBackwardError, p18CombinedBackwardError]
    rw [hf]
    ring
  have hFbound : p18EntryNorm F ≤
      p18TotalBackwardBound fp n eta factorEta A L D := by
    have hsolve :=
      p18_combined_norm_bound fp n eta L D ΔL ΔD ΔU
        heta hvalid hΔL hΔD hΔU
    calc
      p18EntryNorm F ≤
          p18EntryNorm E0 +
            p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) :=
              p18_entry_norm_add E0 _
      _ ≤ factorEta * p18EntryNorm A +
            p18SolveBackwardFactor fp n eta L D :=
              add_le_add hE0 hsolve
      _ = p18TotalBackwardBound fp n eta factorEta A L D := rfl
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, hFbound⟩
  intro i
  change ∑ j : Fin n,
    (A + F) i j * p18BackSub fp n (p18Transpose L) z j = b i
  rw [hAF]
  exact hP i

end VSCLReuse

import VSCLReuse.P18.Definitions

namespace VSCLReuse


private noncomputable def p18Coeff (u : ℝ) (n : ℕ) : ℝ :=
  u / (1 - (n : ℝ) * u)

private lemma p18_coeff_basic (u : ℝ) (n k : ℕ)
    (hu : 0 ≤ u) (hv : (n : ℝ) * u < 1) (hk : k + 1 ≤ n) :
    let c := p18Coeff u n
    0 ≤ c ∧ 0 ≤ 1 - u ∧
      ((k : ℝ) * c + u) ≤ ((k + 1 : ℕ) : ℝ) * c * (1 - u) ∧
      ((k : ℝ) * c * (1 + u) + u) ≤ ((k + 1 : ℕ) : ℝ) * c := by
  dsimp [p18Coeff]
  have hkn : (k + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  have hun : u < 1 := by
    have : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    nlinarith [mul_nonneg (sub_nonneg.mpr this) hu]
  have hc : 0 ≤ u / (1 - (n : ℝ) * u) := div_nonneg hu hden.le
  have hid : u / (1 - (n : ℝ) * u) * (1 - (n : ℝ) * u) = u :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hsmall : u ≤ u / (1 - (n : ℝ) * u) * (1 - (k + 1 : ℝ) * u) := by
    nlinarith [mul_nonneg hc (mul_nonneg (by linarith : 0 ≤ (n : ℝ) - (k + 1 : ℝ)) hu)]
  refine ⟨hc, by linarith, ?_, ?_⟩
  · push_cast
    nlinarith
  · have hsmall' : u ≤ u / (1 - (n : ℝ) * u) * (1 - (k : ℝ) * u) := by
      nlinarith [mul_nonneg hc hu]
    push_cast
    nlinarith

private lemma p18_sub_step (fp : P18FPModel)
    (a s t T p q α β : ℝ)
    (herr : |a - s - t| ≤ α * (|s| + T))
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α ≤ β)
    (hc₁ : α + fp.u ≤ β * (1 - fp.u))
    (hc₂ : α * (1 + fp.u) + fp.u ≤ β) :
    |a - fp.fl_sub s (fp.fl_mul p q) - (t + p * q)| ≤
      β * (|fp.fl_sub s (fp.fl_mul p q)| + (T + |p * q|)) := by
  let v := p * q
  let w := fp.fl_mul p q
  let s' := fp.fl_sub s w
  obtain ⟨μ, hμ, hw⟩ := fp.model_mul p q
  obtain ⟨σ, hσ, hs'⟩ := fp.model_sub s w
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hw_eq : w = v * (1 + μ) := by simpa [v, w] using hw
  have hs_eq : s' = (s - w) * (1 + σ) := by simpa [s', w] using hs'
  have hμ₁ : |μ| ≤ fp.u := hμ
  have hσ₁ : |σ| ≤ fp.u := hσ
  have hw_diff : |w - v| ≤ fp.u * |v| := by
    have heq : w - v = v * μ := by rw [hw_eq]; ring
    rw [heq, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hμ₁ (abs_nonneg v)
  have hw_abs : |w| ≤ (1 + fp.u) * |v| := by
    calc
      |w| = |v + (w - v)| := by congr 1; ring
      _ ≤ |v| + |w - v| := abs_add_le _ _
      _ ≤ (1 + fp.u) * |v| := by nlinarith [hw_diff]
  have hsub_diff : |(s - w) - s'| ≤ fp.u * |s - w| := by
    have heq : (s - w) - s' = -(s - w) * σ := by rw [hs_eq]; ring
    rw [heq, abs_mul, abs_neg]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hσ₁ (abs_nonneg (s - w))
  have hsub_lower : (1 - fp.u) * |s - w| ≤ |s'| := by
    have htri : |s - w| ≤ |s'| + |(s - w) - s'| := by
      calc
        |s - w| = |s' + ((s - w) - s')| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    nlinarith
  have hs_abs : |s| ≤ |s - w| + |w| := by
    calc
      |s| = |(s - w) + w| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hstep : |s - s' - v| ≤ fp.u * |s - w| + fp.u * |v| := by
    have heq : s - s' - v = ((s - w) - s') + (w - v) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans (add_le_add hsub_diff hw_diff)
  have htri : |a - s' - (t + v)| ≤ |a - s - t| + |s - s' - v| := by
    have heq : a - s' - (t + v) = (a - s - t) + (s - s' - v) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hlin : |a - s' - (t + v)| ≤
      (α + fp.u) * |s - w| + α * T +
        (α * (1 + fp.u) + fp.u) * |v| := by
    nlinarith [mul_nonneg hα (sub_nonneg.mpr hs_abs),
      mul_nonneg hα (sub_nonneg.mpr hw_abs)]
  have hfinal : (α + fp.u) * |s - w| + α * T +
      (α * (1 + fp.u) + fp.u) * |v| ≤
      β * (|s'| + (T + |v|)) := by
    have hcoef1 := mul_le_mul_of_nonneg_right hc₁ (abs_nonneg (s - w))
    have hcoef2 := mul_le_mul_of_nonneg_right hc₂ (abs_nonneg v)
    have hcoef3 := mul_le_mul_of_nonneg_right hαβ hT
    nlinarith
  simpa only [s', w, v] using hlin.trans hfinal

private lemma p18_fold_error (fp : P18FPModel) (n : ℕ)
    (hvalid : P18GammaValid fp.u n) :
    ∀ (m : ℕ) (_hm : m ≤ n) (x y : Fin m → ℝ) (a : ℝ),
      let s := Fin.foldl m
        (fun acc j => fp.fl_sub acc (fp.fl_mul (x j) (y j))) a
      |a - s - ∑ j : Fin m, x j * y j| ≤
        ((m : ℝ) * p18Coeff fp.u n) *
          (|s| + ∑ j : Fin m, |x j * y j|) := by
  intro m
  induction m with
  | zero =>
      intro hm x y a
      simp [Fin.foldl_zero]
  | succ m ih =>
      intro hm x y a
      let x' : Fin m → ℝ := fun j => x j.castSucc
      let y' : Fin m → ℝ := fun j => y j.castSucc
      let s := Fin.foldl m
        (fun acc j => fp.fl_sub acc (fp.fl_mul (x' j) (y' j))) a
      let t := ∑ j : Fin m, x' j * y' j
      let T := ∑ j : Fin m, |x' j * y' j|
      have hih := ih (by omega : m ≤ n) x' y' a
      have hT : 0 ≤ T := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      obtain ⟨hc, hu1, hc1, hc2⟩ :=
        p18_coeff_basic fp.u n m fp.u_nonneg hvalid hm
      have hα : 0 ≤ (m : ℝ) * p18Coeff fp.u n :=
        mul_nonneg (Nat.cast_nonneg _) hc
      have hβ : 0 ≤ ((m + 1 : ℕ) : ℝ) * p18Coeff fp.u n :=
        mul_nonneg (Nat.cast_nonneg _) hc
      have hαβ : (m : ℝ) * p18Coeff fp.u n ≤
          ((m + 1 : ℕ) : ℝ) * p18Coeff fp.u n := by
        push_cast
        nlinarith
      have hstep := p18_sub_step fp a s t T (x (Fin.last m)) (y (Fin.last m))
        ((m : ℝ) * p18Coeff fp.u n)
        (((m + 1 : ℕ) : ℝ) * p18Coeff fp.u n)
        hih hT hα hβ hαβ hc1 hc2
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        Finset.sum_add_distrib, x', y', s, t, T] using hstep

private lemma p18_div_finish (fp : P18FPModel) (n m : ℕ)
    (hvalid : P18GammaValid fp.u n) (hm : m + 1 ≤ n)
    (a s t T d : ℝ) (hd : d ≠ 0) (hT : 0 ≤ T)
    (herr : |a - s - t| ≤
      ((m : ℝ) * p18Coeff fp.u n) * (|s| + T)) :
    let x := fp.fl_div s d
    |a - (t + d * x)| ≤
      (((m + 1 : ℕ) : ℝ) * p18Coeff fp.u n) *
        (T + |d * x|) := by
  dsimp
  obtain ⟨δ, hδ, hx⟩ := fp.model_div s d hd
  let x := fp.fl_div s d
  have hdx : d * x = s * (1 + δ) := by
    change d * fp.fl_div s d = s * (1 + δ)
    rw [hx]
    field_simp
  have hdiff : |s - d * x| ≤ fp.u * |s| := by
    have heq : s - d * x = -(s * δ) := by rw [hdx]; ring
    rw [heq, abs_neg, abs_mul]
    exact (mul_le_mul_of_nonneg_left hδ (abs_nonneg s)).trans_eq (mul_comm _ _)
  have hlower : (1 - fp.u) * |s| ≤ |d * x| := by
    have htri : |s| ≤ |d * x| + |s - d * x| := by
      calc
        |s| = |d * x + (s - d * x)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    nlinarith
  obtain ⟨hc, hu1, hc1, hc2⟩ :=
    p18_coeff_basic fp.u n m fp.u_nonneg hvalid hm
  have hα : 0 ≤ (m : ℝ) * p18Coeff fp.u n :=
    mul_nonneg (Nat.cast_nonneg _) hc
  have hαβ : (m : ℝ) * p18Coeff fp.u n ≤
      ((m + 1 : ℕ) : ℝ) * p18Coeff fp.u n := by
    push_cast
    nlinarith
  have htri : |a - (t + d * x)| ≤ |a - s - t| + |s - d * x| := by
    have heq : a - (t + d * x) = (a - s - t) + (s - d * x) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hlin : |a - (t + d * x)| ≤
      ((m : ℝ) * p18Coeff fp.u n + fp.u) * |s| +
        ((m : ℝ) * p18Coeff fp.u n) * T := by
    nlinarith
  have hcoef1 := mul_le_mul_of_nonneg_right hc1 (abs_nonneg s)
  have hcoef2 := mul_le_mul_of_nonneg_right hαβ hT
  nlinarith

private def p18Below {n : ℕ} (i : Fin n) (j : Fin i.val) : Fin n :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

private def p18Above {n : ℕ} (i : Fin n)
    (j : Fin (n - i.val - 1)) : Fin n :=
  ⟨i.val + 1 + j.val, by omega⟩

private lemma p18_sum_split {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin n, f j) =
      (∑ j : Fin i.val, f (p18Below i j)) + f i +
        ∑ j : Fin (n - i.val - 1), f (p18Above i j) := by
  let g : ℕ → ℝ := fun j => if hj : j < n then f ⟨j, hj⟩ else 0
  have hfull : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g n)
  have hbelow : (∑ j : Fin i.val, f (p18Below i j)) =
      ∑ j ∈ Finset.range i.val, g j := by
    calc
      (∑ j : Fin i.val, f (p18Below i j)) =
          ∑ j : Fin i.val, g j.val := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : j.val < n := lt_trans j.isLt i.isLt
            simp [g, p18Below, hjlt]
      _ = _ := Fin.sum_univ_eq_sum_range g i.val
  have habove : (∑ j : Fin (n - i.val - 1), f (p18Above i j)) =
      ∑ j ∈ Finset.range (n - i.val - 1), g (i.val + 1 + j) := by
    calc
      (∑ j : Fin (n - i.val - 1), f (p18Above i j)) =
          ∑ j : Fin (n - i.val - 1), g (i.val + 1 + j.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjlt : i.val + 1 + j.val < n := by
              have := j.isLt
              omega
            simp [g, p18Above, hjlt]
      _ = _ := Fin.sum_univ_eq_sum_range
        (fun j => g (i.val + 1 + j)) (n - i.val - 1)
  have hi : g i.val = f i := by simp [g, i.isLt]
  calc
    (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := hfull
    _ = ∑ j ∈ Finset.range (i.val + 1 + (n - i.val - 1)), g j := by
      have hnat : n = i.val + 1 + (n - i.val - 1) := by omega
      exact congrArg (fun m => ∑ j ∈ Finset.range m, g j) hnat
    _ = (∑ j ∈ Finset.range (i.val + 1), g j) +
        ∑ j ∈ Finset.range (n - i.val - 1), g (i.val + 1 + j) :=
      Finset.sum_range_add g (i.val + 1) (n - i.val - 1)
    _ = (∑ j : Fin i.val, f (p18Below i j)) + f i +
        ∑ j : Fin (n - i.val - 1), f (p18Above i j) := by
      rw [Finset.sum_range_succ, ← hbelow, ← habove, hi]

private lemma p18_forward_preserve (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k → p18ForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl ik.val
        (fun acc (t : Fin ik.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik (p18Below ik t))
              (x (p18Below ik t))))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hi' : i.val < n - k := by omega
      have hne : i ≠ ik := by
        intro heq
        have : i.val = n - k - 1 := congrArg Fin.val heq
        omega
      change p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' i hi']
      simp [x', hne]

private def p18ForwardRowBound (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |b i - ((∑ j : Fin i.val, L i (p18Below i j) * x (p18Below i j)) +
    L i i * x i)| ≤
    p18Gamma fp.u n *
      ((∑ j : Fin i.val, |L i (p18Below i j) * x (p18Below i j)|) +
        |L i i * x i|)

private lemma p18_forward_rows (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hvalid : P18GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
        p18ForwardRowBound fp n L b (p18ForwardSubSteps fp n L b k hk x) i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl ik.val
        (fun acc (t : Fin ik.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik (p18Below ik t))
              (x (p18Below ik t))))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let out := p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      change p18ForwardRowBound fp n L b out i
      by_cases hiik : i = ik
      · subst i
        have hbelow (j : Fin ik.val) : out (p18Below ik j) = x (p18Below ik j) := by
          have hj : (p18Below ik j).val < n - k := by
            dsimp [p18Below, ik] at *
            omega
          change p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' _ = _
          rw [p18_forward_preserve fp n L b k (Nat.le_of_succ_le hk) x' _ hj]
          have hne : p18Below ik j ≠ ik := by
            intro heq
            have := congrArg Fin.val heq
            dsimp [p18Below] at this
            omega
          simp [x', hne]
        have hself : out ik = fp.fl_div s (L ik ik) := by
          have hj : ik.val < n - k := by dsimp [ik]; omega
          change p18ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' ik = _
          rw [p18_forward_preserve fp n L b k (Nat.le_of_succ_le hk) x' ik hj]
          simp [x']
        have hfold :
            s = Fin.foldl ik.val
              (fun acc j => fp.fl_sub acc
                (fp.fl_mul (L ik (p18Below ik j)) (out (p18Below ik j))))
              (b ik) := by
          simp only [s]
          congr 1
          funext acc j
          rw [hbelow j]
        have hsum :
            (∑ j : Fin ik.val, L ik (p18Below ik j) * out (p18Below ik j)) =
              (∑ j : Fin ik.val, L ik (p18Below ik j) * out (p18Below ik j)) := rfl
        have hf := p18_fold_error fp n hvalid ik.val (by omega)
          (fun j => L ik (p18Below ik j)) (fun j => out (p18Below ik j)) (b ik)
        have hT : 0 ≤ (∑ j : Fin ik.val,
            |L ik (p18Below ik j) * out (p18Below ik j)|) :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have hdiv := p18_div_finish fp n ik.val hvalid (by omega)
          (b ik)
          (Fin.foldl ik.val
            (fun acc j => fp.fl_sub acc
              (fp.fl_mul (L ik (p18Below ik j)) (out (p18Below ik j))))
            (b ik))
          (∑ j : Fin ik.val, L ik (p18Below ik j) * out (p18Below ik j))
          (∑ j : Fin ik.val, |L ik (p18Below ik j) * out (p18Below ik j)|)
          (L ik ik) (hdiag ik) hT hf
        have hfactor : ((ik.val + 1 : ℕ) : ℝ) * p18Coeff fp.u n ≤
            p18Gamma fp.u n := by
          have hcn := (p18_coeff_basic fp.u n ik.val fp.u_nonneg hvalid
            (by omega : ik.val + 1 ≤ n)).1
          have hle : ((ik.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (by omega : ik.val + 1 ≤ n)
          have hmul := mul_le_mul_of_nonneg_right hle hcn
          simpa [p18Gamma, p18Coeff, mul_div_assoc] using hmul
        unfold p18ForwardRowBound
        rw [hself]
        rw [hfold]
        dsimp at hdiv
        exact hdiv.trans (mul_le_mul_of_nonneg_right hfactor
          (add_nonneg hT (abs_nonneg _)))
      · have hi' : n - k ≤ i.val := by
          have hik : ik.val = n - (k + 1) := by dsimp [ik]; omega
          have hneq : i.val ≠ ik.val := by
            intro heq
            exact hiik (Fin.ext heq)
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hi'

private lemma p18_sign_mul (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    ring
  · subst x
    simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    ring

private lemma p18_abs_sign_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

private lemma p18_row_correction {n : ℕ} (a x : Fin n → ℝ)
    (b γ : ℝ) (hγ : 0 ≤ γ)
    (hres : |b - ∑ j : Fin n, a j * x j| ≤
      γ * ∑ j : Fin n, |a j * x j|) :
    ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ γ * |a j|) ∧
      (∑ j : Fin n, (a j + e j) * x j) = b := by
  let S := ∑ j : Fin n, |a j * x j|
  let r := b - ∑ j : Fin n, a j * x j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hS0 : S = 0
  · have hr : r = 0 := by
      have hrabs : |r| ≤ 0 := by simpa only [S, r, hS0, mul_zero] using hres
      exact abs_eq_zero.mp (le_antisymm hrabs (abs_nonneg _))
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro j
      simpa using mul_nonneg hγ (abs_nonneg (a j))
    · simp only [add_zero]
      dsimp [r] at hr
      linarith
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    let e : Fin n → ℝ := fun j => (r / S) * |a j| * Real.sign (x j)
    refine ⟨e, ?_, ?_⟩
    · intro j
      have hratio : |r / S| ≤ γ := by
        rw [abs_div, abs_of_pos hSpos]
        apply (div_le_iff₀ hSpos).2
        simpa only [r, S] using hres
      have hsign := p18_abs_sign_le (x j)
      dsimp [e]
      rw [abs_mul, abs_mul, abs_abs]
      have hmid : |r / S| * |a j| * |Real.sign (x j)| ≤
          |r / S| * |a j| := by
        nlinarith [mul_nonneg (abs_nonneg (r / S)) (abs_nonneg (a j))]
      exact hmid.trans (mul_le_mul_of_nonneg_right hratio (abs_nonneg (a j)))
    · have he : (∑ j : Fin n, e j * x j) = r := by
        calc
          (∑ j : Fin n, e j * x j) =
              (r / S) * ∑ j : Fin n, |a j * x j| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                simp only [e]
                calc
                  r / S * |a j| * Real.sign (x j) * x j =
                      r / S * |a j| * (Real.sign (x j) * x j) := by ring
                  _ = r / S * |a j * x j| := by rw [p18_sign_mul, abs_mul]; ring
          _ = r := by
            change r / S * S = r
            exact div_mul_cancel₀ r hS0
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, he]
      dsimp [r]
      ring

private lemma p18_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P18GammaValid u n) :
    0 ≤ p18Gamma u n := by
  unfold p18Gamma P18GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p18_forward_residual (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    let x := p18ForwardSub fp n L b
    ∀ i, |b i - ∑ j : Fin n, L i j * x j| ≤
      p18Gamma fp.u n * ∑ j : Fin n, |L i j * x j| := by
  intro x i
  have hrow := p18_forward_rows fp n L b hdiag hvalid n (le_refl n)
    (fun _ => 0) i (by simp)
  have hsum : (∑ j : Fin n, L i j * x j) =
      (∑ j : Fin i.val, L i (p18Below i j) * x (p18Below i j)) +
        L i i * x i := by
    have hs := p18_sum_split i (fun j => L i j * x j)
    have hz : (∑ j : Fin (n - i.val - 1),
        L i (p18Above i j) * x (p18Above i j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hlt : i.val < (p18Above i j).val := by
        dsimp [p18Above]
        omega
      rw [hlower i (p18Above i j) hlt]
      ring
    rw [hz] at hs
    simpa only [add_zero] using hs
  have hsumabs : (∑ j : Fin n, |L i j * x j|) =
      (∑ j : Fin i.val, |L i (p18Below i j) * x (p18Below i j)|) +
        |L i i * x i| := by
    have hs := p18_sum_split i (fun j => |L i j * x j|)
    have hz : (∑ j : Fin (n - i.val - 1),
        |L i (p18Above i j) * x (p18Above i j)|) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hlt : i.val < (p18Above i j).val := by
        dsimp [p18Above]
        omega
      rw [hlower i (p18Above i j) hlt]
      simp
    rw [hz] at hs
    simpa only [add_zero] using hs
  change p18ForwardRowBound fp n L b x i at hrow
  unfold p18ForwardRowBound at hrow
  simpa only [hsum, hsumabs] using hrow

private lemma p18_forward_backward_error (fp : P18FPModel) (n : ℕ)
    (L : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    ∃ ΔL : P18Matrix n n,
      (∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|) ∧
      ∀ i, (∑ j : Fin n,
        (L i j + ΔL i j) * p18ForwardSub fp n L b j) = b i := by
  classical
  let x := p18ForwardSub fp n L b
  have hγ := p18_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hrow (i : Fin n) := p18_row_correction (L i) x (b i)
    (p18Gamma fp.u n) hγ
    (p18_forward_residual fp n L b hdiag hlower hvalid i)
  choose e he using hrow
  refine ⟨fun i j => e i j, ?_, ?_⟩
  · intro i j
    exact (he i).1 j
  · intro i
    exact (he i).2

private lemma p18_back_preserve (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      k ≤ i.val → p18BackSubSteps fp n U b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik (p18Above ik t))
              (x (p18Above ik t))))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hne : i ≠ ik := by
        intro heq
        have := congrArg Fin.val heq
        dsimp [ik] at this
        omega
      change p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega)]
      simp [x', hne]

private def p18BackRowBound (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |b i - ((∑ j : Fin (n - i.val - 1),
      U i (p18Above i j) * x (p18Above i j)) + U i i * x i)| ≤
    p18Gamma fp.u n *
      ((∑ j : Fin (n - i.val - 1),
        |U i (p18Above i j) * x (p18Above i j)|) + |U i i * x i|)

private lemma p18_back_rows (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hvalid : P18GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < k →
        p18BackRowBound fp n U b (p18BackSubSteps fp n U b k hk x) i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik (p18Above ik t))
              (x (p18Above ik t))))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      let out := p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      change p18BackRowBound fp n U b out i
      by_cases hiik : i = ik
      · subst i
        have habove (j : Fin (n - ik.val - 1)) :
            out (p18Above ik j) = x (p18Above ik j) := by
          have hj : k ≤ (p18Above ik j).val := by
            dsimp [p18Above, ik]
            omega
          change p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' _ = _
          rw [p18_back_preserve fp n U b k (Nat.le_of_succ_le hk) x' _ hj]
          have hne : p18Above ik j ≠ ik := by
            intro heq
            have := congrArg Fin.val heq
            dsimp [p18Above, ik] at this
            omega
          simp [x', hne]
        have hself : out ik = fp.fl_div s (U ik ik) := by
          have hj : k ≤ ik.val := by dsimp [ik]; exact le_refl _
          change p18BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' ik = _
          rw [p18_back_preserve fp n U b k (Nat.le_of_succ_le hk) x' ik hj]
          simp [x']
        have hfold :
            s = Fin.foldl (n - ik.val - 1)
              (fun acc j => fp.fl_sub acc
                (fp.fl_mul (U ik (p18Above ik j)) (out (p18Above ik j))))
              (b ik) := by
          simp only [s]
          congr 1
          funext acc j
          rw [habove j]
        have hf := p18_fold_error fp n hvalid (n - ik.val - 1) (by omega)
          (fun j => U ik (p18Above ik j)) (fun j => out (p18Above ik j)) (b ik)
        have hT : 0 ≤ (∑ j : Fin (n - ik.val - 1),
            |U ik (p18Above ik j) * out (p18Above ik j)|) :=
          Finset.sum_nonneg (fun _ _ => abs_nonneg _)
        have hdiv := p18_div_finish fp n (n - ik.val - 1) hvalid (by omega)
          (b ik)
          (Fin.foldl (n - ik.val - 1)
            (fun acc j => fp.fl_sub acc
              (fp.fl_mul (U ik (p18Above ik j)) (out (p18Above ik j))))
            (b ik))
          (∑ j : Fin (n - ik.val - 1), U ik (p18Above ik j) * out (p18Above ik j))
          (∑ j : Fin (n - ik.val - 1), |U ik (p18Above ik j) * out (p18Above ik j)|)
          (U ik ik) (hdiag ik) hT hf
        have hfactor : (((n - ik.val - 1) + 1 : ℕ) : ℝ) * p18Coeff fp.u n ≤
            p18Gamma fp.u n := by
          have hcn := (p18_coeff_basic fp.u n (n - ik.val - 1) fp.u_nonneg hvalid
            (by omega : (n - ik.val - 1) + 1 ≤ n)).1
          have hle : (((n - ik.val - 1) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast (by omega : (n - ik.val - 1) + 1 ≤ n)
          have hmul := mul_le_mul_of_nonneg_right hle hcn
          simpa [p18Gamma, p18Coeff, mul_div_assoc] using hmul
        unfold p18BackRowBound
        rw [hself, hfold]
        dsimp at hdiv
        exact hdiv.trans (mul_le_mul_of_nonneg_right hfactor
          (add_nonneg hT (abs_nonneg _)))
      · have hi' : i.val < k := by
          have hneq : i.val ≠ ik.val := by
            intro heq
            exact hiik (Fin.ext heq)
          dsimp [ik] at hneq
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hi'

private lemma p18_back_residual (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    let x := p18BackSub fp n U b
    ∀ i, |b i - ∑ j : Fin n, U i j * x j| ≤
      p18Gamma fp.u n * ∑ j : Fin n, |U i j * x j| := by
  intro x i
  have hrow := p18_back_rows fp n U b hdiag hvalid n (le_refl n)
    (fun _ => 0) i i.isLt
  have hsum : (∑ j : Fin n, U i j * x j) =
      (∑ j : Fin (n - i.val - 1), U i (p18Above i j) * x (p18Above i j)) +
        U i i * x i := by
    have hs := p18_sum_split i (fun j => U i j * x j)
    have hz : (∑ j : Fin i.val, U i (p18Below i j) * x (p18Below i j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hlt : (p18Below i j).val < i.val := j.isLt
      rw [hupper i (p18Below i j) hlt]
      ring
    rw [hz] at hs
    simpa [add_assoc, add_comm, add_left_comm] using hs
  have hsumabs : (∑ j : Fin n, |U i j * x j|) =
      (∑ j : Fin (n - i.val - 1), |U i (p18Above i j) * x (p18Above i j)|) +
        |U i i * x i| := by
    have hs := p18_sum_split i (fun j => |U i j * x j|)
    have hz : (∑ j : Fin i.val, |U i (p18Below i j) * x (p18Below i j)|) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hlt : (p18Below i j).val < i.val := j.isLt
      rw [hupper i (p18Below i j) hlt]
      simp
    rw [hz] at hs
    simpa [add_assoc, add_comm, add_left_comm] using hs
  change p18BackRowBound fp n U b x i at hrow
  unfold p18BackRowBound at hrow
  simpa only [hsum, hsumabs] using hrow

private lemma p18_back_backward_error (fp : P18FPModel) (n : ℕ)
    (U : P18Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P18GammaValid fp.u n) :
    ∃ ΔU : P18Matrix n n,
      (∀ i j, |ΔU i j| ≤ p18Gamma fp.u n * |U i j|) ∧
      ∀ i, (∑ j : Fin n,
        (U i j + ΔU i j) * p18BackSub fp n U b j) = b i := by
  classical
  let x := p18BackSub fp n U b
  have hγ := p18_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hrow (i : Fin n) := p18_row_correction (U i) x (b i)
    (p18Gamma fp.u n) hγ
    (p18_back_residual fp n U b hdiag hupper hvalid i)
  choose e he using hrow
  refine ⟨fun i j => e i j, ?_, ?_⟩
  · intro i j
    exact (he i).1 j
  · intro i
    exact (he i).2

private lemma p18_matmul_vec {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p)
    (x : Fin p → ℝ) (i : Fin m) :
    (∑ j : Fin p, p18MatMul A B i j * x j) =
      ∑ k : Fin n, A i k * (∑ j : Fin p, B k j * x j) := by
  unfold p18MatMul
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p18_norm_nonneg {m n : ℕ} (A : P18Matrix m n) :
    0 ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  exact Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))

private lemma p18_norm_entry {m n : ℕ} (A : P18Matrix m n)
    (i : Fin m) (j : Fin n) :
    |A i j| ≤ p18EntryNorm A := by
  unfold p18EntryNorm
  have hinner : |A i j| ≤ ∑ j' : Fin n, |A i j'| :=
    Finset.single_le_sum (f := fun j' : Fin n => |A i j'|) (s := Finset.univ)
      (fun j' hj' => abs_nonneg _) (Finset.mem_univ j)
  have houter : (∑ j' : Fin n, |A i j'|) ≤
      ∑ i' : Fin m, ∑ j' : Fin n, |A i' j'| :=
    Finset.single_le_sum
      (f := fun i' : Fin m => ∑ j' : Fin n, |A i' j'|) (s := Finset.univ)
      (fun i' hi' => Finset.sum_nonneg (fun j' hj' => abs_nonneg _))
      (Finset.mem_univ i)
  exact hinner.trans houter

private lemma p18_norm_add {m n : ℕ} (A B : P18Matrix m n) :
    p18EntryNorm (A + B) ≤ p18EntryNorm A + p18EntryNorm B := by
  unfold p18EntryNorm
  simp only [Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  exact abs_add_le _ _

private lemma p18_norm_le_of_pointwise {m n : ℕ}
    (A B : P18Matrix m n) (c : ℝ) (_hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) :
    p18EntryNorm A ≤ c * p18EntryNorm B := by
  unfold p18EntryNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact h i j

private lemma p18_norm_mul {m n p : ℕ}
    (A : P18Matrix m n) (B : P18Matrix n p) :
    p18EntryNorm (p18MatMul A B) ≤
      p18EntryNorm A * p18EntryNorm B := by
  let N := p18EntryNorm B
  have hN : 0 ≤ N := p18_norm_nonneg B
  have hrow (k : Fin n) :
      (∑ j : Fin p, |B k j|) ≤ N := by
    unfold N p18EntryNorm
    exact Finset.single_le_sum
      (f := fun i : Fin n => ∑ j : Fin p, |B i j|) (s := Finset.univ)
      (fun i hi => Finset.sum_nonneg (fun j hj => abs_nonneg _))
      (Finset.mem_univ k)
  have hterm (i : Fin m) (k : Fin n) :
      (∑ j : Fin p, |A i k * B k j|) ≤ |A i k| * N := by
    simp_rw [abs_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow k) (abs_nonneg _)
  unfold p18EntryNorm p18MatMul at *
  calc
    (∑ i : Fin m, ∑ j : Fin p, |∑ k : Fin n, A i k * B k j|) ≤
        ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |A i k * B k j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m, ∑ k : Fin n, ∑ j : Fin p, |A i k * B k j| := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ ≤ ∑ i : Fin m, ∑ k : Fin n, |A i k| * N := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i k
    _ = (∑ i : Fin m, ∑ k : Fin n, |A i k|) * N := by
      simp_rw [Finset.sum_mul]

private lemma p18_matmul_add_left {m n p : ℕ}
    (A B : P18Matrix m n) (C : P18Matrix n p) :
    p18MatMul (A + B) C = p18MatMul A C + p18MatMul B C := by
  ext i j
  simp [p18MatMul, add_mul, Finset.sum_add_distrib]

private lemma p18_matmul_add_right {m n p : ℕ}
    (A : P18Matrix m n) (B C : P18Matrix n p) :
    p18MatMul A (B + C) = p18MatMul A B + p18MatMul A C := by
  ext i j
  simp [p18MatMul, mul_add, Finset.sum_add_distrib]

private lemma p18_combined_decomp {n : ℕ}
    (L D ΔL ΔD ΔU : P18Matrix n n) :
    p18CombinedBackwardError L D ΔL ΔD ΔU =
      p18MatMul (p18MatMul ΔL (D + ΔD)) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L ΔD) (p18Transpose L + ΔU) +
      p18MatMul (p18MatMul L D) ΔU := by
  unfold p18CombinedBackwardError p18PerturbedLDLT p18LDLT
  ext i j
  simp only [p18_matmul_add_left, p18_matmul_add_right,
    Matrix.add_apply, Matrix.sub_apply]
  ring

private lemma p18_combined_norm_bound (fp : P18FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P18Matrix n n)
    (hvalid : P18GammaValid fp.u n) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ p18Gamma fp.u n * |L i j|)
    (hD : p18EntryNorm ΔD ≤ eta * p18EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p18Gamma fp.u n * |p18Transpose L i j|) :
    p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p18SolveBackwardFactor fp n eta L D := by
  let U := p18Transpose L
  let γ := p18Gamma fp.u n
  let l := p18EntryNorm L
  let d := p18EntryNorm D
  let u := p18EntryNorm U
  let B := γ * (1 + eta) * (1 + γ) + eta * (1 + γ) + γ
  have hγ : 0 ≤ γ := p18_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hl : 0 ≤ l := p18_norm_nonneg L
  have hd : 0 ≤ d := p18_norm_nonneg D
  have hu : 0 ≤ u := p18_norm_nonneg U
  have hDnorm : p18EntryNorm ΔD ≤ eta * d := hD
  have hLnorm : p18EntryNorm ΔL ≤ γ * l :=
    p18_norm_le_of_pointwise ΔL L γ hγ hL
  have hUnorm : p18EntryNorm ΔU ≤ γ * u :=
    p18_norm_le_of_pointwise ΔU U γ hγ hU
  have hDplus : p18EntryNorm (D + ΔD) ≤ (1 + eta) * d := by
    calc
      p18EntryNorm (D + ΔD) ≤ d + p18EntryNorm ΔD := p18_norm_add D ΔD
      _ ≤ d + eta * d := add_le_add_right hDnorm d
      _ = (1 + eta) * d := by ring
  have hUplus : p18EntryNorm (U + ΔU) ≤ (1 + γ) * u := by
    calc
      p18EntryNorm (U + ΔU) ≤ u + p18EntryNorm ΔU := p18_norm_add U ΔU
      _ ≤ u + γ * u := add_le_add_right hUnorm u
      _ = (1 + γ) * u := by ring
  have hηplus : 0 ≤ 1 + eta := by linarith
  have hγplus : 0 ≤ 1 + γ := by linarith
  let T1 := p18MatMul (p18MatMul ΔL (D + ΔD)) (U + ΔU)
  let T2 := p18MatMul (p18MatMul L ΔD) (U + ΔU)
  let T3 := p18MatMul (p18MatMul L D) ΔU
  have ht1 : p18EntryNorm T1 ≤ (γ * l) * ((1 + eta) * d) * ((1 + γ) * u) := by
    calc
      p18EntryNorm T1 ≤
          p18EntryNorm (p18MatMul ΔL (D + ΔD)) * p18EntryNorm (U + ΔU) :=
        p18_norm_mul _ _
      _ ≤ (p18EntryNorm ΔL * p18EntryNorm (D + ΔD)) *
          p18EntryNorm (U + ΔU) := by
        exact mul_le_mul_of_nonneg_right (p18_norm_mul ΔL (D + ΔD))
          (p18_norm_nonneg (U + ΔU))
      _ ≤ (γ * l) * ((1 + eta) * d) * ((1 + γ) * u) := by
        have hp : p18EntryNorm ΔL * p18EntryNorm (D + ΔD) ≤
            (γ * l) * ((1 + eta) * d) := by
          calc
            _ ≤ (γ * l) * p18EntryNorm (D + ΔD) :=
              mul_le_mul_of_nonneg_right hLnorm (p18_norm_nonneg _)
            _ ≤ (γ * l) * ((1 + eta) * d) :=
              mul_le_mul_of_nonneg_left hDplus (mul_nonneg hγ hl)
        calc
          _ ≤ ((γ * l) * ((1 + eta) * d)) * p18EntryNorm (U + ΔU) :=
            mul_le_mul_of_nonneg_right hp (p18_norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hUplus
            (mul_nonneg (mul_nonneg hγ hl) (mul_nonneg hηplus hd))
  have ht2 : p18EntryNorm T2 ≤ l * (eta * d) * ((1 + γ) * u) := by
    calc
      p18EntryNorm T2 ≤
          p18EntryNorm (p18MatMul L ΔD) * p18EntryNorm (U + ΔU) :=
        p18_norm_mul _ _
      _ ≤ (l * p18EntryNorm ΔD) * p18EntryNorm (U + ΔU) := by
        exact mul_le_mul_of_nonneg_right (p18_norm_mul L ΔD)
          (p18_norm_nonneg (U + ΔU))
      _ ≤ l * (eta * d) * ((1 + γ) * u) := by
        have hp : l * p18EntryNorm ΔD ≤ l * (eta * d) :=
          mul_le_mul_of_nonneg_left hDnorm hl
        calc
          _ ≤ (l * (eta * d)) * p18EntryNorm (U + ΔU) :=
            mul_le_mul_of_nonneg_right hp (p18_norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hUplus
            (mul_nonneg hl (mul_nonneg heta hd))
  have ht3 : p18EntryNorm T3 ≤ (l * d) * (γ * u) := by
    calc
      p18EntryNorm T3 ≤ p18EntryNorm (p18MatMul L D) * p18EntryNorm ΔU :=
        p18_norm_mul _ _
      _ ≤ (l * d) * p18EntryNorm ΔU := by
        exact mul_le_mul_of_nonneg_right (p18_norm_mul L D)
          (p18_norm_nonneg ΔU)
      _ ≤ (l * d) * (γ * u) := by
        exact mul_le_mul_of_nonneg_left hUnorm (mul_nonneg hl hd)
  have hsum : p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
      l * d * u * B := by
    rw [p18_combined_decomp]
    calc
      p18EntryNorm (T1 + T2 + T3) ≤
          p18EntryNorm T1 + p18EntryNorm T2 + p18EntryNorm T3 := by
        exact (p18_norm_add (T1 + T2) T3).trans
          (add_le_add_left (p18_norm_add T1 T2) (p18EntryNorm T3))
      _ ≤ (γ * l) * ((1 + eta) * d) * ((1 + γ) * u) +
          l * (eta * d) * ((1 + γ) * u) + (l * d) * (γ * u) := by
        linarith
      _ = l * d * u * B := by dsimp [B]; ring
  have hB : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ 1 + eta := by linarith
    have h2 : 0 ≤ 1 + γ := by linarith
    positivity
  have hP : 0 ≤ l * d * u * B := by positivity
  have hscale : l * d * u * B ≤ (n : ℝ) ^ 6 * (l * d * u * B) := by
    cases n with
    | zero =>
        have hl0 : l = 0 := by simp [l, p18EntryNorm]
        simp [hl0]
    | succ n =>
        have hn : (1 : ℝ) ≤ (↑(n + 1) : ℝ) := by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
        have hp : (1 : ℝ) ≤ (↑(n + 1) : ℝ) ^ 6 := one_le_pow₀ hn
        nlinarith
  unfold p18SolveBackwardFactor
  change p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) ≤
    (n : ℝ) ^ 6 * l * d * u * B
  convert hsum.trans hscale using 1; ring

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
    p18_forward_backward_error fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have hUdiag : ∀ i, U i i ≠ 0 := by
    intro i
    exact hdiag i
  have hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p18_back_backward_error fp n U z hUdiag hUupper hvalid
  let F := p18TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · intro i
    have hpert : (∑ j : Fin n,
        p18PerturbedLDLT L D ΔL ΔD ΔU i j * x j) = b i := by
      calc
        (∑ j : Fin n, p18PerturbedLDLT L D ΔL ΔD ΔU i j * x j) =
            ∑ k : Fin n, p18MatMul (L + ΔL) (D + ΔD) i k *
              (∑ j : Fin n, (U + ΔU) k j * x j) := by
                exact p18_matmul_vec (p18MatMul (L + ΔL) (D + ΔD))
                  (U + ΔU) x i
        _ = ∑ k : Fin n, p18MatMul (L + ΔL) (D + ΔD) i k * z k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : (∑ j : Fin n, (U + ΔU) k j * x j) = z k := by
            simpa only [Matrix.add_apply] using hback k
          rw [hk']
        _ = ∑ k : Fin n, (L + ΔL) i k *
            (∑ j : Fin n, (D + ΔD) k j * z j) :=
          p18_matmul_vec (L + ΔL) (D + ΔD) z i
        _ = ∑ k : Fin n, (L + ΔL) i k * y k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : (∑ j : Fin n, (D + ΔD) k j * z j) = y k := by
            simpa only [Matrix.add_apply] using hblock k
          rw [hk']
        _ = b i := by
          simpa only [Matrix.add_apply] using hforward i
    have hpoint (j : Fin n) :
        A i j + F i j = p18PerturbedLDLT L D ΔL ΔD ΔU i j := by
      have hfij := congrArg (fun M : P18Matrix n n => M i j) hfactor
      simp only [Matrix.add_apply] at hfij
      dsimp [F, p18TotalBackwardError, p18CombinedBackwardError]
      linarith
    change (∑ j : Fin n, (A i j + F i j) * x j) = b i
    simpa only [hpoint] using hpert
  · have hcombined := p18_combined_norm_bound fp n eta L D ΔL ΔD ΔU
      hvalid heta hΔL hΔD hΔU
    calc
      p18EntryNorm F ≤
          p18EntryNorm E0 + p18EntryNorm (p18CombinedBackwardError L D ΔL ΔD ΔU) :=
        p18_norm_add E0 _
      _ ≤ factorEta * p18EntryNorm A + p18SolveBackwardFactor fp n eta L D :=
        add_le_add hE0 hcombined
      _ = p18TotalBackwardBound fp n eta factorEta A L D := rfl

end VSCLReuse

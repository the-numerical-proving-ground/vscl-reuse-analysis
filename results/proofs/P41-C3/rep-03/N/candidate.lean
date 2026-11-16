import VSCLReuse.P41.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p41_gamma_step_real
    (x u : ℝ) (hu : 0 ≤ u) (hx : 0 ≤ x) (h : x + u < 1) :
    (x / (1 - x) + u) / (1 - u) ≤ (x + u) / (1 - x - u) := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 < 1 - u := by linarith
  have h3 : 0 < 1 - x - u := by linarith
  have heq : (x / (1 - x) + u) / (1 - u) =
      (x + u - u * x) / ((1 - x) * (1 - u)) := by
    field_simp
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos h1 h2) h3).2
  nlinarith [mul_nonneg hx hu]

private theorem p41_gamma_step_real₂
    (x u : ℝ) (hu : 0 ≤ u) (hx : 0 ≤ x) (h : x + u < 1) :
    x / (1 - x) * (1 + u) + u ≤ (x + u) / (1 - x - u) := by
  have h1 : 0 < 1 - x := by linarith
  have h3 : 0 < 1 - x - u := by linarith
  have heq : x / (1 - x) * (1 + u) + u = (x + u) / (1 - x) := by
    field_simp
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ h1 h3).2
  nlinarith [mul_nonneg hu (add_nonneg hx hu)]

private theorem p41_gamma_step_inv (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (h : ((m + 1 : ℕ) : ℝ) * u < 1)
    (e d : ℝ) (he : |e| ≤ p41Gamma u m) (hd : |d| ≤ u) :
    |(1 + e) / (1 + d) - 1| ≤ p41Gamma u (m + 1) := by
  let x : ℝ := (m : ℝ) * u
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hxu : x + u < 1 := by dsimp [x] at *; push_cast at h; nlinarith
  have hden : 0 < 1 + d := by have := (abs_le.mp hd).1; linarith
  have hden' : 0 < 1 - u := by linarith
  have hg : 0 ≤ p41Gamma u m := by
    unfold p41Gamma
    exact div_nonneg hx (by dsimp [x] at hxu ⊢; linarith)
  have hab : |e - d| ≤ p41Gamma u m + u := by
    calc
      |e - d| ≤ |e| + |d| := by
        simpa using (abs_add_le e (-d))
      _ ≤ p41Gamma u m + u := add_le_add he hd
  have hfrac : |e - d| / (1 + d) ≤ (p41Gamma u m + u) / (1 - u) := by
    apply (div_le_div_iff₀ hden hden').2
    calc
      |e - d| * (1 - u) ≤ (p41Gamma u m + u) * (1 - u) :=
        mul_le_mul_of_nonneg_right hab (le_of_lt hden')
      _ ≤ (p41Gamma u m + u) * (1 + d) :=
        mul_le_mul_of_nonneg_left (by have := (abs_le.mp hd).1; linarith) (add_nonneg hg hu)
  have heq : (1 + e) / (1 + d) - 1 = (e - d) / (1 + d) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hden]
  exact hfrac.trans (by
    convert p41_gamma_step_real x u hu hx hxu using 1 <;>
      simp only [p41Gamma, x, Nat.cast_add, Nat.cast_one, add_mul, one_mul] <;> ring)

private theorem p41_gamma_step_mul (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (h : ((m + 1 : ℕ) : ℝ) * u < 1)
    (e d : ℝ) (he : |e| ≤ p41Gamma u m) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ p41Gamma u (m + 1) := by
  let x : ℝ := (m : ℝ) * u
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hxu : x + u < 1 := by dsimp [x] at *; push_cast at h; nlinarith
  have hfac : |1 + d| ≤ 1 + u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le 1 d
      _ ≤ 1 + u := by simpa using add_le_add_left hd 1
  have hg : 0 ≤ p41Gamma u m := by
    unfold p41Gamma
    exact div_nonneg hx (by dsimp [x] at hxu ⊢; linarith)
  have hbound : |e * (1 + d) + d| ≤ p41Gamma u m * (1 + u) + u := by
    calc
      |e * (1 + d) + d| ≤ |e * (1 + d)| + |d| := abs_add_le _ _
      _ = |e| * |1 + d| + |d| := by rw [abs_mul]
      _ ≤ p41Gamma u m * (1 + u) + u := by
        exact add_le_add (mul_le_mul he hfac (abs_nonneg _) hg) hd
  have heq : (1 + e) * (1 + d) - 1 = e * (1 + d) + d := by ring
  rw [heq]
  exact hbound.trans (by
    convert p41_gamma_step_real₂ x u hu hx hxu using 1 <;>
      simp only [p41Gamma, x, Nat.cast_add, Nat.cast_one, add_mul, one_mul] <;> ring)

private theorem p41_gamma_le_succ (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (h : ((m + 1 : ℕ) : ℝ) * u < 1) :
    p41Gamma u m ≤ p41Gamma u (m + 1) := by
  let x : ℝ := (m : ℝ) * u
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hxu : x + u < 1 := by dsimp [x] at *; push_cast at h; nlinarith
  have hden : 0 < 1 - x := by linarith
  have hg : 0 ≤ p41Gamma u m := by
    unfold p41Gamma
    exact div_nonneg hx (by dsimp [x] at hxu ⊢; linarith)
  have hmid : p41Gamma u m ≤ p41Gamma u m * (1 + u) + u := by
    nlinarith [mul_nonneg hg hu]
  exact hmid.trans (by
    convert p41_gamma_step_real₂ x u hu hx hxu using 1 <;>
      simp only [p41Gamma, x, Nat.cast_add, Nat.cast_one, add_mul, one_mul] <;> ring)

private theorem p41_gamma_u_le (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (h : ((m + 1 : ℕ) : ℝ) * u < 1) :
    u ≤ p41Gamma u (m + 1) := by
  let x : ℝ := (m : ℝ) * u
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hu
  have hxu : x + u < 1 := by dsimp [x] at *; push_cast at h; nlinarith
  have hden : 0 < 1 - x - u := by linarith
  have hh : u ≤ (x + u) / (1 - x - u) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hu (add_nonneg hx hu)]
  convert hh using 1 <;>
    simp only [p41Gamma, x, Nat.cast_add, Nat.cast_one, add_mul, one_mul] <;> ring

private noncomputable def p41SubFold (fp : P41FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (b : ℝ) : ℝ :=
  Fin.foldl m (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) b

private theorem p41_subfold_perturbed (fp : P41FPModel) :
    ∀ (m : ℕ) (a x : Fin m → ℝ) (b : ℝ),
      P41GammaValid fp.u m →
      ∃ e0 : ℝ, ∃ e : Fin m → ℝ,
        |e0| ≤ p41Gamma fp.u m ∧
        (∀ j, |e j| ≤ p41Gamma fp.u m) ∧
        b = p41SubFold fp m a x b * (1 + e0) +
          ∑ j : Fin m, (a j * x j) * (1 + e j) := by
  intro m
  induction m with
  | zero =>
      intro a x b hv
      refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
      · simp [p41Gamma]
      · intro j; exact j.elim0
      · simp [p41SubFold]
  | succ m ih =>
      intro a x b hv
      let a' : Fin m → ℝ := fun j => a j.castSucc
      let x' : Fin m → ℝ := fun j => x j.castSucc
      have hv' : P41GammaValid fp.u m := by
        unfold P41GammaValid at *
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        have hu := fp.u_nonneg
        push_cast at hv
        nlinarith
      obtain ⟨e0, e, he0, he, hrep⟩ := ih a' x' b hv'
      let s := p41SubFold fp m a' x' b
      let t := a (Fin.last m) * x (Fin.last m)
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (a (Fin.last m)) (x (Fin.last m))
      obtain ⟨ds, hds, hsub⟩ := fp.model_sub s (fp.fl_mul (a (Fin.last m)) (x (Fin.last m)))
      have hden : 1 + ds ≠ 0 := by
        have hsmall : fp.u < 1 := by
          unfold P41GammaValid at hv
          have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
          push_cast at hv
          nlinarith [fp.u_nonneg]
        have := (abs_le.mp hds).1
        linarith
      let enew : ℝ := (1 + e0) / (1 + ds) - 1
      let elast : ℝ := (1 + e0) * (1 + dm) - 1
      refine ⟨enew, Fin.snoc e elast, ?_, ?_, ?_⟩
      · exact p41_gamma_step_inv fp.u m fp.u_nonneg hv e0 ds he0 hds
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa [elast] using
            p41_gamma_step_mul fp.u m fp.u_nonneg hv e0 dm he0 hdm
        · simpa using (he j).trans (p41_gamma_le_succ fp.u m fp.u_nonneg hv)
      · have hfold : p41SubFold fp (m + 1) a x b =
            (s - t * (1 + dm)) * (1 + ds) := by
          simp only [p41SubFold, Fin.foldl_succ_last]
          simpa [s, a', x', t, p41SubFold, hmul] using hsub
        have hcancel :
            ((s - t * (1 + dm)) * (1 + ds)) * (1 + enew) +
              t * (1 + elast) = s * (1 + e0) := by
          dsimp [enew, elast]
          field_simp
          ring
        rw [hfold, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        calc
          b = s * (1 + e0) + ∑ j : Fin m,
              (a j.castSucc * x j.castSucc) * (1 + e j) := hrep
          _ = (s - t * (1 + dm)) * (1 + ds) * (1 + enew) +
              ((∑ j : Fin m, (a j.castSucc * x j.castSucc) * (1 + e j)) +
              t * (1 + elast)) := by rw [← hcancel]; ring

private theorem p41_row_solve_perturbed (fp : P41FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (b d y : ℝ)
    (hv : P41GammaValid fp.u (m + 1)) (hd : d ≠ 0)
    (hy : y = fp.fl_div (p41SubFold fp m a x b) d) :
    ∃ ed : ℝ, ∃ e : Fin m → ℝ,
      |ed| ≤ p41Gamma fp.u (m + 1) ∧
      (∀ j, |e j| ≤ p41Gamma fp.u (m + 1)) ∧
      b = d * y * (1 + ed) +
        ∑ j : Fin m, (a j * x j) * (1 + e j) := by
  have hv' : P41GammaValid fp.u m := by
    unfold P41GammaValid at *
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    push_cast at hv
    nlinarith [fp.u_nonneg]
  obtain ⟨e0, e, he0, he, hrep⟩ :=
    p41_subfold_perturbed fp m a x b hv'
  let s := p41SubFold fp m a x b
  obtain ⟨dd, hdd, hdiv⟩ := fp.model_div s d hd
  have hden : 1 + dd ≠ 0 := by
    have hsmall : fp.u < 1 := by
      unfold P41GammaValid at hv
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      push_cast at hv
      nlinarith [fp.u_nonneg]
    have := (abs_le.mp hdd).1
    linarith
  let ed : ℝ := (1 + e0) / (1 + dd) - 1
  refine ⟨ed, e, ?_, ?_, ?_⟩
  · exact p41_gamma_step_inv fp.u m fp.u_nonneg hv e0 dd he0 hdd
  · intro j
    exact (he j).trans (p41_gamma_le_succ fp.u m fp.u_nonneg hv)
  · have hs : s = d * y / (1 + dd) := by
      rw [hy, hdiv]
      field_simp
    calc
      b = s * (1 + e0) + ∑ j : Fin m,
          (a j * x j) * (1 + e j) := hrep
      _ = d * y * (1 + ed) + ∑ j : Fin m,
          (a j * x j) * (1 + e j) := by
        rw [hs]
        dsimp [ed]
        field_simp
        ring

private theorem p41_gamma_mono (u : ℝ) (m n : ℕ)
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : P41GammaValid u n) :
    p41Gamma u m ≤ p41Gamma u n := by
  let x : ℝ := (m : ℝ) * u
  let y : ℝ := (n : ℝ) * u
  have hxy : x ≤ y := mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu
  have hy : y < 1 := hv
  have hx : x < 1 := lt_of_le_of_lt hxy hy
  have hdenx : 0 < 1 - x := by linarith
  have hdeny : 0 < 1 - y := by linarith
  change x / (1 - x) ≤ y / (1 - y)
  apply (div_le_div_iff₀ hdenx hdeny).2
  nlinarith

private theorem p41_abs_sum_mul_bound {m : ℕ} (c e : Fin m → ℝ) (g : ℝ)
    (he : ∀ j, |e j| ≤ g) :
    |∑ j : Fin m, c j * e j| ≤ g * ∑ j : Fin m, |c j| := by
  calc
    |∑ j : Fin m, c j * e j| ≤ ∑ j : Fin m, |c j * e j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin m, g * |c j| := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (he j) (abs_nonneg (c j))
    _ = g * ∑ j : Fin m, |c j| := by rw [Finset.mul_sum]

private theorem p41_row_solve_bound (fp : P41FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (b d y : ℝ)
    (hv : P41GammaValid fp.u (m + 1)) (hd : d ≠ 0)
    (hy : y = fp.fl_div (p41SubFold fp m a x b) d) :
    |(d * y + ∑ j : Fin m, a j * x j) - b| ≤
      p41Gamma fp.u (m + 1) *
        (|d * y| + ∑ j : Fin m, |a j * x j|) := by
  obtain ⟨ed, e, hed, he, hrep⟩ :=
    p41_row_solve_perturbed fp m a x b d y hv hd hy
  let c : Fin m → ℝ := fun j => a j * x j
  have hsum := p41_abs_sum_mul_bound c e (p41Gamma fp.u (m + 1)) he
  have hformula :
      (d * y + ∑ j : Fin m, a j * x j) - b =
        -(d * y * ed + ∑ j : Fin m, c j * e j) := by
    rw [hrep]
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib]
    dsimp [c]
    ring
  rw [hformula, abs_neg]
  calc
    |d * y * ed + ∑ j : Fin m, c j * e j| ≤
        |d * y * ed| + |∑ j : Fin m, c j * e j| := abs_add_le _ _
    _ ≤ p41Gamma fp.u (m + 1) * |d * y| +
        p41Gamma fp.u (m + 1) * ∑ j : Fin m, |c j| := by
          apply add_le_add
          · rw [abs_mul]
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left hed (abs_nonneg (d * y))
          · exact hsum
    _ = p41Gamma fp.u (m + 1) *
          (|d * y| + ∑ j : Fin m, |a j * x j|) := by
            dsimp [c]
            ring

private def p41PrefixIndex {n : ℕ} (i : Fin n) (t : Fin i.val) : Fin n :=
  ⟨t.val, lt_trans t.isLt i.isLt⟩

private def p41LowerRowBound (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |(L i i * x i + ∑ t : Fin i.val,
        L i (p41PrefixIndex i t) * x (p41PrefixIndex i t)) - b i| ≤
    p41Gamma fp.u n *
      (|L i i * x i| + ∑ t : Fin i.val,
        |L i (p41PrefixIndex i t) * x (p41PrefixIndex i t)|)

private theorem p41_forward_preserves (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k →
      p41ForwardSubSteps fp n L b k hk x i = x i := by
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
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hstep : p41ForwardSubSteps fp n L b (k + 1) hk x =
          p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' := rfl
      rw [hstep]
      have hi' : i.val < n - k := by omega
      rw [ih (Nat.le_of_succ_le hk) x' i hi']
      have hne : i ≠ ik := by
        intro heq
        have : i.val = n - k - 1 := congrArg Fin.val heq
        omega
      simp [x', hne]

private theorem p41_forward_rows (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hv : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
      p41LowerRowBound fp n L b
        (p41ForwardSubSteps fp n L b k hk x) i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      have := i.isLt
      omega
  | succ k ih =>
      intro hk x i hi
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let out := p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hstep : p41ForwardSubSteps fp n L b (k + 1) hk x = out := rfl
      rw [hstep]
      by_cases heq : i = ik
      · subst i
        have hcount : count + 1 ≤ n := by dsimp [count]; omega
        have hvcount : P41GammaValid fp.u (count + 1) := by
          unfold P41GammaValid at *
          have hc : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcount
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hv
        have hself : out ik = fp.fl_div s (L ik ik) := by
          have hpr : out ik = x' ik := by
            exact p41_forward_preserves fp n L b k (Nat.le_of_succ_le hk) x' ik (by dsimp [ik]; omega)
          rw [hpr]
          simp [x']
        have hy : out ik = fp.fl_div
            (p41SubFold fp count
              (fun t : Fin count => L ik (p41PrefixIndex ik t))
              (fun t : Fin count => x (p41PrefixIndex ik t)) (b ik))
            (L ik ik) := by
          simpa [s, p41SubFold, count, ik, p41PrefixIndex] using hself
        have hxs (t : Fin count) :
            x (p41PrefixIndex ik t) = out (p41PrefixIndex ik t) := by
          have hne : p41PrefixIndex ik t ≠ ik := by
            intro hh
            have hh' := congrArg Fin.val hh
            dsimp [p41PrefixIndex, ik] at hh'
            omega
          have hpr : out (p41PrefixIndex ik t) = x' (p41PrefixIndex ik t) := by
            exact p41_forward_preserves fp n L b k (Nat.le_of_succ_le hk) x'
              (p41PrefixIndex ik t) (by dsimp [p41PrefixIndex, count, ik]; omega)
          rw [hpr]
          simp [x', hne]
        have hrow := p41_row_solve_bound fp count
          (fun t : Fin count => L ik (p41PrefixIndex ik t))
          (fun t : Fin count => x (p41PrefixIndex ik t))
          (b ik) (L ik ik) (out ik) hvcount (hdiag ik) hy
        simp_rw [hxs] at hrow
        have hgamma := p41_gamma_mono fp.u (count + 1) n fp.u_nonneg hcount hv
        dsimp [p41LowerRowBound]
        calc
          _ ≤ p41Gamma fp.u (count + 1) *
              (|L ik ik * out ik| + ∑ t : Fin ik.val,
                |L ik (p41PrefixIndex ik t) * out (p41PrefixIndex ik t)|) := by
                  simpa [count, ik] using hrow
          _ ≤ p41Gamma fp.u n *
              (|L ik ik * out ik| + ∑ t : Fin ik.val,
                |L ik (p41PrefixIndex ik t) * out (p41PrefixIndex ik t)|) :=
                  mul_le_mul_of_nonneg_right hgamma (by positivity)
      · have hi' : n - k ≤ i.val := by
          have hge : n - k - 1 ≤ i.val := hi
          have hneval : i.val ≠ n - k - 1 := by
            intro hvv
            apply heq
            exact Fin.ext hvv
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hi'

private def p41SuffixIndex {n : ℕ} (i : Fin n)
    (t : Fin (n - i.val - 1)) : Fin n :=
  ⟨i.val + 1 + t.val, by omega⟩

private def p41UpperRowBound (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |(U i i * x i + ∑ t : Fin (n - i.val - 1),
        U i (p41SuffixIndex i t) * x (p41SuffixIndex i t)) - b i| ≤
    p41Gamma fp.u n *
      (|U i i * x i| + ∑ t : Fin (n - i.val - 1),
        |U i (p41SuffixIndex i t) * x (p41SuffixIndex i t)|)

private theorem p41_back_preserves (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      k ≤ i.val →
      p41BackSubSteps fp n U b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨k, hk⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hstep : p41BackSubSteps fp n U b (k + 1) hk x =
          p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' := rfl
      rw [hstep]
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega)]
      have hne : i ≠ ik := by
        intro heq
        have : i.val = k := congrArg Fin.val heq
        omega
      simp [x', hne]

private theorem p41_back_rows (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hv : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < k →
      p41UpperRowBound fp n U b
        (p41BackSubSteps fp n U b k hk x) i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨k, hk⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      let out := p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      have hstep : p41BackSubSteps fp n U b (k + 1) hk x = out := rfl
      rw [hstep]
      by_cases heq : i = ik
      · subst i
        have hcount : count + 1 ≤ n := by dsimp [count]; omega
        have hvcount : P41GammaValid fp.u (count + 1) := by
          unfold P41GammaValid at *
          have hc : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcount
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc fp.u_nonneg) hv
        have hself : out ik = fp.fl_div s (U ik ik) := by
          have hpr : out ik = x' ik := by
            exact p41_back_preserves fp n U b k (Nat.le_of_succ_le hk) x' ik (by dsimp [ik]; omega)
          rw [hpr]
          simp [x']
        have hy : out ik = fp.fl_div
            (p41SubFold fp count
              (fun t : Fin count => U ik (p41SuffixIndex ik t))
              (fun t : Fin count => x (p41SuffixIndex ik t)) (b ik))
            (U ik ik) := by
          simpa [s, p41SubFold, count, ik, p41SuffixIndex] using hself
        have hxs (t : Fin count) :
            x (p41SuffixIndex ik t) = out (p41SuffixIndex ik t) := by
          have hne : p41SuffixIndex ik t ≠ ik := by
            intro hh
            have hh' := congrArg Fin.val hh
            dsimp [p41SuffixIndex, ik] at hh'
            omega
          have hpr : out (p41SuffixIndex ik t) = x' (p41SuffixIndex ik t) := by
            exact p41_back_preserves fp n U b k (Nat.le_of_succ_le hk) x'
              (p41SuffixIndex ik t) (by dsimp [p41SuffixIndex, ik]; omega)
          rw [hpr]
          simp [x', hne]
        have hrow := p41_row_solve_bound fp count
          (fun t : Fin count => U ik (p41SuffixIndex ik t))
          (fun t : Fin count => x (p41SuffixIndex ik t))
          (b ik) (U ik ik) (out ik) hvcount (hdiag ik) hy
        simp_rw [hxs] at hrow
        have hgamma := p41_gamma_mono fp.u (count + 1) n fp.u_nonneg hcount hv
        dsimp [p41UpperRowBound]
        calc
          _ ≤ p41Gamma fp.u (count + 1) *
              (|U ik ik * out ik| + ∑ t : Fin (n - ik.val - 1),
                |U ik (p41SuffixIndex ik t) * out (p41SuffixIndex ik t)|) := by
                  simpa [count, ik] using hrow
          _ ≤ p41Gamma fp.u n *
              (|U ik ik * out ik| + ∑ t : Fin (n - ik.val - 1),
                |U ik (p41SuffixIndex ik t) * out (p41SuffixIndex ik t)|) :=
                  mul_le_mul_of_nonneg_right hgamma (by positivity)
      · have hi' : i.val < k := by
          have hneval : i.val ≠ k := by
            intro hvv
            apply heq
            exact Fin.ext hvv
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hi'

private noncomputable def p41DotFold (fp : P41FPModel) (m : ℕ)
    (a x : Fin (m + 1) → ℝ) : ℝ :=
  Fin.foldl m
    (fun acc j => fp.fl_add acc (fp.fl_mul (a j.succ) (x j.succ)))
    (fp.fl_mul (a 0) (x 0))

private theorem p41_dotfold_perturbed (fp : P41FPModel) :
    ∀ (m : ℕ) (a x : Fin (m + 1) → ℝ),
      P41GammaValid fp.u (m + 1) →
      ∃ e : Fin (m + 1) → ℝ,
        (∀ j, |e j| ≤ p41Gamma fp.u (m + 1)) ∧
        p41DotFold fp m a x =
          ∑ j : Fin (m + 1), (a j * x j) * (1 + e j) := by
  intro m
  induction m with
  | zero =>
      intro a x hv
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (a 0) (x 0)
      refine ⟨fun _ => dm, ?_, ?_⟩
      · intro j
        exact hdm.trans (p41_gamma_u_le fp.u 0 fp.u_nonneg hv)
      · simpa [p41DotFold] using hmul
  | succ m ih =>
      intro a x hv
      let a' : Fin (m + 1) → ℝ := fun j => a j.castSucc
      let x' : Fin (m + 1) → ℝ := fun j => x j.castSucc
      have hv' : P41GammaValid fp.u (m + 1) := by
        unfold P41GammaValid at *
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        push_cast at hv ⊢
        nlinarith [fp.u_nonneg]
      obtain ⟨e, he, hrep⟩ := ih a' x' hv'
      let r := p41DotFold fp m a' x'
      let t := a (Fin.last (m + 1)) * x (Fin.last (m + 1))
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul
        (a (Fin.last (m + 1))) (x (Fin.last (m + 1)))
      obtain ⟨da, hda, hadd⟩ := fp.model_add r
        (fp.fl_mul (a (Fin.last (m + 1))) (x (Fin.last (m + 1))))
      let enew : Fin (m + 1) → ℝ := fun j => (1 + e j) * (1 + da) - 1
      let elast : ℝ := (1 + dm) * (1 + da) - 1
      refine ⟨Fin.snoc enew elast, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · have hdu : |dm| ≤ p41Gamma fp.u (m + 1) :=
            hdm.trans (p41_gamma_u_le fp.u m fp.u_nonneg hv')
          simpa [elast] using
            p41_gamma_step_mul fp.u (m + 1) fp.u_nonneg hv dm da hdu hda
        · simpa [enew] using
            p41_gamma_step_mul fp.u (m + 1) fp.u_nonneg hv (e j) da (he j) hda
      · have hfold : p41DotFold fp (m + 1) a x =
            (r + t * (1 + dm)) * (1 + da) := by
          simp only [p41DotFold, Fin.foldl_succ_last]
          simpa [r, t, a', x', p41DotFold, hmul] using hadd
        rw [hfold, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have hrep' : r = ∑ j : Fin (m + 1),
            (a j.castSucc * x j.castSucc) * (1 + e j) := hrep
        rw [hrep']
        dsimp [enew, elast, t]
        rw [add_mul, Finset.sum_mul]
        congr 1
        · apply Finset.sum_congr rfl
          intro j hj
          ring
        · ring

private theorem p41_rounded_dot_bound (fp : P41FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hv : P41GammaValid fp.u n) :
    |p41RoundedDotProduct fp n a x - ∑ j : Fin n, a j * x j| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |a j| * |x j| := by
  cases n with
  | zero =>
      simp [p41RoundedDotProduct]
  | succ m =>
      obtain ⟨e, he, hrep⟩ := p41_dotfold_perturbed fp m a x hv
      have hfold : p41RoundedDotProduct fp (m + 1) a x = p41DotFold fp m a x := rfl
      rw [hfold, hrep]
      have heq :
          (∑ j : Fin (m + 1), a j * x j * (1 + e j)) -
            (∑ j : Fin (m + 1), a j * x j) =
              ∑ j : Fin (m + 1), (a j * x j) * e j := by
        simp_rw [mul_add, mul_one, Finset.sum_add_distrib]
        ring
      rw [heq]
      simpa only [abs_mul] using
        (p41_abs_sum_mul_bound (fun j : Fin (m + 1) => a j * x j) e
          (p41Gamma fp.u (m + 1)) he)

private theorem p41_fin_sum_to_range {n : ℕ} (f : Fin n → ℝ) :
    (∑ j : Fin n, f j) =
      ∑ j ∈ Finset.range n, (if h : j < n then f ⟨j, h⟩ else 0) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [j.isLt]

private theorem p41_lower_sum {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      ∑ t : Fin i.val, f (p41PrefixIndex i t) := by
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j, h⟩ else 0
  have hfull : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j :=
    p41_fin_sum_to_range f
  have hpre : (∑ t : Fin i.val, f (p41PrefixIndex i t)) =
      ∑ j ∈ Finset.range i.val, g j := by
    rw [p41_fin_sum_to_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < i.val := Finset.mem_range.mp hj
    have hjn : j < n := lt_trans hjlt i.isLt
    simp [g, hjn, hjlt, p41PrefixIndex]
  have hupper (j : ℕ) : g (i.val + 1 + j) = 0 := by
    by_cases hj : i.val + 1 + j < n
    · simp only [g, dif_pos hj]
      exact hzero ⟨i.val + 1 + j, hj⟩ (by dsimp; omega)
    · simp [g, hj]
  have hn : n = (i.val + 1) + (n - i.val - 1) := by omega
  calc
    (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := hfull
    _ = ∑ j ∈ Finset.range ((i.val + 1) + (n - i.val - 1)), g j :=
      congrArg (fun q : ℕ => ∑ j ∈ Finset.range q, g j) hn
    _ = (∑ j ∈ Finset.range (i.val + 1), g j) +
        ∑ j ∈ Finset.range (n - i.val - 1), g (i.val + 1 + j) :=
          Finset.sum_range_add _ _ _
    _ = ∑ j ∈ Finset.range (i.val + 1), g j := by simp [hupper]
    _ = (∑ j ∈ Finset.range i.val, g j) + g i.val := by
      rw [Finset.sum_range_succ]
    _ = f i + ∑ t : Fin i.val, f (p41PrefixIndex i t) := by
      rw [hpre]
      simp [g, i.isLt, add_comm]

private theorem p41_upper_sum {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      ∑ t : Fin (n - i.val - 1), f (p41SuffixIndex i t) := by
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j, h⟩ else 0
  have hfull : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j :=
    p41_fin_sum_to_range f
  have hsuf : (∑ t : Fin (n - i.val - 1), f (p41SuffixIndex i t)) =
      ∑ j ∈ Finset.range (n - i.val - 1), g (i.val + 1 + j) := by
    rw [p41_fin_sum_to_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < n - i.val - 1 := Finset.mem_range.mp hj
    have hjn : i.val + 1 + j < n := by omega
    simp [g, hjn, hjlt, p41SuffixIndex]
  have hlower (j : ℕ) (hj : j < i.val) : g j = 0 := by
    have hjn : j < n := lt_trans hj i.isLt
    simp only [g, dif_pos hjn]
    exact hzero ⟨j, hjn⟩ (by dsimp; exact hj)
  have hn : n = i.val + (n - i.val) := by omega
  have hcount : n - i.val = (n - i.val - 1) + 1 := by omega
  calc
    (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := hfull
    _ = ∑ j ∈ Finset.range (i.val + (n - i.val)), g j :=
      congrArg (fun q : ℕ => ∑ j ∈ Finset.range q, g j) hn
    _ = (∑ j ∈ Finset.range i.val, g j) +
        ∑ j ∈ Finset.range (n - i.val), g (i.val + j) :=
          Finset.sum_range_add _ _ _
    _ = ∑ j ∈ Finset.range (n - i.val), g (i.val + j) := by
      simp [Finset.sum_eq_zero (fun j hj => hlower j (Finset.mem_range.mp hj))]
    _ = ∑ j ∈ Finset.range ((n - i.val - 1) + 1), g (i.val + j) :=
      congrArg (fun q : ℕ => ∑ j ∈ Finset.range q, g (i.val + j)) hcount
    _ = g i.val + ∑ j ∈ Finset.range (n - i.val - 1), g (i.val + 1 + j) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_comm] using
        (Finset.sum_range_succ' (fun j => g (i.val + j)) (n - i.val - 1))
    _ = f i + ∑ t : Fin (n - i.val - 1), f (p41SuffixIndex i t) := by
      rw [hsuf]
      simp [g, i.isLt]

private theorem p41_forward_full_bound (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hv : P41GammaValid fp.u n) :
    let y := p41ForwardSub fp n L b
    ∀ i, |(∑ j : Fin n, L i j * y j) - b i| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |L i j| * |y j| := by
  intro y i
  have hrow := p41_forward_rows fp n L b hdiag hv n (le_refl n)
    (fun _ => 0) i (by omega)
  have hsum : (∑ j : Fin n, L i j * y j) =
      L i i * y i + ∑ t : Fin i.val,
        L i (p41PrefixIndex i t) * y (p41PrefixIndex i t) := by
    apply p41_lower_sum
    intro j hj
    rw [hupper i j hj]
    ring
  have habs : (∑ j : Fin n, |L i j| * |y j|) =
      |L i i| * |y i| + ∑ t : Fin i.val,
        |L i (p41PrefixIndex i t)| * |y (p41PrefixIndex i t)| := by
    apply p41_lower_sum
    intro j hj
    rw [hupper i j hj]
    simp
  rw [hsum, habs]
  simpa [p41LowerRowBound, p41ForwardSub, abs_mul] using hrow

private theorem p41_back_full_bound (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hlower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hv : P41GammaValid fp.u n) :
    let y := p41BackSub fp n U b
    ∀ i, |(∑ j : Fin n, U i j * y j) - b i| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |U i j| * |y j| := by
  intro y i
  have hrow := p41_back_rows fp n U b hdiag hv n (le_refl n)
    (fun _ => 0) i (by exact i.isLt)
  have hsum : (∑ j : Fin n, U i j * y j) =
      U i i * y i + ∑ t : Fin (n - i.val - 1),
        U i (p41SuffixIndex i t) * y (p41SuffixIndex i t) := by
    apply p41_upper_sum
    intro j hj
    rw [hlower i j hj]
    ring
  have habs : (∑ j : Fin n, |U i j| * |y j|) =
      |U i i| * |y i| + ∑ t : Fin (n - i.val - 1),
        |U i (p41SuffixIndex i t)| * |y (p41SuffixIndex i t)| := by
    apply p41_upper_sum
    intro j hj
    rw [hlower i j hj]
    simp
  rw [hsum, habs]
  simpa [p41UpperRowBound, p41BackSub, abs_mul] using hrow

private noncomputable def p41Sign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private theorem p41_sign_mul (x : ℝ) : p41Sign x * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [p41Sign, hx, abs_of_nonneg hx]
  · have hneg : x < 0 := lt_of_not_ge hx
    simp [p41Sign, hx, abs_of_neg hneg]

private theorem p41_abs_sign (x : ℝ) : |p41Sign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [p41Sign, hx]

private theorem p41_weighted_representation {n : ℕ}
    (M x : Fin n → ℝ) (r : ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hr : |r| ≤ ∑ j : Fin n, M j * |x j|) :
    ∃ d : Fin n → ℝ,
      (∀ j, |d j| ≤ M j) ∧ r = ∑ j : Fin n, d j * x j := by
  let S := ∑ j : Fin n, M j * |x j|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j hj => mul_nonneg (hM j) (abs_nonneg _))
  by_cases hzero : S = 0
  · have hr0 : r = 0 := abs_eq_zero.mp (le_antisymm (by simpa [S, hzero] using hr) (abs_nonneg _))
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro j
      simpa using hM j
    · simp [hr0]
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    let c := r / S
    have hc : |c| ≤ 1 := by
      dsimp [c]
      rw [abs_div, abs_of_pos hSpos]
      apply (div_le_iff₀ hSpos).2
      simpa [S] using hr
    let d : Fin n → ℝ := fun j => c * M j * p41Sign (x j)
    refine ⟨d, ?_, ?_⟩
    · intro j
      dsimp [d]
      rw [abs_mul, abs_mul, abs_of_nonneg (hM j), p41_abs_sign]
      have hh := mul_le_mul_of_nonneg_right hc (hM j)
      nlinarith
    · calc
        r = c * S := by dsimp [c]; field_simp
        _ = ∑ j : Fin n, d j * x j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          dsimp [d]
          rw [← p41_sign_mul (x j)]
          ring

private theorem p41_sum_swap {n : ℕ}
    (a : Fin n → ℝ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ j : Fin n, a j * (∑ k : Fin n, B j k * x k)) =
      ∑ k : Fin n, (∑ j : Fin n, a j * B j k) * x k := by
  calc
    (∑ j : Fin n, a j * (∑ k : Fin n, B j k * x k)) =
        ∑ j : Fin n, ∑ k : Fin n, a j * (B j k * x k) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ j : Fin n, a j * (B j k * x k) :=
      Finset.sum_comm
    _ = ∑ k : Fin n, (∑ j : Fin n, a j * B j k) * x k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private theorem p41_abs_matvec_bound {n : ℕ}
    (a x : Fin n → ℝ) :
    |∑ j : Fin n, a j * x j| ≤
      ∑ j : Fin n, |a j| * |x j| := by
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun j : Fin n => a j * x j))

private theorem p41_lu_residual_bound {n : ℕ}
    (A L U : P41Matrix n n) (b x y : Fin n → ℝ) (g : ℝ)
    (hg : 0 ≤ g)
    (hfact : ∀ i j, |(∑ k : Fin n, L i k * U k j) - A i j| ≤
      g * ∑ k : Fin n, |L i k| * |U k j|)
    (hfwd : ∀ i, |(∑ j : Fin n, L i j * y j) - b i| ≤
      g * ∑ j : Fin n, |L i j| * |y j|)
    (hback : ∀ i, |(∑ j : Fin n, U i j * x j) - y i| ≤
      g * ∑ j : Fin n, |U i j| * |x j|) :
    ∀ i, |(∑ j : Fin n, A i j * x j) - b i| ≤
      (3 * g + g ^ 2) *
        ∑ j : Fin n, (∑ k : Fin n, |L i k| * |U k j|) * |x j| := by
  let T : P41Matrix n n := fun i j => ∑ k : Fin n, L i k * U k j
  let W : P41Matrix n n := fun i j => ∑ k : Fin n, |L i k| * |U k j|
  let v : Fin n → ℝ := fun j => ∑ k : Fin n, U j k * x k
  let Q : Fin n → ℝ := fun j => ∑ k : Fin n, |U j k| * |x k|
  let S : Fin n → ℝ := fun i => ∑ j : Fin n, W i j * |x j|
  have hQ (j : Fin n) : 0 ≤ Q j := by
    dsimp [Q]
    positivity
  have hW (i j : Fin n) : 0 ≤ W i j := by
    dsimp [W]
    positivity
  have hvbound (j : Fin n) : |y j| ≤ (1 + g) * Q j := by
    have hvabs : |v j| ≤ Q j := p41_abs_matvec_bound (U j) x
    have hbj : |v j - y j| ≤ g * Q j := hback j
    calc
      |y j| = |v j + (y j - v j)| := by congr 1; ring
      _ ≤ |v j| + |y j - v j| := abs_add_le _ _
      _ ≤ Q j + g * Q j := by
        rw [abs_sub_comm]
        exact add_le_add hvabs hbj
      _ = (1 + g) * Q j := by ring
  have hswap (i : Fin n) :
      (∑ j : Fin n, |L i j| * Q j) = S i := by
    exact p41_sum_swap (fun j => |L i j|) (fun j k => |U j k|) (fun k => |x k|)
  intro i
  have hS : 0 ≤ S i := by
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (hW i j) (abs_nonneg _))
  have hfactor :
      |∑ j : Fin n, (A i j - T i j) * x j| ≤ g * S i := by
    calc
      _ ≤ ∑ j : Fin n, |A i j - T i j| * |x j| :=
        p41_abs_matvec_bound (fun j => A i j - T i j) x
      _ ≤ ∑ j : Fin n, (g * W i j) * |x j| := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (by simpa [T, W, abs_sub_comm] using hfact i j) (abs_nonneg _)
      _ = g * S i := by
        dsimp [S]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hbackterm :
      |∑ j : Fin n, L i j * (v j - y j)| ≤ g * S i := by
    calc
      _ ≤ ∑ j : Fin n, |L i j| * |v j - y j| :=
        p41_abs_matvec_bound (L i) (fun j => v j - y j)
      _ ≤ ∑ j : Fin n, |L i j| * (g * Q j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hback j) (abs_nonneg _)
      _ = g * S i := by
        calc
          (∑ j : Fin n, |L i j| * (g * Q j)) =
              g * ∑ j : Fin n, |L i j| * Q j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = g * S i := by rw [hswap]
  have hyweighted :
      (∑ j : Fin n, |L i j| * |y j|) ≤ (1 + g) * S i := by
    calc
      _ ≤ ∑ j : Fin n, |L i j| * ((1 + g) * Q j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hvbound j) (abs_nonneg _)
      _ = (1 + g) * S i := by
        calc
          (∑ j : Fin n, |L i j| * ((1 + g) * Q j)) =
              (1 + g) * ∑ j : Fin n, |L i j| * Q j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = (1 + g) * S i := by rw [hswap]
  have hfwdterm :
      |(∑ j : Fin n, L i j * y j) - b i| ≤ g * ((1 + g) * S i) :=
    (hfwd i).trans (mul_le_mul_of_nonneg_left hyweighted hg)
  have hmul : (∑ j : Fin n, T i j * x j) =
      ∑ j : Fin n, L i j * v j := by
    symm
    exact p41_sum_swap (L i) U x
  have hidentity :
      (∑ j : Fin n, A i j * x j) - b i =
        (∑ j : Fin n, (A i j - T i j) * x j) +
        (∑ j : Fin n, L i j * (v j - y j)) +
        ((∑ j : Fin n, L i j * y j) - b i) := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
    linear_combination hmul
  rw [hidentity]
  calc
    |(∑ j : Fin n, (A i j - T i j) * x j) +
        (∑ j : Fin n, L i j * (v j - y j)) +
        ((∑ j : Fin n, L i j * y j) - b i)| ≤
      |∑ j : Fin n, (A i j - T i j) * x j| +
      |∑ j : Fin n, L i j * (v j - y j)| +
      |(∑ j : Fin n, L i j * y j) - b i| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ g * S i + g * S i + g * ((1 + g) * S i) := by
      exact add_le_add (add_le_add hfactor hbackterm) hfwdterm
    _ = (3 * g + g ^ 2) * S i := by ring

private theorem p41_lu_solve_matrix_residual
    (fp : P41FPModel) (n : ℕ)
    (A L U : P41Matrix n n) (b : Fin n → ℝ)
    (hcert : P41LUCertificate fp n A L U)
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hv : P41GammaValid fp.u n) :
    let x := p41LUSolve fp n L U b
    ∃ D : P41Matrix n n,
      (∀ i j, |D i j| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |L i k| * |U k j|) ∧
      (∀ i, (∑ j : Fin n, A i j * x j) - b i =
        -(∑ j : Fin n, D i j * x j)) := by
  intro x
  let y := p41ForwardSub fp n L b
  let g := p41Gamma fp.u n
  let C := 3 * g + g ^ 2
  have hg : 0 ≤ g := by
    dsimp [g, p41Gamma]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
      (le_of_lt (sub_pos.mpr hv))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLdiag : ∀ i : Fin n, L i i ≠ 0 := by
    intro i
    rw [hcert.L_diag i]
    norm_num
  have hfwd : ∀ i, |(∑ j : Fin n, L i j * y j) - b i| ≤
      g * ∑ j : Fin n, |L i j| * |y j| := by
    simpa [y, g] using
      (p41_forward_full_bound fp n L b hLdiag hcert.L_upper_zero hv)
  have hback : ∀ i, |(∑ j : Fin n, U i j * x j) - y i| ≤
      g * ∑ j : Fin n, |U i j| * |x j| := by
    simpa [x, y, g, p41LUSolve] using
      (p41_back_full_bound fp n U y hUdiag hcert.U_lower_zero hv)
  have hres := p41_lu_residual_bound A L U b x y g hg
    hcert.backward_bound hfwd hback
  have hrow (i : Fin n) :
      ∃ d : Fin n → ℝ,
        (∀ j, |d j| ≤ C * ∑ k : Fin n, |L i k| * |U k j|) ∧
        b i - (∑ j : Fin n, A i j * x j) =
          ∑ j : Fin n, d j * x j := by
    apply p41_weighted_representation
      (fun j => C * ∑ k : Fin n, |L i k| * |U k j|) x
      (b i - (∑ j : Fin n, A i j * x j))
    · intro j
      exact mul_nonneg hC (by positivity)
    · rw [abs_sub_comm]
      calc
        |(∑ j : Fin n, A i j * x j) - b i| ≤
            C * ∑ j : Fin n,
              (∑ k : Fin n, |L i k| * |U k j|) * |x j| := hres i
        _ = ∑ j : Fin n,
              (C * ∑ k : Fin n, |L i k| * |U k j|) * |x j| := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
  choose d hd hre using hrow
  refine ⟨fun i j => d i j, ?_, ?_⟩
  · intro i j
    exact hd i j
  · intro i
    have hi := hre i
    dsimp at hi ⊢
    linarith

/-- The G-stage block residual at a node whose child systems are GE leaves. -/
theorem p41_c3_G_stage_leaf_residual
    (fp : P41FPModel) (n : ℕ)
    (Ase Anw Ane Ls Us Ln Un : P41Matrix n n)
    (uvec : Fin n → ℝ)
    (hLs : P41LUCertificate fp n Ase Ls Us)
    (hLn : P41LUCertificate fp n Anw Ln Un)
    (hUsdiag : ∀ i : Fin n, Us i i ≠ 0)
    (hUndiag : ∀ i : Fin n, Un i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    let gs := p41LUSolve fp n Ls Us uvec
    let w := p41RoundedMatVec fp n Ane gs
    let gn := p41LUSolve fp n Ln Un w
    ∃ Ds Dn : P41Matrix n n, ∃ dw : Fin n → ℝ,
      (∀ i j, |Ds i j| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ls i k| * |Us k j|) ∧
      (∀ i j, |Dn i j| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n, |Ln i k| * |Un k j|) ∧
      (∀ i, |dw i| ≤ p41Gamma fp.u n *
        ∑ j : Fin n, |Ane i j| * |gs j|) ∧
      (∀ i,
        (∑ j : Fin n, Ase i j * gs j) - uvec i =
          -(∑ j : Fin n, Ds i j * gs j) ∧
        (∑ j : Fin n, Anw i j * gn j) -
          (∑ j : Fin n, Ane i j * gs j) =
            dw i - (∑ j : Fin n, Dn i j * gn j)) := by
  -- PROOF_START P41-C3-H001
  let gs := p41LUSolve fp n Ls Us uvec
  let w := p41RoundedMatVec fp n Ane gs
  let gn := p41LUSolve fp n Ln Un w
  obtain ⟨Ds, hDsBound, hDsEq⟩ :=
    p41_lu_solve_matrix_residual fp n Ase Ls Us uvec hLs hUsdiag hvalid
  obtain ⟨Dn, hDnBound, hDnEq⟩ :=
    p41_lu_solve_matrix_residual fp n Anw Ln Un w hLn hUndiag hvalid
  let dw : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Ane i j * gs j
  refine ⟨Ds, Dn, dw, ?_, ?_, ?_, ?_⟩
  · exact hDsBound
  · exact hDnBound
  · intro i
    exact p41_rounded_dot_bound fp n (Ane i) gs hvalid
  · intro i
    constructor
    · exact hDsEq i
    · dsimp [dw]
      linarith [hDnEq i]

end VSCLReuse

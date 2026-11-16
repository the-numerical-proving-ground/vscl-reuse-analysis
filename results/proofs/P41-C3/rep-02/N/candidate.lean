import VSCLReuse.P41.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p41_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : P41GammaValid u n) : 0 ≤ p41Gamma u n := by
  unfold p41Gamma P41GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr h))

private theorem p41_gamma_step (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (h : P41GammaValid u (m + 1)) :
    p41Gamma u m + u ≤ (1 - u) * p41Gamma u (m + 1) := by
  have hm : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hmu : 0 ≤ (m : ℝ) * u * u := mul_nonneg hm hu
  have h1 : 0 < 1 - (m : ℝ) * u := by
    unfold P41GammaValid at h
    push_cast at h
    nlinarith
  have h2 : 0 < 1 - ((m : ℝ) + 1) * u := by
    unfold P41GammaValid at h
    push_cast at h
    linarith
  unfold p41Gamma
  push_cast
  let v : ℝ := (m : ℝ) * u
  let g : ℝ := v / (1 - v)
  let G : ℝ := (v + u) / (1 - v - u)
  have hv : 0 ≤ v := hm
  have hd1 : 0 < 1 - v := h1
  have hd2 : 0 < 1 - v - u := by dsimp [v]; nlinarith [h2]
  have hg : g * (1 - v) = v := by
    dsimp [g]
    exact div_mul_cancel₀ _ (ne_of_gt hd1)
  have hG : G * (1 - v - u) = v + u := by
    dsimp [G]
    exact div_mul_cancel₀ _ (ne_of_gt hd2)
  have hid :
      (g + u - (1 - u) * G) * ((1 - v) * (1 - v - u)) = -(v * u) := by
    calc
      _ = (g * (1 - v) + u * (1 - v)) * (1 - v - u) -
          (1 - u) * (G * (1 - v - u)) * (1 - v) := by ring
      _ = -(v * u) := by rw [hg, hG]; ring
  have hgoal : g + u ≤ (1 - u) * G := by
    by_contra hn
    have hp := mul_pos hd1 hd2
    have hp' : 0 < (g + u - (1 - u) * G) * ((1 - v) * (1 - v - u)) := by
      apply mul_pos
      · linarith
      · exact hp
    linarith
  have hnum : ((m : ℝ) + 1) * u = v + u := by dsimp [v]; ring
  have hden : 1 - (v + u) = 1 - v - u := by ring
  rw [hnum, hden]
  exact hgoal

private theorem p41_gamma_mono (u : ℝ) (m n : ℕ)
    (hu : 0 ≤ u) (hmn : m ≤ n) (hn : P41GammaValid u n) :
    p41Gamma u m ≤ p41Gamma u n := by
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hd2 : 0 < 1 - (n : ℝ) * u := by
    unfold P41GammaValid at hn
    linarith
  have hd1 : 0 < 1 - (m : ℝ) * u := by linarith
  unfold p41Gamma
  apply (div_le_div_iff₀ hd1 hd2).2
  nlinarith

private theorem p41_gamma_ge_u (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hm : 1 ≤ m) (hvalid : P41GammaValid u m) :
    u ≤ p41Gamma u m := by
  have hcast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmu : u ≤ (m : ℝ) * u := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hu]
  have hden : 0 < 1 - (m : ℝ) * u := by
    unfold P41GammaValid at hvalid
    linarith
  unfold p41Gamma
  apply (le_div_iff₀ hden).2
  nlinarith [mul_nonneg (le_trans hu hmu) hu]

private theorem p41_gamma_forward_step (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hvalid : P41GammaValid u (m + 1)) :
    (1 + u) * p41Gamma u m + u ≤ p41Gamma u (m + 1) := by
  have hu1 : u < 1 := by
    unfold P41GammaValid at hvalid
    push_cast at hvalid
    nlinarith
  have hm : P41GammaValid u m := by
    unfold P41GammaValid at *
    push_cast at hvalid
    nlinarith
  have hg := p41_gamma_nonneg u m hu hm
  have hG := p41_gamma_nonneg u (m + 1) hu hvalid
  have hs := p41_gamma_step u m hu hvalid
  have haux : 0 ≤ u ^ 2 * (p41Gamma u m + 1) := by positivity
  nlinarith

private theorem p41_one_step_bound
    (u g G W t v a a' dm ds : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hW : 0 ≤ W)
    (hg : 0 ≤ g) (hG : 0 ≤ G)
    (hstep : g + u ≤ (1 - u) * G)
    (hdm : |dm| ≤ u) (hds : |ds| ≤ u)
    (ha : a' = (a - t * (1 + dm)) * (1 + ds))
    (hv : |v| ≤ W) (hr : |a' - v| ≤ g * W) :
    |a - (v + t)| ≤ G * (W + |t|) := by
  let q := 1 + ds
  have hq : 0 < q := by
    have := (abs_le.mp hds).1
    dsimp [q]
    linarith
  have hqlo : 1 - u ≤ q := by
    have := (abs_le.mp hds).1
    dsimp [q]
    linarith
  have hqG : g + u ≤ q * G := by
    calc
      g + u ≤ (1 - u) * G := hstep
      _ ≤ q * G := mul_le_mul_of_nonneg_right hqlo hG
  have huG : u ≤ G := by
    have hbase : 1 - u ≤ 1 := by linarith
    have hh : (1 - u) * G ≤ G := by nlinarith
    linarith
  have hid : q * (a - (v + t)) = (a' - v) - v * ds + q * (t * dm) := by
    rw [ha]
    dsimp [q]
    ring
  have htri : |q * (a - (v + t))| ≤
      |a' - v| + |v * ds| + |q * (t * dm)| := by
    rw [hid]
    calc
      _ ≤ |(a' - v) - v * ds| + |q * (t * dm)| := abs_add_le _ _
      _ ≤ |a' - v| + |v * ds| + |q * (t * dm)| := by
        have hh := abs_add_le (a' - v) (-(v * ds))
        simp only [sub_eq_add_neg, abs_neg] at hh ⊢
        linarith
  have hvm : |v * ds| ≤ W * u := by
    rw [abs_mul]
    exact mul_le_mul hv hds (abs_nonneg _) hW
  have htm : |q * (t * dm)| ≤ q * (u * |t|) := by
    rw [abs_mul, abs_mul, abs_of_pos hq]
    have := mul_le_mul_of_nonneg_left hdm (abs_nonneg t)
    nlinarith
  have hbound : q * |a - (v + t)| ≤ (g + u) * W + q * (u * |t|) := by
    have habs : |q * (a - (v + t))| = q * |a - (v + t)| := by
      rw [abs_mul, abs_of_pos hq]
    rw [habs] at htri
    nlinarith [htri]
  have hleft : (g + u) * W ≤ q * G * W :=
    mul_le_mul_of_nonneg_right hqG hW
  have hright : q * (u * |t|) ≤ q * (G * |t|) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right huG (abs_nonneg t)) (le_of_lt hq)
  have htot : q * |a - (v + t)| ≤ q * (G * (W + |t|)) := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hq).mp htot

private theorem p41_fold_submul_bound (fp : P41FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (a : ℝ)
    (hvalid : P41GammaValid fp.u m) :
    let s := Fin.foldl m
      (fun acc i => fp.fl_sub acc (fp.fl_mul (x i) (y i))) a
    |a - (s + ∑ i : Fin m, x i * y i)| ≤
      p41Gamma fp.u m * (|s| + ∑ i : Fin m, |x i * y i|) := by
  induction m generalizing a with
  | zero =>
      simp [p41Gamma]
  | succ m ih =>
      have hm : P41GammaValid fp.u m := by
        unfold P41GammaValid at *
        have hu := fp.u_nonneg
        push_cast at hvalid
        nlinarith
      let a' := fp.fl_sub a (fp.fl_mul (x 0) (y 0))
      let xs : Fin m → ℝ := fun i => x i.succ
      let ys : Fin m → ℝ := fun i => y i.succ
      let s := Fin.foldl m
        (fun acc i => fp.fl_sub acc (fp.fl_mul (xs i) (ys i))) a'
      let T : ℝ := ∑ i : Fin m, xs i * ys i
      let W : ℝ := |s| + ∑ i : Fin m, |xs i * ys i|
      have hrec : |a' - (s + T)| ≤ p41Gamma fp.u m * W :=
        ih xs ys a' hm
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (x 0) (y 0)
      obtain ⟨ds, hds, hsub⟩ := fp.model_sub a (fp.fl_mul (x 0) (y 0))
      have ha : a' = (a - (x 0 * y 0) * (1 + dm)) * (1 + ds) := by
        dsimp [a']
        rw [hsub, hmul]
      have hW : 0 ≤ W := by
        dsimp [W]
        positivity
      have hv : |s + T| ≤ W := by
        dsimp [W, T]
        calc
          _ ≤ |s| + |∑ i : Fin m, xs i * ys i| := abs_add_le _ _
          _ ≤ |s| + ∑ i : Fin m, |xs i * ys i| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      have hstep := p41_gamma_step fp.u m fp.u_nonneg hvalid
      have hg := p41_gamma_nonneg fp.u m fp.u_nonneg hm
      have hG := p41_gamma_nonneg fp.u (m + 1) fp.u_nonneg hvalid
      have hu1 : fp.u < 1 := by
        unfold P41GammaValid at hvalid
        push_cast at hvalid
        nlinarith [fp.u_nonneg]
      have hb := p41_one_step_bound fp.u (p41Gamma fp.u m)
        (p41Gamma fp.u (m + 1)) W (x 0 * y 0) (s + T) a a' dm ds
        fp.u_nonneg hu1 hW hg hG hstep hdm hds ha hv hrec
      simpa only [Fin.foldl_succ, Fin.sum_univ_succ, xs, ys, a', s, T, W,
        add_assoc, add_comm, add_left_comm] using hb

private theorem p41_div_row_bound
    (u g G b s z T W δ : ℝ)
    (hu : 0 ≤ u) (hu1 : u < 1) (hW : 0 ≤ W)
    (hg : 0 ≤ g) (hG : 0 ≤ G)
    (hstep : g + u ≤ (1 - u) * G)
    (hδ : |δ| ≤ u) (hz : z = s * (1 + δ))
    (hr : |b - (s + T)| ≤ g * (|s| + W)) :
    |b - (z + T)| ≤ G * (|z| + W) := by
  let q := 1 + δ
  have hq : 0 < q := by
    dsimp [q]
    have hh := (abs_le.mp hδ).1
    linarith
  have hqlo : 1 - u ≤ q := by
    dsimp [q]
    have hh := (abs_le.mp hδ).1
    linarith
  have hgG : g ≤ G := by
    have hsmall : (1 - u) * G ≤ G := by nlinarith
    linarith
  have hqG : g + u ≤ q * G :=
    le_trans hstep (mul_le_mul_of_nonneg_right hqlo hG)
  have hid : q * (b - (z + T)) = q * (b - (s + T)) - δ * z := by
    rw [hz]
    dsimp [q]
    ring
  have htri : |q * (b - (z + T))| ≤
      |q * (b - (s + T))| + |δ * z| := by
    rw [hid]
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (q * (b - (s + T))) (-(δ * z))
  have hqabs : |q * (b - (z + T))| = q * |b - (z + T)| := by
    rw [abs_mul, abs_of_pos hq]
  have hqabs' : |q * (b - (s + T))| = q * |b - (s + T)| := by
    rw [abs_mul, abs_of_pos hq]
  have hzabs : |z| = q * |s| := by
    rw [hz, abs_mul, abs_of_pos hq]
    ring
  have hδz : |δ * z| ≤ u * |z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg z)
  have hbound : q * |b - (z + T)| ≤ (g + u) * |z| + q * (g * W) := by
    rw [hqabs, hqabs'] at htri
    have hhr := mul_le_mul_of_nonneg_left hr (le_of_lt hq)
    nlinarith [htri, hhr, hδz, hzabs]
  have hleft : (g + u) * |z| ≤ q * G * |z| :=
    mul_le_mul_of_nonneg_right hqG (abs_nonneg z)
  have hright : q * (g * W) ≤ q * (G * W) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hgG hW) (le_of_lt hq)
  have htot : q * |b - (z + T)| ≤ q * (G * (|z| + W)) := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_left hq).mp htot

private theorem p41_submul_div_bound (fp : P41FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (b d : ℝ) (hd : d ≠ 0)
    (hvalid : P41GammaValid fp.u (m + 1)) :
    let s := Fin.foldl m
      (fun acc i => fp.fl_sub acc (fp.fl_mul (x i) (y i))) b
    let z := d * fp.fl_div s d
    |b - (z + ∑ i : Fin m, x i * y i)| ≤
      p41Gamma fp.u (m + 1) *
        (|z| + ∑ i : Fin m, |x i * y i|) := by
  have hm : P41GammaValid fp.u m := by
    unfold P41GammaValid at *
    push_cast at hvalid
    nlinarith [fp.u_nonneg]
  let s := Fin.foldl m
    (fun acc i => fp.fl_sub acc (fp.fl_mul (x i) (y i))) b
  let T : ℝ := ∑ i : Fin m, x i * y i
  let W : ℝ := ∑ i : Fin m, |x i * y i|
  have hfold : |b - (s + T)| ≤ p41Gamma fp.u m * (|s| + W) :=
    p41_fold_submul_bound fp m x y b hm
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s d hd
  let z := d * fp.fl_div s d
  have hz : z = s * (1 + δ) := by
    dsimp [z]
    rw [hdiv]
    field_simp [hd]
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hstep := p41_gamma_step fp.u m fp.u_nonneg hvalid
  have hg := p41_gamma_nonneg fp.u m fp.u_nonneg hm
  have hG := p41_gamma_nonneg fp.u (m + 1) fp.u_nonneg hvalid
  have hu1 : fp.u < 1 := by
    unfold P41GammaValid at hvalid
    push_cast at hvalid
    nlinarith [fp.u_nonneg]
  exact p41_div_row_bound fp.u (p41Gamma fp.u m)
    (p41Gamma fp.u (m + 1)) b s z T W δ
    fp.u_nonneg hu1 hW hg hG hstep hδ hz hfold

private theorem p41_lower_sum (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      f i + ∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩ := by
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j.val < i.val)
  have hprefix :
      (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) =
        ∑ j ∈ S, f j := by
    apply Finset.sum_bij
      (fun (t : Fin i.val) (_ : t ∈ (Finset.univ : Finset (Fin i.val))) =>
        (⟨t.val, lt_trans t.isLt i.isLt⟩ : Fin n))
    · intro t ht
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact t.isLt
    · intro t₁ ht₁ t₂ ht₂ heq
      exact Fin.ext (by simpa using congrArg Fin.val heq)
    · intro j hj
      have hji : j.val < i.val := by simpa [S] using hj
      refine ⟨⟨j.val, hji⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro t ht
      rfl
  have hdecomp : (∑ j : Fin n, f j) = f i + ∑ j ∈ S, f j := by
    calc
      (∑ j : Fin n, f j) =
          (∑ j : Fin n, if j = i then f j else 0) +
          (∑ j : Fin n, if j.val < i.val then f j else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · by_cases hjlt : j.val < i.val
          · simp [hji, hjlt]
          · have hij : i.val < j.val := by omega
            simp [hji, hjlt, hzero j hij]
      _ = f i + ∑ j ∈ S, f j := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Finset.sum_filter]
  rw [hdecomp, hprefix]

private theorem p41_upper_sum (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) =
      f i + ∑ t : Fin (n - i.val - 1),
        f ⟨i.val + 1 + t.val, by omega⟩ := by
  let S : Finset (Fin n) := Finset.univ.filter (fun j => i.val < j.val)
  have hprefix :
      (∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩) =
        ∑ j ∈ S, f j := by
    apply Finset.sum_bij
      (fun (t : Fin (n - i.val - 1))
        (_ : t ∈ (Finset.univ : Finset (Fin (n - i.val - 1)))) =>
        (⟨i.val + 1 + t.val, by omega⟩ : Fin n))
    · intro t ht
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro t₁ ht₁ t₂ ht₂ heq
      apply Fin.ext
      have := congrArg Fin.val heq
      dsimp at this
      omega
    · intro j hj
      have hji : i.val < j.val := by simpa [S] using hj
      refine ⟨⟨j.val - i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp
      omega
    · intro t ht
      rfl
  have hdecomp : (∑ j : Fin n, f j) = f i + ∑ j ∈ S, f j := by
    calc
      (∑ j : Fin n, f j) =
          (∑ j : Fin n, if j = i then f j else 0) +
          (∑ j : Fin n, if i.val < j.val then f j else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · by_cases hjlt : i.val < j.val
          · simp [hji, hjlt]
          · have hij : j.val < i.val := by omega
            simp [hji, hjlt, hzero j hij]
      _ = f i + ∑ j ∈ S, f j := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Finset.sum_filter]
  rw [hdecomp, hprefix]

private theorem p41_forward_preserve (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (j : Fin n),
      j.val < n - k →
      p41ForwardSubSteps fp n L b k hk x j = x j := by
  intro k
  induction k with
  | zero =>
      intro hk x j hj
      rfl
  | succ k ih =>
      intro hk x j hj
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
      have hjk : j.val < n - k := by omega
      have hne : j ≠ ik := by
        intro heq
        have := congrArg Fin.val heq
        dsimp [ik] at this
        omega
      have hpres := ih (Nat.le_of_succ_le hk) x' j hjk
      change p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' j = x j
      rw [hpres]
      exact Function.update_of_ne hne _ x

private theorem p41_forward_row_update (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hupper : ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hdiag : L i i ≠ 0) (hvalid : P41GammaValid fp.u n) :
    let s := Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        fp.fl_sub acc
          (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt i.isLt⟩)))
      (b i)
    let y := Function.update x i (fp.fl_div s (L i i))
    |b i - ∑ j : Fin n, L i j * y j| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |L i j * y j| := by
  let xv : Fin i.val → ℝ :=
    fun t => L i ⟨t.val, lt_trans t.isLt i.isLt⟩
  let yv : Fin i.val → ℝ :=
    fun t => x ⟨t.val, lt_trans t.isLt i.isLt⟩
  let s := Fin.foldl i.val
    (fun acc t => fp.fl_sub acc (fp.fl_mul (xv t) (yv t))) (b i)
  let y := Function.update x i (fp.fl_div s (L i i))
  have hsmall : P41GammaValid fp.u (i.val + 1) := by
    unfold P41GammaValid at *
    have hic : i.val + 1 ≤ n := by omega
    have hcast : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hic
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
  have hdiv := p41_submul_div_bound fp i.val xv yv (b i) (L i i) hdiag hsmall
  have hyi : y i = fp.fl_div s (L i i) := by simp [y]
  have hyprefix (t : Fin i.val) :
      y ⟨t.val, lt_trans t.isLt i.isLt⟩ = yv t := by
    dsimp [y, yv]
    have hne : (⟨t.val, lt_trans t.isLt i.isLt⟩ : Fin n) ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      dsimp at this
      omega
    exact Function.update_of_ne hne _ x
  have hsum : (∑ j : Fin n, L i j * y j) =
      L i i * fp.fl_div s (L i i) + ∑ t : Fin i.val, xv t * yv t := by
    rw [p41_lower_sum n i (fun j => L i j * y j)]
    · rw [hyi]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      simp only [xv, yv, hyprefix]
    · intro j hij
      rw [hupper j hij, zero_mul]
  have habssum : (∑ j : Fin n, |L i j * y j|) =
      |L i i * fp.fl_div s (L i i)| +
        ∑ t : Fin i.val, |xv t * yv t| := by
    rw [p41_lower_sum n i (fun j => |L i j * y j|)]
    · rw [hyi]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      simp only [xv, yv, hyprefix]
    · intro j hij
      rw [hupper j hij, zero_mul, abs_zero]
  have hmono := p41_gamma_mono fp.u (i.val + 1) n
    fp.u_nonneg (by omega) hvalid
  have hweight : 0 ≤ |L i i * fp.fl_div s (L i i)| +
      ∑ t : Fin i.val, |xv t * yv t| := by positivity
  have hdiv' :
      |b i - (L i i * fp.fl_div s (L i i) +
        ∑ t : Fin i.val, xv t * yv t)| ≤
      p41Gamma fp.u n *
        (|L i i * fp.fl_div s (L i i)| +
          ∑ t : Fin i.val, |xv t * yv t|) :=
    le_trans hdiv (mul_le_mul_of_nonneg_right hmono hweight)
  change |b i - ∑ j : Fin n, L i j * y j| ≤
    p41Gamma fp.u n * ∑ j : Fin n, |L i j * y j|
  rw [hsum, habssum]
  exact hdiv'

private theorem p41_lower_row_transfer (n : ℕ) (L : P41Matrix n n)
    (i : Fin n) (x y : Fin n → ℝ)
    (hupper : ∀ j : Fin n, i.val < j.val → L i j = 0)
    (hxy : ∀ j : Fin n, j.val ≤ i.val → x j = y j) :
    (∑ j : Fin n, L i j * x j) = (∑ j : Fin n, L i j * y j) ∧
    (∑ j : Fin n, |L i j * x j|) = (∑ j : Fin n, |L i j * y j|) := by
  constructor
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j.val ≤ i.val
    · rw [hxy j hji]
    · have hij : i.val < j.val := by omega
      rw [hupper j hij, zero_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j.val ≤ i.val
    · rw [hxy j hji]
    · have hij : i.val < j.val := by omega
      rw [hupper j hij, zero_mul, zero_mul]

private theorem p41_forward_steps_bound (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      (∀ i : Fin n, i.val < n - k →
        |b i - ∑ j : Fin n, L i j * x j| ≤
          p41Gamma fp.u n * ∑ j : Fin n, |L i j * x j|) →
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, L i j *
          p41ForwardSubSteps fp n L b k hk x j| ≤
          p41Gamma fp.u n *
            ∑ j : Fin n, |L i j * p41ForwardSubSteps fp n L b k hk x j| := by
  intro k
  induction k with
  | zero =>
      intro hk x hinv i
      exact hinv i (by omega)
  | succ k ih =>
      intro hk x hinv i
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let y : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hcur :
          |b ik - ∑ j : Fin n, L ik j * y j| ≤
            p41Gamma fp.u n * ∑ j : Fin n, |L ik j * y j| := by
        have hh := p41_forward_row_update fp n L b x ik
          (hupper ik) (hdiag ik) hvalid
        exact hh
      have hinv' : ∀ r : Fin n, r.val < n - k →
          |b r - ∑ j : Fin n, L r j * y j| ≤
            p41Gamma fp.u n * ∑ j : Fin n, |L r j * y j| := by
        intro r hr
        by_cases hri : r = ik
        · subst r
          exact hcur
        · have hrprev : r.val < n - (k + 1) := by
            have hvalne : r.val ≠ ik.val := by
              intro heq
              exact hri (Fin.ext heq)
            dsimp [ik] at hvalne
            omega
          have hxy : ∀ j : Fin n, j.val ≤ r.val → x j = y j := by
            intro j hj
            have hne : j ≠ ik := by
              intro heq
              have := congrArg Fin.val heq
              have hrlt : r.val < ik.val := by dsimp [ik]; omega
              omega
            exact (Function.update_of_ne hne _ x).symm
          obtain ⟨hsum, habs⟩ := p41_lower_row_transfer n L r x y
            (hupper r) hxy
          rw [← hsum, ← habs]
          exact hinv r hrprev
      have hfinal := ih (Nat.le_of_succ_le hk) y hinv' i
      change
        |b i - ∑ j : Fin n, L i j *
          p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) y j| ≤
          p41Gamma fp.u n *
            ∑ j : Fin n, |L i j *
              p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) y j|
      exact hfinal

private theorem p41_forward_bound (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    let x := p41ForwardSub fp n L b
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, L i j * x j| ≤
        p41Gamma fp.u n * ∑ j : Fin n, |L i j * x j| := by
  change ∀ i : Fin n,
    |b i - ∑ j : Fin n, L i j * p41ForwardSub fp n L b j| ≤
      p41Gamma fp.u n *
        ∑ j : Fin n, |L i j * p41ForwardSub fp n L b j|
  intro i
  exact p41_forward_steps_bound fp n L b hupper hdiag hvalid
    n (le_refl n) (fun _ => 0) (by intro j hj; omega) i

private theorem p41_back_row_update (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hlower : ∀ j : Fin n, j.val < i.val → U i j = 0)
    (hdiag : U i i ≠ 0) (hvalid : P41GammaValid fp.u n) :
    let count := n - i.val - 1
    let s := Fin.foldl count
      (fun acc (t : Fin count) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩)))
      (b i)
    let y := Function.update x i (fp.fl_div s (U i i))
    |b i - ∑ j : Fin n, U i j * y j| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |U i j * y j| := by
  let count := n - i.val - 1
  let xv : Fin count → ℝ :=
    fun t => U i ⟨i.val + 1 + t.val, by dsimp [count] at t ⊢; omega⟩
  let yv : Fin count → ℝ :=
    fun t => x ⟨i.val + 1 + t.val, by dsimp [count] at t ⊢; omega⟩
  let s := Fin.foldl count
    (fun acc t => fp.fl_sub acc (fp.fl_mul (xv t) (yv t))) (b i)
  let y := Function.update x i (fp.fl_div s (U i i))
  have hsmall : P41GammaValid fp.u (count + 1) := by
    unfold P41GammaValid at *
    have hic : count + 1 ≤ n := by dsimp [count]; omega
    have hcast : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hic
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
  have hdiv := p41_submul_div_bound fp count xv yv (b i) (U i i) hdiag hsmall
  have hyi : y i = fp.fl_div s (U i i) := by simp [y]
  have hysuffix (t : Fin count) :
      y ⟨i.val + 1 + t.val, by dsimp [count] at t ⊢; omega⟩ = yv t := by
    dsimp [y, yv]
    have hne : (⟨i.val + 1 + t.val, by dsimp [count] at t ⊢; omega⟩ : Fin n) ≠ i := by
      intro heq
      have := congrArg Fin.val heq
      dsimp at this
      omega
    exact Function.update_of_ne hne _ x
  have hsum : (∑ j : Fin n, U i j * y j) =
      U i i * fp.fl_div s (U i i) + ∑ t : Fin count, xv t * yv t := by
    rw [p41_upper_sum n i (fun j => U i j * y j)]
    · rw [hyi]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      simp only [xv, yv, hysuffix]
    · intro j hij
      rw [hlower j hij, zero_mul]
  have habssum : (∑ j : Fin n, |U i j * y j|) =
      |U i i * fp.fl_div s (U i i)| +
        ∑ t : Fin count, |xv t * yv t| := by
    rw [p41_upper_sum n i (fun j => |U i j * y j|)]
    · rw [hyi]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      simp only [xv, yv, hysuffix]
    · intro j hij
      rw [hlower j hij, zero_mul, abs_zero]
  have hmono := p41_gamma_mono fp.u (count + 1) n
    fp.u_nonneg (by dsimp [count]; omega) hvalid
  have hweight : 0 ≤ |U i i * fp.fl_div s (U i i)| +
      ∑ t : Fin count, |xv t * yv t| := by positivity
  have hdiv' :
      |b i - (U i i * fp.fl_div s (U i i) +
        ∑ t : Fin count, xv t * yv t)| ≤
      p41Gamma fp.u n *
        (|U i i * fp.fl_div s (U i i)| +
          ∑ t : Fin count, |xv t * yv t|) :=
    le_trans hdiv (mul_le_mul_of_nonneg_right hmono hweight)
  change |b i - ∑ j : Fin n, U i j * y j| ≤
    p41Gamma fp.u n * ∑ j : Fin n, |U i j * y j|
  rw [hsum, habssum]
  exact hdiv'

private theorem p41_upper_row_transfer (n : ℕ) (U : P41Matrix n n)
    (i : Fin n) (x y : Fin n → ℝ)
    (hlower : ∀ j : Fin n, j.val < i.val → U i j = 0)
    (hxy : ∀ j : Fin n, i.val ≤ j.val → x j = y j) :
    (∑ j : Fin n, U i j * x j) = (∑ j : Fin n, U i j * y j) ∧
    (∑ j : Fin n, |U i j * x j|) = (∑ j : Fin n, |U i j * y j|) := by
  constructor
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : i.val ≤ j.val
    · rw [hxy j hji]
    · have hij : j.val < i.val := by omega
      rw [hlower j hij, zero_mul, zero_mul]
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : i.val ≤ j.val
    · rw [hxy j hji]
    · have hij : j.val < i.val := by omega
      rw [hlower j hij, zero_mul, zero_mul]

private theorem p41_back_steps_bound (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hlower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      (∀ i : Fin n, k ≤ i.val →
        |b i - ∑ j : Fin n, U i j * x j| ≤
          p41Gamma fp.u n * ∑ j : Fin n, |U i j * x j|) →
      ∀ i : Fin n,
        |b i - ∑ j : Fin n, U i j *
          p41BackSubSteps fp n U b k hk x j| ≤
          p41Gamma fp.u n *
            ∑ j : Fin n, |U i j * p41BackSubSteps fp n U b k hk x j| := by
  intro k
  induction k with
  | zero =>
      intro hk x hinv i
      exact hinv i (by omega)
  | succ k ih =>
      intro hk x hinv i
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let y : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hcur :
          |b ik - ∑ j : Fin n, U ik j * y j| ≤
            p41Gamma fp.u n * ∑ j : Fin n, |U ik j * y j| := by
        have hh := p41_back_row_update fp n U b x ik
          (hlower ik) (hdiag ik) hvalid
        exact hh
      have hinv' : ∀ r : Fin n, k ≤ r.val →
          |b r - ∑ j : Fin n, U r j * y j| ≤
            p41Gamma fp.u n * ∑ j : Fin n, |U r j * y j| := by
        intro r hr
        by_cases hri : r = ik
        · subst r
          exact hcur
        · have hrprev : k + 1 ≤ r.val := by
            have hvalne : r.val ≠ ik.val := by
              intro heq
              exact hri (Fin.ext heq)
            dsimp [ik] at hvalne
            omega
          have hxy : ∀ j : Fin n, r.val ≤ j.val → x j = y j := by
            intro j hj
            have hne : j ≠ ik := by
              intro heq
              have := congrArg Fin.val heq
              have hrlt : ik.val < r.val := by dsimp [ik]; omega
              omega
            exact (Function.update_of_ne hne _ x).symm
          obtain ⟨hsum, habs⟩ := p41_upper_row_transfer n U r x y
            (hlower r) hxy
          rw [← hsum, ← habs]
          exact hinv r hrprev
      have hfinal := ih (Nat.le_of_succ_le hk) y hinv' i
      change
        |b i - ∑ j : Fin n, U i j *
          p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) y j| ≤
          p41Gamma fp.u n *
            ∑ j : Fin n, |U i j *
              p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) y j|
      exact hfinal

private theorem p41_back_bound (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hlower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    let x := p41BackSub fp n U b
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, U i j * x j| ≤
        p41Gamma fp.u n * ∑ j : Fin n, |U i j * x j| := by
  change ∀ i : Fin n,
    |b i - ∑ j : Fin n, U i j * p41BackSub fp n U b j| ≤
      p41Gamma fp.u n *
        ∑ j : Fin n, |U i j * p41BackSub fp n U b j|
  intro i
  exact p41_back_steps_bound fp n U b hlower hdiag hvalid
    n (le_refl n) (fun _ => 0) (by intro j hj; omega) i

private theorem p41_abs_sum_mul_le {n : ℕ} (a b : Fin n → ℝ) :
    |∑ j : Fin n, a j * b j| ≤ ∑ j : Fin n, |a j| * |b j| := by
  calc
    _ ≤ ∑ j : Fin n, |a j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, |a j| * |b j| := by simp only [abs_mul]

private theorem p41_lu_assoc (n : ℕ) (L U : P41Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) :
    (∑ k : Fin n, (∑ j : Fin n, L i j * U j k) * x k) =
      ∑ j : Fin n, L i j * (∑ k : Fin n, U j k * x k) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext k
  ring

private theorem p41_lu_weight_assoc (n : ℕ) (L U : P41Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) :
    (∑ k : Fin n, (∑ j : Fin n, |L i j| * |U j k|) * |x k|) =
      ∑ j : Fin n, |L i j| * (∑ k : Fin n, |U j k * x k|) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum, abs_mul]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext k
  ring

private theorem p41_lu_solve_residual_bound (fp : P41FPModel) (n : ℕ)
    (A L U : P41Matrix n n) (b : Fin n → ℝ)
    (hcert : P41LUCertificate fp n A L U)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hvalid : P41GammaValid fp.u n) :
    let x := p41LUSolve fp n L U b
    ∀ i : Fin n,
      |(∑ k : Fin n, A i k * x k) - b i| ≤
        (3 * p41Gamma fp.u n + p41Gamma fp.u n ^ 2) *
          ∑ k : Fin n,
            (∑ j : Fin n, |L i j| * |U j k|) * |x k| := by
  let γ := p41Gamma fp.u n
  let y := p41ForwardSub fp n L b
  let x := p41BackSub fp n U y
  have hγ : 0 ≤ γ := p41_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hLdiag : ∀ i : Fin n, L i i ≠ 0 := by
    intro i
    rw [hcert.L_diag i]
    exact one_ne_zero
  have hF : ∀ i : Fin n,
      |b i - ∑ j : Fin n, L i j * y j| ≤
        γ * ∑ j : Fin n, |L i j * y j| :=
    p41_forward_bound fp n L b hcert.L_upper_zero hLdiag hvalid
  have hB : ∀ i : Fin n,
      |y i - ∑ k : Fin n, U i k * x k| ≤
        γ * ∑ k : Fin n, |U i k * x k| :=
    p41_back_bound fp n U y hcert.U_lower_zero hdiag hvalid
  change ∀ i : Fin n,
    |(∑ k : Fin n, A i k * x k) - b i| ≤
      (3 * γ + γ ^ 2) *
        ∑ k : Fin n,
          (∑ j : Fin n, |L i j| * |U j k|) * |x k|
  intro i
  let Q : Fin n → ℝ := fun j => ∑ k : Fin n, |U j k * x k|
  let W : ℝ := ∑ j : Fin n, |L i j| * Q j
  have hQ (j : Fin n) : 0 ≤ Q j := by dsimp [Q]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hy (j : Fin n) : |y j| ≤ (1 + γ) * Q j := by
    have hsum :
        |∑ k : Fin n, U j k * x k| ≤ Q j := by
      dsimp [Q]
      exact Finset.abs_sum_le_sum_abs _ _
    have htri : |y j| ≤
        |y j - ∑ k : Fin n, U j k * x k| +
          |∑ k : Fin n, U j k * x k| := by
      have hh := abs_add_le
        (y j - ∑ k : Fin n, U j k * x k)
        (∑ k : Fin n, U j k * x k)
      have heq :
          (y j - ∑ k : Fin n, U j k * x k) +
            (∑ k : Fin n, U j k * x k) = y j := by ring
      rw [heq] at hh
      exact hh
    have hBj := hB j
    nlinarith
  have hsumY :
      (∑ j : Fin n, |L i j * y j|) ≤ (1 + γ) * W := by
    calc
      _ = ∑ j : Fin n, |L i j| * |y j| := by simp only [abs_mul]
      _ ≤ ∑ j : Fin n, |L i j| * ((1 + γ) * Q j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _)
      _ = (1 + γ) * W := by
        dsimp [W]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hforward :
      |(∑ j : Fin n, L i j * y j) - b i| ≤ γ * ((1 + γ) * W) := by
    rw [abs_sub_comm]
    exact le_trans (hF i) (mul_le_mul_of_nonneg_left hsumY hγ)
  have hupper :
      |∑ j : Fin n,
        L i j * ((∑ k : Fin n, U j k * x k) - y j)| ≤ γ * W := by
    calc
      _ ≤ ∑ j : Fin n,
          |L i j| * |(∑ k : Fin n, U j k * x k) - y j| :=
        p41_abs_sum_mul_le (L i)
          (fun j => (∑ k : Fin n, U j k * x k) - y j)
      _ ≤ ∑ j : Fin n, |L i j| * (γ * Q j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)
      _ = γ * W := by
        dsimp [W]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hfactor :
      |∑ k : Fin n,
        (A i k - ∑ j : Fin n, L i j * U j k) * x k| ≤ γ * W := by
    calc
      _ ≤ ∑ k : Fin n,
          |A i k - ∑ j : Fin n, L i j * U j k| * |x k| :=
        p41_abs_sum_mul_le
          (fun k => A i k - ∑ j : Fin n, L i j * U j k) x
      _ ≤ ∑ k : Fin n,
          (γ * ∑ j : Fin n, |L i j| * |U j k|) * |x k| := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_sub_comm]
        exact mul_le_mul_of_nonneg_right (hcert.backward_bound i k) (abs_nonneg _)
      _ = γ * W := by
        calc
          _ = γ * ∑ k : Fin n,
              (∑ j : Fin n, |L i j| * |U j k|) * |x k| := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = γ * W := by rw [p41_lu_weight_assoc]
  have hid :
      (∑ k : Fin n, A i k * x k) - b i =
      (∑ k : Fin n,
        (A i k - ∑ j : Fin n, L i j * U j k) * x k) +
      (∑ j : Fin n,
        L i j * ((∑ k : Fin n, U j k * x k) - y j)) +
      ((∑ j : Fin n, L i j * y j) - b i) := by
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [← p41_lu_assoc n L U x i]
    ring
  rw [hid]
  calc
    _ ≤ |∑ k : Fin n,
          (A i k - ∑ j : Fin n, L i j * U j k) * x k| +
        |∑ j : Fin n,
          L i j * ((∑ k : Fin n, U j k * x k) - y j)| +
        |(∑ j : Fin n, L i j * y j) - b i| := by
      have h1 := abs_add_le
        ((∑ k : Fin n,
          (A i k - ∑ j : Fin n, L i j * U j k) * x k) +
         (∑ j : Fin n,
          L i j * ((∑ k : Fin n, U j k * x k) - y j)))
        ((∑ j : Fin n, L i j * y j) - b i)
      have h2 := abs_add_le
        (∑ k : Fin n,
          (A i k - ∑ j : Fin n, L i j * U j k) * x k)
        (∑ j : Fin n,
          L i j * ((∑ k : Fin n, U j k * x k) - y j))
      linarith
    _ ≤ (3 * γ + γ ^ 2) *
        ∑ k : Fin n,
          (∑ j : Fin n, |L i j| * |U j k|) * |x k| := by
      rw [p41_lu_weight_assoc]
      nlinarith [hfactor, hupper, hforward]

private theorem p41_residual_matrix (n : ℕ)
    (M : P41Matrix n n) (x r : Fin n → ℝ) (C : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hC : 0 ≤ C)
    (hr : ∀ i, |r i| ≤ C * ∑ j : Fin n, M i j * |x j|) :
    ∃ D : P41Matrix n n,
      (∀ i j, |D i j| ≤ C * M i j) ∧
      (∀ i, r i = -(∑ j : Fin n, D i j * x j)) := by
  let σ : ℝ → ℝ := fun t => if t < 0 then -1 else 1
  have hσmul (t : ℝ) : σ t * t = |t| := by
    by_cases ht : t < 0
    · simp [σ, ht, abs_of_neg ht]
    · simp [σ, ht, abs_of_nonneg (le_of_not_gt ht)]
  have hσabs (t : ℝ) : |σ t| = 1 := by
    by_cases ht : t < 0 <;> simp [σ, ht]
  let den : Fin n → ℝ := fun i => ∑ j : Fin n, M i j * |x j|
  let D : P41Matrix n n := fun i j =>
    if den i = 0 then 0 else -(r i / den i) * M i j * σ (x j)
  refine ⟨D, ?_, ?_⟩
  · intro i j
    have hden0 : 0 ≤ den i := by
      dsimp [den]
      exact Finset.sum_nonneg fun j hj => mul_nonneg (hM i j) (abs_nonneg _)
    by_cases hzero : den i = 0
    · simpa [D, hzero] using mul_nonneg hC (hM i j)
    · have hden : 0 < den i := lt_of_le_of_ne hden0 (Ne.symm hzero)
      have hquot : |r i / den i| ≤ C := by
        rw [abs_div, abs_of_pos hden]
        exact (div_le_iff₀ hden).2 (hr i)
      dsimp [D]
      rw [if_neg hzero, abs_mul, abs_mul, abs_neg, hσabs,
        abs_of_nonneg (hM i j), mul_one]
      exact mul_le_mul_of_nonneg_right hquot (hM i j)
  · intro i
    have hden0 : 0 ≤ den i := by
      dsimp [den]
      exact Finset.sum_nonneg fun j hj => mul_nonneg (hM i j) (abs_nonneg _)
    by_cases hzero : den i = 0
    · have hri : r i = 0 := by
        have h := hr i
        change |r i| ≤ C * den i at h
        rw [hzero, mul_zero] at h
        exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simp [D, hzero, hri]
    · have hden : 0 < den i := lt_of_le_of_ne hden0 (Ne.symm hzero)
      have hsum : (∑ j : Fin n, D i j * x j) = -(r i / den i) * den i := by
        dsimp [D]
        simp only [if_neg hzero]
        calc
          _ = ∑ j : Fin n, (-(r i / den i)) *
              (M i j * (σ (x j) * x j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = -(r i / den i) * den i := by
            simp_rw [hσmul]
            rw [Finset.mul_sum]
      rw [hsum]
      dsimp [den] at hden
      field_simp [hzero]

private theorem p41_forward_one_step_bound
    (u g G W t v a a' dm ds : ℝ)
    (hu : 0 ≤ u) (hW : 0 ≤ W) (hg : 0 ≤ g)
    (hug : u ≤ g)
    (hstep : (1 + u) * g + u ≤ G)
    (hdm : |dm| ≤ u) (hds : |ds| ≤ u)
    (ha : a' = (a + t * (1 + dm)) * (1 + ds))
    (hv : |v| ≤ W) (hr : |a - v| ≤ g * W) :
    |a' - (v + t)| ≤ G * (W + |t|) := by
  let q := 1 + ds
  let c := dm + ds + dm * ds
  have hq : |q| ≤ 1 + u := by
    dsimp [q]
    calc
      _ ≤ 1 + |ds| := by
        simpa using abs_add_le (1 : ℝ) ds
      _ ≤ 1 + u := by linarith
  have hc : |c| ≤ 2 * u + u ^ 2 := by
    dsimp [c]
    have h1 := abs_add_le (dm + ds) (dm * ds)
    have h2 := abs_add_le dm ds
    have h3 : |dm * ds| ≤ u ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hdm hds (abs_nonneg _) hu
    nlinarith
  have hGterm : 2 * u + u ^ 2 ≤ G := by
    have hnon : 0 ≤ 1 + u := by linarith
    have hmul := mul_le_mul_of_nonneg_left hug hnon
    nlinarith
  have hid : a' - (v + t) = (a - v) * q + v * ds + t * c := by
    rw [ha]
    dsimp [q, c]
    ring
  have htri : |a' - (v + t)| ≤
      |a - v| * |q| + |v| * |ds| + |t| * |c| := by
    rw [hid]
    calc
      _ ≤ |(a - v) * q + v * ds| + |t * c| := abs_add_le _ _
      _ ≤ |(a - v) * q| + |v * ds| + |t * c| := by
        have hh := abs_add_le ((a - v) * q) (v * ds)
        linarith
      _ = |a - v| * |q| + |v| * |ds| + |t| * |c| := by
        simp only [abs_mul]
  have hfirst : |a - v| * |q| ≤ (1 + u) * g * W := by
    have hqa : 0 ≤ |q| := abs_nonneg q
    have h1 := mul_le_mul_of_nonneg_right hr hqa
    have h2 := mul_le_mul_of_nonneg_left hq (mul_nonneg hg hW)
    nlinarith
  have hsecond : |v| * |ds| ≤ W * u :=
    mul_le_mul hv hds (abs_nonneg _) hW
  have hthird : |t| * |c| ≤ G * |t| := by
    have h1 := mul_le_mul_of_nonneg_left hc (abs_nonneg t)
    have h2 := mul_le_mul_of_nonneg_right hGterm (abs_nonneg t)
    nlinarith
  have hGW : ((1 + u) * g + u) * W ≤ G * W :=
    mul_le_mul_of_nonneg_right hstep hW
  nlinarith [htri, hfirst, hsecond, hthird, hGW]

private theorem p41_fold_addmul_bound (fp : P41FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (a₀ a : ℝ)
    (hinit : |a - a₀| ≤ fp.u * |a₀|)
    (hvalid : P41GammaValid fp.u (m + 1)) :
    let s := Fin.foldl m
      (fun acc i => fp.fl_add acc (fp.fl_mul (x i) (y i))) a
    |s - (a₀ + ∑ i : Fin m, x i * y i)| ≤
      p41Gamma fp.u (m + 1) *
        (|a₀| + ∑ i : Fin m, |x i * y i|) := by
  induction m generalizing a₀ a with
  | zero =>
      have hγ := p41_gamma_ge_u fp.u 1 fp.u_nonneg (by omega) hvalid
      simpa using
        le_trans hinit (mul_le_mul_of_nonneg_right hγ (abs_nonneg a₀))
  | succ m ih =>
      have hm : P41GammaValid fp.u (m + 1) := by
        unfold P41GammaValid at *
        have hcast : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show m + 1 ≤ m + 1 + 1 by omega)
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
      let xs : Fin m → ℝ := fun i => x i.castSucc
      let ys : Fin m → ℝ := fun i => y i.castSucc
      let a' := Fin.foldl m
        (fun acc i => fp.fl_add acc (fp.fl_mul (xs i) (ys i))) a
      let T : ℝ := ∑ i : Fin m, xs i * ys i
      let W : ℝ := |a₀| + ∑ i : Fin m, |xs i * ys i|
      let t : ℝ := x (Fin.last m) * y (Fin.last m)
      let a'' := fp.fl_add a' (fp.fl_mul (x (Fin.last m)) (y (Fin.last m)))
      have hrec : |a' - (a₀ + T)| ≤ p41Gamma fp.u (m + 1) * W :=
        ih xs ys a₀ a hinit hm
      obtain ⟨dm, hdm, hmul⟩ :=
        fp.model_mul (x (Fin.last m)) (y (Fin.last m))
      obtain ⟨ds, hds, hadd⟩ :=
        fp.model_add a' (fp.fl_mul (x (Fin.last m)) (y (Fin.last m)))
      have ha : a'' = (a' + t * (1 + dm)) * (1 + ds) := by
        dsimp [a'', t]
        rw [hadd, hmul]
      have hW : 0 ≤ W := by dsimp [W]; positivity
      have hv : |a₀ + T| ≤ W := by
        dsimp [W, T]
        calc
          _ ≤ |a₀| + |∑ i : Fin m, xs i * ys i| := abs_add_le _ _
          _ ≤ |a₀| + ∑ i : Fin m, |xs i * ys i| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
      have hstep := p41_gamma_forward_step fp.u (m + 1)
        fp.u_nonneg hvalid
      have hg := p41_gamma_nonneg fp.u (m + 1) fp.u_nonneg hm
      have hug := p41_gamma_ge_u fp.u (m + 1) fp.u_nonneg
        (by omega) hm
      have hb := p41_forward_one_step_bound fp.u
        (p41Gamma fp.u (m + 1)) (p41Gamma fp.u (m + 2))
        W t (a₀ + T) a' a'' dm ds fp.u_nonneg hW hg hug
        hstep hdm hds ha hv hrec
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        xs, ys, a', a'', T, W, t, add_assoc, add_comm, add_left_comm]
        using hb

private theorem p41_rounded_dot_bound (fp : P41FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P41GammaValid fp.u n) :
    |p41RoundedDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      p41Gamma fp.u n * ∑ i : Fin n, |x i * y i| := by
  cases n with
  | zero =>
      simp [p41RoundedDotProduct, p41Gamma]
  | succ m =>
      obtain ⟨δ, hδ, hmul⟩ := fp.model_mul (x 0) (y 0)
      have hinit : |fp.fl_mul (x 0) (y 0) - x 0 * y 0| ≤
          fp.u * |x 0 * y 0| := by
        rw [hmul]
        have heq : x 0 * y 0 * (1 + δ) - x 0 * y 0 =
            (x 0 * y 0) * δ := by ring
        rw [heq, abs_mul]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hδ (abs_nonneg (x 0 * y 0))
      have hh := p41_fold_addmul_bound fp m
        (fun i => x i.succ) (fun i => y i.succ)
        (x 0 * y 0) (fp.fl_mul (x 0) (y 0)) hinit hvalid
      simpa only [p41RoundedDotProduct, Fin.sum_univ_succ]
        using hh

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
  let γ := p41Gamma fp.u n
  let C := 3 * γ + γ ^ 2
  let Ms : P41Matrix n n :=
    fun i j => ∑ k : Fin n, |Ls i k| * |Us k j|
  let Mn : P41Matrix n n :=
    fun i j => ∑ k : Fin n, |Ln i k| * |Un k j|
  have hγ : 0 ≤ γ := p41_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hMs : ∀ i j, 0 ≤ Ms i j := by
    intro i j
    dsimp [Ms]
    positivity
  have hMn : ∀ i j, 0 ≤ Mn i j := by
    intro i j
    dsimp [Mn]
    positivity
  have hs : ∀ i,
      |(∑ j : Fin n, Ase i j * gs j) - uvec i| ≤
        C * ∑ j : Fin n, Ms i j * |gs j| :=
    p41_lu_solve_residual_bound fp n Ase Ls Us uvec
      hLs hUsdiag hvalid
  have hn : ∀ i,
      |(∑ j : Fin n, Anw i j * gn j) - w i| ≤
        C * ∑ j : Fin n, Mn i j * |gn j| :=
    p41_lu_solve_residual_bound fp n Anw Ln Un w
      hLn hUndiag hvalid
  obtain ⟨Ds, hDs, hDse⟩ := p41_residual_matrix n Ms gs
    (fun i => (∑ j : Fin n, Ase i j * gs j) - uvec i)
    C hMs hC hs
  obtain ⟨Dn, hDn, hDne⟩ := p41_residual_matrix n Mn gn
    (fun i => (∑ j : Fin n, Anw i j * gn j) - w i)
    C hMn hC hn
  let dw : Fin n → ℝ :=
    fun i => w i - ∑ j : Fin n, Ane i j * gs j
  have hdw : ∀ i,
      |dw i| ≤ γ * ∑ j : Fin n, |Ane i j| * |gs j| := by
    intro i
    have hh := p41_rounded_dot_bound fp n (Ane i) gs hvalid
    simpa only [dw, w, p41RoundedMatVec, abs_mul] using hh
  refine ⟨Ds, Dn, dw, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hDs i j
  · intro i j
    exact hDn i j
  · exact hdw
  · intro i
    constructor
    · exact hDse i
    · calc
        (∑ j : Fin n, Anw i j * gn j) -
            (∑ j : Fin n, Ane i j * gs j) =
          ((∑ j : Fin n, Anw i j * gn j) - w i) + dw i := by
            dsimp [dw]
            ring
        _ = dw i - ∑ j : Fin n, Dn i j * gn j := by
          rw [hDne i]
          ring

end VSCLReuse

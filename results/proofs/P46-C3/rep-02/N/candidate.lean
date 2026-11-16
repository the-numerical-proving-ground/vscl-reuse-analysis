import VSCLReuse.P46.Definitions

namespace VSCLReuse

open scoped BigOperators

private theorem p46_gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u k) : 0 ≤ p46Gamma u k := by
  unfold p46Gamma P46GammaValid at *
  have ha : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hb : 0 < 1 - (k : ℝ) * u := by linarith
  exact div_nonneg ha hb.le

private theorem p46_gamma_step_algebra (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b < 1) :
    (a / (1 - a) + b) / (1 - b) ≤ (a + b) / (1 - a - b) := by
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hab1 : 0 < 1 - a - b := by linarith
  apply (div_le_div_iff₀ hb1 hab1).2
  have heq : a / (1 - a) + b = (a + b - a * b) / (1 - a) := by
    field_simp
    ring
  rw [heq]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ ha1).2
  nlinarith [mul_nonneg ha hb]

private theorem p46_gamma_step (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u (k + 1)) :
    (p46Gamma u k + u) / (1 - u) ≤ p46Gamma u (k + 1) := by
  unfold p46Gamma P46GammaValid at *
  have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hsum : (k : ℝ) * u + u < 1 := by
    convert hk using 1 <;> push_cast <;> ring
  have h := p46_gamma_step_algebra ((k : ℝ) * u) u hku hu hsum
  simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hk ⊢
  convert h using 1 <;> congr 1 <;> ring

private theorem p46_gamma_mono (u : ℝ) (k n : ℕ) (hu : 0 ≤ u)
    (hkn : k ≤ n) (hn : P46GammaValid u n) :
    p46Gamma u k ≤ p46Gamma u n := by
  unfold p46Gamma P46GammaValid at *
  have hab : (k : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hu
  have ha : 0 < 1 - (k : ℝ) * u := by linarith
  have hb : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ ha hb).2
  nlinarith

private theorem p46_gamma_valid_le (u : ℝ) (k n : ℕ) (hu : 0 ≤ u)
    (hkn : k ≤ n) (hn : P46GammaValid u n) : P46GammaValid u k := by
  unfold P46GammaValid at *
  have hab : (k : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) hu
  linarith

private theorem p46_gamma_step_strong (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : P46GammaValid u (k + 1)) :
    p46Gamma u k * (1 + p46Gamma u 1) + p46Gamma u 1 ≤
      p46Gamma u (k + 1) := by
  have hu1 : 0 < 1 - u := by
    have h := p46_gamma_valid_le u 1 (k + 1) hu (by omega) hk
    simpa [P46GammaValid] using h
  have heq : p46Gamma u k * (1 + p46Gamma u 1) + p46Gamma u 1 =
      (p46Gamma u k + u) / (1 - u) := by
    simp only [p46Gamma, Nat.cast_one, one_mul]
    field_simp
    ring
  rw [heq]
  exact p46_gamma_step u k hu hk

private theorem p46_relative_reverse (u x y δ : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) (hδ : |δ| ≤ u) (hy : y = x * (1 + δ)) :
    |x - y| ≤ p46Gamma u 1 * |y| := by
  have hδlower : -u ≤ δ := by have h := (abs_le.mp hδ).1; linarith
  have hfactor : 0 < 1 + δ := by linarith
  have hfaclow : 0 ≤ 1 - u := by linarith
  have hxy : |x - y| ≤ u * |x| := by
    rw [hy]
    have heq : x - x * (1 + δ) = -(x * δ) := by ring
    rw [heq, abs_neg, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg x)
  have hybound : |x| * (1 - u) ≤ |y| := by
    rw [hy, abs_mul, abs_of_pos hfactor]
    exact mul_le_mul_of_nonneg_left (by linarith : 1 - u ≤ 1 + δ) (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hybound hu
  simp only [p46Gamma, Nat.cast_one, one_mul]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
  nlinarith

private theorem p46_mul_error (fp : P46FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, hmul⟩ := fp.model_mul a b
  rw [hmul]
  have heq : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [heq, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private theorem p46_sub_mul_step (fp : P46TriFPModel) (r a b : ℝ)
    (hu1 : fp.u < 1) :
    |r - (fp.fl_sub r (fp.fl_mul a b) + a * b)| ≤
      p46Gamma fp.u 1 * |fp.fl_sub r (fp.fl_mul a b)| +
        fp.u * |a * b| := by
  let v := fp.fl_mul a b
  let s := fp.fl_sub r v
  obtain ⟨δ, hδ, hs⟩ := fp.model_sub r v
  have hrel := p46_relative_reverse fp.u (r - v) s δ fp.u_nonneg hu1 hδ hs
  have hmul := p46_mul_error fp.toP46FPModel a b
  have heq : r - (s + a * b) = (r - v - s) + (v - a * b) := by ring
  rw [heq]
  calc
    |(r - v - s) + (v - a * b)| ≤ |r - v - s| + |v - a * b| := abs_add_le _ _
    _ ≤ p46Gamma fp.u 1 * |s| + fp.u * |a * b| := add_le_add hrel hmul

private theorem p46_gamma_one_ge_u (u : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) : u ≤ p46Gamma u 1 := by
  simp only [p46Gamma, Nat.cast_one, one_mul]
  apply (le_div_iff₀ (by linarith : 0 < 1 - u)).2
  nlinarith

private theorem p46_fold_step_bound (u r s t P W b : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : P46GammaValid u (k + 1)) (hW : 0 ≤ W)
    (hold : |r + P - b| ≤ p46Gamma u k * (|r| + W))
    (hstep : |r - (s + t)| ≤ p46Gamma u 1 * |s| + u * |t|) :
    |s + (P + t) - b| ≤
      p46Gamma u (k + 1) * (|s| + (W + |t|)) := by
  let g := p46Gamma u k
  let e := p46Gamma u 1
  let G := p46Gamma u (k + 1)
  have hk' := p46_gamma_valid_le u k (k + 1) hu (by omega) hk
  have hg : 0 ≤ g := p46_gamma_nonneg u k hu hk'
  have hge : g ≤ G := p46_gamma_mono u k (k + 1) hu (by omega) hk
  have he : u ≤ e := p46_gamma_one_ge_u u hu (by
    have h := p46_gamma_valid_le u 1 (k + 1) hu (by omega) hk
    simpa [P46GammaValid] using h)
  have hG : g * (1 + e) + e ≤ G := p46_gamma_step_strong u k hu hk
  have hGt : g * (1 + u) + u ≤ G := by nlinarith [mul_nonneg hg (sub_nonneg.mpr he)]
  have hr : |r| ≤ |s| + |t| + |r - (s + t)| := by
    have h := abs_add_le (r - (s + t)) (s + t)
    have hst := abs_add_le s t
    have heq : r - (s + t) + (s + t) = r := by ring
    rw [heq] at h
    linarith
  have htop : |s + (P + t) - b| ≤ |r + P - b| + |r - (s + t)| := by
    have h := abs_add_le (r + P - b) (-(r - (s + t)))
    have heq : (r + P - b) + -(r - (s + t)) = s + (P + t) - b := by ring
    rw [heq, abs_neg] at h
    exact h
  have hbound : |r| ≤ (1 + e) * |s| + (1 + u) * |t| := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hbound W) hg
  have hGs := mul_le_mul_of_nonneg_right hG (abs_nonneg s)
  have hGt' := mul_le_mul_of_nonneg_right hGt (abs_nonneg t)
  have hGw := mul_le_mul_of_nonneg_right hge hW
  calc
    |s + (P + t) - b| ≤ g * (|r| + W) + (e * |s| + u * |t|) := by linarith
    _ ≤ (g * (1 + e) + e) * |s| + g * W + (g * (1 + u) + u) * |t| := by
      nlinarith
    _ ≤ G * (|s| + (W + |t|)) := by nlinarith

private theorem p46_sub_fold_bound (fp : P46TriFPModel) (count : ℕ)
    (a x : Fin count → ℝ) (b : ℝ)
    (hvalid : P46GammaValid fp.u count) :
    let s := Fin.foldl count (fun r j => fp.fl_sub r (fp.fl_mul (a j) (x j))) b
    |s + (∑ j : Fin count, a j * x j) - b| ≤
      p46Gamma fp.u count * (|s| + ∑ j : Fin count, |a j * x j|) := by
  induction count generalizing b with
  | zero =>
      simp [Fin.foldl_zero, p46Gamma]
  | succ k ih =>
      let a' : Fin k → ℝ := fun j => a j.castSucc
      let x' : Fin k → ℝ := fun j => x j.castSucc
      let r := Fin.foldl k (fun z j => fp.fl_sub z (fp.fl_mul (a' j) (x' j))) b
      let t := a (Fin.last k) * x (Fin.last k)
      let s := fp.fl_sub r (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      have hvk := p46_gamma_valid_le fp.u k (k + 1) fp.u_nonneg (by omega) hvalid
      have hi := ih a' x' b hvk
      have hs := p46_sub_mul_step fp r (a (Fin.last k)) (x (Fin.last k)) (by
        have hv1 := p46_gamma_valid_le fp.u 1 (k + 1) fp.u_nonneg (by omega) hvalid
        simpa [P46GammaValid] using hv1)
      have hw : 0 ≤ ∑ j : Fin k, |a' j * x' j| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have h := p46_fold_step_bound fp.u r s t
        (∑ j : Fin k, a' j * x' j) (∑ j : Fin k, |a' j * x' j|) b k
        fp.u_nonneg hvalid hw hi hs
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc] using h

private theorem p46_div_error_reverse (fp : P46TriFPModel) (s d : ℝ)
    (hd : d ≠ 0) (hu1 : fp.u < 1) :
    |s - d * fp.fl_div s d| ≤
      p46Gamma fp.u 1 * |d * fp.fl_div s d| := by
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s d hd
  have hy : d * fp.fl_div s d = s * (1 + δ) := by
    rw [hdiv]
    field_simp
  exact p46_relative_reverse fp.u s (d * fp.fl_div s d) δ
    fp.u_nonneg hu1 hδ hy

private theorem p46_fold_div_bound (fp : P46TriFPModel) (count : ℕ)
    (a x : Fin count → ℝ) (b d : ℝ) (hd : d ≠ 0)
    (hvalid : P46GammaValid fp.u (count + 1)) :
    let s := Fin.foldl count (fun r j => fp.fl_sub r (fp.fl_mul (a j) (x j))) b
    let z := fp.fl_div s d
    |d * z + (∑ j : Fin count, a j * x j) - b| ≤
      p46Gamma fp.u (count + 1) *
        (|d * z| + ∑ j : Fin count, |a j * x j|) := by
  let s := Fin.foldl count (fun r j => fp.fl_sub r (fp.fl_mul (a j) (x j))) b
  let z := fp.fl_div s d
  let P := ∑ j : Fin count, a j * x j
  let W := ∑ j : Fin count, |a j * x j|
  let g := p46Gamma fp.u count
  let e := p46Gamma fp.u 1
  let G := p46Gamma fp.u (count + 1)
  have hvk := p46_gamma_valid_le fp.u count (count + 1) fp.u_nonneg (by omega) hvalid
  have hold : |s + P - b| ≤ g * (|s| + W) :=
    p46_sub_fold_bound fp count a x b hvk
  have hu1 : fp.u < 1 := by
    have hv1 := p46_gamma_valid_le fp.u 1 (count + 1) fp.u_nonneg (by omega) hvalid
    simpa [P46GammaValid] using hv1
  have hdiv : |s - d * z| ≤ e * |d * z| := p46_div_error_reverse fp s d hd hu1
  have hs : |s| ≤ (1 + e) * |d * z| := by
    have ht := abs_add_le (s - d * z) (d * z)
    have heq : s - d * z + d * z = s := by ring
    rw [heq] at ht
    nlinarith
  have hg : 0 ≤ g := p46_gamma_nonneg fp.u count fp.u_nonneg hvk
  have hge : g ≤ G := p46_gamma_mono fp.u count (count + 1) fp.u_nonneg (by omega) hvalid
  have hG : g * (1 + e) + e ≤ G := p46_gamma_step_strong fp.u count fp.u_nonneg hvalid
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have htop : |d * z + P - b| ≤ |s + P - b| + |s - d * z| := by
    have ht := abs_add_le (s + P - b) (-(s - d * z))
    have heq : s + P - b + -(s - d * z) = d * z + P - b := by ring
    rw [heq, abs_neg] at ht
    exact ht
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hs W) hg
  have hGs := mul_le_mul_of_nonneg_right hG (abs_nonneg (d * z))
  have hGw := mul_le_mul_of_nonneg_right hge hW
  calc
    |d * z + P - b| ≤ g * (|s| + W) + e * |d * z| := by linarith
    _ ≤ (g * (1 + e) + e) * |d * z| + g * W := by nlinarith
    _ ≤ G * (|d * z| + W) := by nlinarith

private theorem p46_upper_row_sum {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ := by
  let count := n - i.val - 1
  let g : ℕ → ℝ := fun q => if h : q < n then f ⟨q, h⟩ else 0
  have hn : n = i.val + 1 + count := by dsimp [count]; omega
  have hlow : (∑ q ∈ Finset.range i.val, g q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : q < i.val := Finset.mem_range.mp hq
    have hqn : q < n := by omega
    simp only [g, dif_pos hqn]
    exact hzero ⟨q, hqn⟩ hq'
  have hdiag : g i.val = f i := by
    simp only [g, dif_pos i.isLt]
  have htail : (∑ q ∈ Finset.range count, g (i.val + 1 + q)) =
      ∑ t : Fin count, f ⟨i.val + 1 + t.val, by omega⟩ := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro q hq
    have hqc : q < count := Finset.mem_range.mp hq
    have hqn : i.val + 1 + q < n := by omega
    simp only [g, dif_pos hqn, dif_pos hqc]
  calc
    (∑ j : Fin n, f j) = ∑ q ∈ Finset.range n, g q := by
      exact Finset.sum_fin_eq_sum_range f
    _ = f i + ∑ q ∈ Finset.range count, g (i.val + 1 + q) := by
      conv_lhs => rw [hn]
      rw [Finset.sum_range_add, Finset.sum_range_succ, hlow]
      simp only [zero_add, hdiag]
    _ = _ := by rw [htail]

private theorem p46_local_backsub_row (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hvalid : P46GammaValid fp.u n)
    (hdiag : U i i ≠ 0)
    (hupper : ∀ j : Fin n, j.val < i.val → U i j = 0) :
    let count := n - i.val - 1
    let s := Fin.foldl count
      (fun acc (t : Fin count) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩))) (b i)
    let x' := Function.update x i (fp.fl_div s (U i i))
    |(∑ j : Fin n, U i j * x' j) - b i| ≤
      p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |x' j| := by
  let count := n - i.val - 1
  let a : Fin count → ℝ := fun t => U i ⟨i.val + 1 + t.val, by omega⟩
  let y : Fin count → ℝ := fun t => x ⟨i.val + 1 + t.val, by omega⟩
  let s := Fin.foldl count (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (y t))) (b i)
  let z := fp.fl_div s (U i i)
  let x' := Function.update x i z
  have hcount : count + 1 ≤ n := by dsimp [count]; omega
  have hv := p46_gamma_valid_le fp.u (count + 1) n fp.u_nonneg hcount hvalid
  have hfold := p46_fold_div_bound fp count a y (b i) (U i i) hdiag hv
  have hneq (t : Fin count) : (⟨i.val + 1 + t.val, by omega⟩ : Fin n) ≠ i := by
    intro heq
    have hh := congrArg Fin.val heq
    dsimp at hh
    omega
  have htail (t : Fin count) : x' ⟨i.val + 1 + t.val, by omega⟩ = y t := by
    exact Function.update_of_ne (hneq t) z x
  have hdiag' : x' i = z := Function.update_self i z x
  have hsum : (∑ j : Fin n, U i j * x' j) =
      U i i * z + ∑ t : Fin count, a t * y t := by
    have hh := p46_upper_row_sum i (fun j => U i j * x' j) (by
      intro j hj
      simpa only [hupper j hj, zero_mul])
    simpa only [hdiag', htail] using hh
  have hsumabs : (∑ j : Fin n, |U i j| * |x' j|) =
      |U i i * z| + ∑ t : Fin count, |a t * y t| := by
    have hh := p46_upper_row_sum i (fun j => |U i j * x' j|) (by
      intro j hj
      simp only [hupper j hj, zero_mul, abs_zero])
    simpa only [abs_mul, hdiag', htail] using hh
  have hgm := p46_gamma_mono fp.u (count + 1) n fp.u_nonneg hcount hvalid
  have hnonneg : 0 ≤ |U i i * z| + ∑ t : Fin count, |a t * y t| := by
    positivity
  change |(∑ j : Fin n, U i j * x' j) - b i| ≤
    p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |x' j|
  rw [hsum, hsumabs]
  exact le_trans hfold (mul_le_mul_of_nonneg_right hgm hnonneg)

private def p46RowBound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |(∑ j : Fin n, U i j * x j) - b i| ≤
    p46Gamma fp.u n * ∑ j : Fin n, |U i j| * |x j|

private theorem p46_row_bound_update (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b x : Fin n → ℝ)
    (i k : Fin n) (z : ℝ) (hzero : U i k = 0)
    (hold : p46RowBound fp n U b x i) :
    p46RowBound fp n U b (Function.update x k z) i := by
  have hsum : (∑ j : Fin n, U i j * Function.update x k z j) =
      ∑ j : Fin n, U i j * x j := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases heq : j = k
    · subst j
      simp [hzero]
    · simp [Function.update_of_ne heq]
  have hsumabs : (∑ j : Fin n, |U i j| * |Function.update x k z j|) =
      ∑ j : Fin n, |U i j| * |x j| := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases heq : j = k
    · subst j
      simp [hzero]
    · simp [Function.update_of_ne heq]
  unfold p46RowBound at *
  simpa only [hsum, hsumabs] using hold

private theorem p46_backsub_steps_bound (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hvalid : P46GammaValid fp.u n)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hinv : ∀ i : Fin n, k ≤ i.val → p46RowBound fp n U b x i) :
    ∀ i : Fin n, p46RowBound fp n U b (p46BackSubSteps fp n U b k hk x) i := by
  induction k generalizing x with
  | zero =>
      intro i
      simpa only [p46BackSubSteps] using hinv i (Nat.zero_le _)
  | succ k ih =>
      let ik : Fin n := ⟨k, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' := Function.update x ik (fp.fl_div s (U ik ik))
      have hinv' : ∀ i : Fin n, k ≤ i.val → p46RowBound fp n U b x' i := by
        intro i hi
        by_cases heq : i = ik
        · subst i
          exact p46_local_backsub_row fp n U b x ik hvalid (hdiag ik) (hupper ik)
        · have hgt : k < i.val := by
            have hne : i.val ≠ k := by
              intro h
              apply heq
              exact Fin.ext h
            omega
          have hold := hinv i (by omega)
          exact p46_row_bound_update fp n U b x i ik (fp.fl_div s (U ik ik))
            (hupper i ik (by omega)) hold
      intro i
      have hrec := ih (Nat.le_of_succ_le hk) x' hinv' i
      simpa only [p46BackSubSteps, count, s, x'] using hrec

private theorem p46_simulated_backsub_residual (fp : P46TriFPModel) (n : ℕ)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hvalid : P46GammaValid fp.u n)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    ∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j| := by
  let xh := p46BackSub fp n U b
  let xl := p46SimulatedBackSub fp n U b
  have hhigh : ∀ i : Fin n, p46RowBound fp n U b xh i := by
    intro i
    exact p46_backsub_steps_bound fp n U b hvalid hdiag hupper n (le_refl n)
      (fun _ => 0) (by intro j hj; have := j.isLt; omega) i
  have hround (j : Fin n) : |xl j - xh j| ≤ fp.u_low * |xh j| :=
    fp.model_low (xh j)
  intro i
  let W := ∑ j : Fin n, |U i j| * |xh j|
  have hW : 0 ≤ W := Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hdiff :
      |(∑ j : Fin n, U i j * xl j) - (∑ j : Fin n, U i j * xh j)| ≤
        fp.u_low * W := by
    have heq : (∑ j : Fin n, U i j * xl j) - (∑ j : Fin n, U i j * xh j) =
        ∑ j : Fin n, U i j * (xl j - xh j) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      ext j
      ring
    rw [heq]
    calc
      |∑ j : Fin n, U i j * (xl j - xh j)| ≤
          ∑ j : Fin n, |U i j * (xl j - xh j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, fp.u_low * (|U i j| * |xh j|) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        calc
          |U i j| * |xl j - xh j| ≤ |U i j| * (fp.u_low * |xh j|) :=
            mul_le_mul_of_nonneg_left (hround j) (abs_nonneg _)
          _ = fp.u_low * (|U i j| * |xh j|) := by ring
      _ = fp.u_low * W := by rw [Finset.mul_sum]
  have htri :
      |(∑ j : Fin n, U i j * xl j) - b i| ≤
        |(∑ j : Fin n, U i j * xl j) - (∑ j : Fin n, U i j * xh j)| +
        |(∑ j : Fin n, U i j * xh j) - b i| := by
    have ht := abs_add_le
      ((∑ j : Fin n, U i j * xl j) - (∑ j : Fin n, U i j * xh j))
      ((∑ j : Fin n, U i j * xh j) - b i)
    convert ht using 1 <;> ring
  have hh := hhigh i
  unfold p46RowBound at hh
  change |(∑ j : Fin n, U i j * xl j) - b i| ≤
    (p46Gamma fp.u n + fp.u_low) * W
  nlinarith

private theorem p46_add_error (fp : P46FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  rw [hadd]
  have heq : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [heq, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private theorem p46_add_mul_step (fp : P46FPModel) (r a b : ℝ) :
    |fp.fl_add r (fp.fl_mul a b) - (r + a * b)| ≤
      fp.u * |r| + (2 * fp.u + fp.u ^ 2) * |a * b| := by
  let t := a * b
  let v := fp.fl_mul a b
  let s := fp.fl_add r v
  have hmul : |v - t| ≤ fp.u * |t| := p46_mul_error fp a b
  have hadd : |s - (r + v)| ≤ fp.u * |r + v| := p46_add_error fp r v
  have hv : |v| ≤ (1 + fp.u) * |t| := by
    have ht := abs_add_le (v - t) t
    have heq : v - t + t = v := by ring
    rw [heq] at ht
    nlinarith
  have hrv : |r + v| ≤ |r| + (1 + fp.u) * |t| := by
    have ht := abs_add_le r v
    linarith
  have hrv' := mul_le_mul_of_nonneg_left hrv fp.u_nonneg
  have htop : |s - (r + t)| ≤ |s - (r + v)| + |v - t| := by
    have ht := abs_add_le (s - (r + v)) (v - t)
    have heq : s - (r + v) + (v - t) = s - (r + t) := by ring
    rw [heq] at ht
    exact ht
  nlinarith

private theorem p46_gamma_two_ge (u : ℝ) (hu : 0 ≤ u)
    (hvalid : P46GammaValid u 2) :
    2 * u + u ^ 2 ≤ p46Gamma u 2 := by
  have hu2 : 0 < 1 - 2 * u := by
    norm_num [P46GammaValid] at hvalid
    linarith
  simp only [p46Gamma, Nat.cast_ofNat]
  apply (le_div_iff₀ hu2).2
  nlinarith [sq_nonneg u, mul_nonneg hu (sq_nonneg u)]

private theorem p46_dot_fold_step (u r s t S W : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hk : 1 ≤ k) (hvalid : P46GammaValid u (k + 1))
    (hW : 0 ≤ W) (hSW : |S| ≤ W)
    (hold : |r - S| ≤ p46Gamma u k * W)
    (hstep : |s - (r + t)| ≤ u * |r| + (2 * u + u ^ 2) * |t|) :
    |s - (S + t)| ≤ p46Gamma u (k + 1) * (W + |t|) := by
  let g := p46Gamma u k
  let G := p46Gamma u (k + 1)
  have hvalidk := p46_gamma_valid_le u k (k + 1) hu (by omega) hvalid
  have hg : 0 ≤ g := p46_gamma_nonneg u k hu hvalidk
  have hge : g * (1 + u) + u ≤ G := by
    have hu1 : u < 1 := by
      have hv1 := p46_gamma_valid_le u 1 (k + 1) hu (by omega) hvalid
      simpa [P46GammaValid] using hv1
    have he := p46_gamma_one_ge_u u hu hu1
    have hs := p46_gamma_step_strong u k hu hvalid
    nlinarith [mul_nonneg hg (sub_nonneg.mpr he)]
  have hv2 := p46_gamma_valid_le u 2 (k + 1) hu (by omega) hvalid
  have hterm : 2 * u + u ^ 2 ≤ G :=
    le_trans (p46_gamma_two_ge u hu hv2)
      (p46_gamma_mono u 2 (k + 1) hu (by omega) hvalid)
  have hr : |r| ≤ (1 + g) * W := by
    have ht := abs_add_le (r - S) S
    have heq : r - S + S = r := by ring
    rw [heq] at ht
    nlinarith
  have htop : |s - (S + t)| ≤ |s - (r + t)| + |r - S| := by
    have ht := abs_add_le (s - (r + t)) (r - S)
    have heq : s - (r + t) + (r - S) = s - (S + t) := by ring
    rw [heq] at ht
    exact ht
  have hru := mul_le_mul_of_nonneg_left hr hu
  have hGW := mul_le_mul_of_nonneg_right hge hW
  have hGt := mul_le_mul_of_nonneg_right hterm (abs_nonneg t)
  nlinarith

private theorem p46_dot_tail_bound (fp : P46FPModel) (count : ℕ)
    (a b : Fin count → ℝ) (r₀ S₀ W₀ : ℝ)
    (hW₀ : 0 ≤ W₀) (hS₀ : |S₀| ≤ W₀)
    (hbase : |r₀ - S₀| ≤ p46Gamma fp.u 1 * W₀)
    (hvalid : P46GammaValid fp.u (count + 1)) :
    let r := Fin.foldl count (fun acc j => fp.fl_add acc (fp.fl_mul (a j) (b j))) r₀
    |r - (S₀ + ∑ j : Fin count, a j * b j)| ≤
      p46Gamma fp.u (count + 1) *
        (W₀ + ∑ j : Fin count, |a j * b j|) := by
  induction count with
  | zero => simpa [Fin.foldl_zero] using hbase
  | succ k ih =>
      let a' : Fin k → ℝ := fun j => a j.castSucc
      let b' : Fin k → ℝ := fun j => b j.castSucc
      let r := Fin.foldl k (fun acc j => fp.fl_add acc (fp.fl_mul (a' j) (b' j))) r₀
      let S := S₀ + ∑ j : Fin k, a' j * b' j
      let W := W₀ + ∑ j : Fin k, |a' j * b' j|
      let t := a (Fin.last k) * b (Fin.last k)
      let s := fp.fl_add r (fp.fl_mul (a (Fin.last k)) (b (Fin.last k)))
      have hvk := p46_gamma_valid_le fp.u (k + 1) (k + 2)
        fp.u_nonneg (by omega) (by simpa only [Nat.add_assoc] using hvalid)
      have hprev := ih a' b' hvk
      have hW : 0 ≤ W := add_nonneg hW₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      have hsum : |∑ j : Fin k, a' j * b' j| ≤ ∑ j : Fin k, |a' j * b' j| :=
        Finset.abs_sum_le_sum_abs _ _
      have hSW : |S| ≤ W := by
        have ht := abs_add_le S₀ (∑ j : Fin k, a' j * b' j)
        linarith
      have hstep := p46_add_mul_step fp r (a (Fin.last k)) (b (Fin.last k))
      have h := p46_dot_fold_step fp.u r s t S W (k + 1) fp.u_nonneg
        (by omega) (by simpa only [Nat.add_assoc] using hvalid)
        hW hSW hprev hstep
      simpa only [S, W, s, t, r, a', b', Fin.foldl_succ_last,
        Fin.sum_univ_castSucc, add_assoc] using h

private theorem p46_rounded_dot_bound (fp : P46FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hvalid : P46GammaValid fp.u n) :
    |p46RoundedDotProduct fp n x y - ∑ j : Fin n, x j * y j| ≤
      p46Gamma fp.u n * ∑ j : Fin n, |x j * y j| := by
  cases n with
  | zero => simp [p46RoundedDotProduct]
  | succ k =>
      let a : Fin k → ℝ := fun j => x j.succ
      let b : Fin k → ℝ := fun j => y j.succ
      let t₀ := x 0 * y 0
      let r₀ := fp.fl_mul (x 0) (y 0)
      have hv1 := p46_gamma_valid_le fp.u 1 (k + 1) fp.u_nonneg (by omega) hvalid
      have hge : fp.u ≤ p46Gamma fp.u 1 :=
        p46_gamma_one_ge_u fp.u fp.u_nonneg (by simpa [P46GammaValid] using hv1)
      have hbase : |r₀ - t₀| ≤ p46Gamma fp.u 1 * |t₀| :=
        le_trans (p46_mul_error fp (x 0) (y 0))
          (mul_le_mul_of_nonneg_right hge (abs_nonneg _))
      have ht := p46_dot_tail_bound fp k a b r₀ t₀ |t₀|
        (abs_nonneg _) (le_refl _) hbase hvalid
      simpa only [p46RoundedDotProduct, Fin.sum_univ_succ, a, b, t₀, r₀,
        add_comm, add_left_comm, add_assoc] using ht

private theorem p46_gamma_size (u u_low : ℝ) (n : ℕ)
    (hu : 0 < u) (hlow : 0 ≤ u_low)
    (hvalid : P46GammaValid u n)
    (hsize : (n : ℝ) ≤ u_low / (u * (1 + 2 * u_low))) :
    p46Gamma u n * (1 + u_low) ≤ u_low := by
  have hdenom : 0 < u * (1 + 2 * u_low) :=
    mul_pos hu (by linarith)
  have hsize' := (le_div_iff₀ hdenom).mp hsize
  have hx : (n : ℝ) * u * (1 + 2 * u_low) ≤ u_low := by
    nlinarith [hsize']
  have hvalid' : 0 < 1 - (n : ℝ) * u := by
    unfold P46GammaValid at hvalid
    linarith
  simp only [p46Gamma]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hvalid').2
  nlinarith

private theorem p46_simulated_matmul_entry (fp : P46FPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (hu : 0 < fp.u) (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (i : Fin m) (j : Fin p) :
    |p46SimulatedMatMul fp A B i j - p46MatMul A B i j| ≤
      2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j := by
  let exact := ∑ k : Fin n, A i k * B k j
  let high := p46RoundedDotProduct fp n (A i) (fun k => B k j)
  let low := fp.fl_low high
  let W := ∑ k : Fin n, |A i k * B k j|
  let g := p46Gamma fp.u n
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hexact : |exact| ≤ W := Finset.abs_sum_le_sum_abs _ _
  have hhigh : |high - exact| ≤ g * W :=
    p46_rounded_dot_bound fp n (A i) (fun k => B k j) hvalid
  have hlow : |low - high| ≤ fp.u_low * |high| := fp.model_low high
  have hhighabs : |high| ≤ (1 + g) * W := by
    have ht := abs_add_le (high - exact) exact
    have heq : high - exact + exact = high := by ring
    rw [heq] at ht
    nlinarith
  have hsize' := p46_gamma_size fp.u fp.u_low n hu fp.u_low_nonneg hvalid hsize
  have hcoef : fp.u_low * (1 + g) + g ≤ 2 * fp.u_low := by nlinarith
  have hcoefW := mul_le_mul_of_nonneg_right hcoef hW
  have hlowhigh := mul_le_mul_of_nonneg_left hhighabs fp.u_low_nonneg
  have htri : |low - exact| ≤ |low - high| + |high - exact| := by
    have ht := abs_add_le (low - high) (high - exact)
    have heq : low - high + (high - exact) = low - exact := by ring
    rw [heq] at ht
    exact ht
  have hfinal : |low - exact| ≤ 2 * fp.u_low * W := by nlinarith
  simpa only [low, high, exact, W, p46SimulatedMatMul, p46RoundedMatMul, p46MatMul,
    p46AbsMatrix, abs_mul] using hfinal

/-- Section 3.2: high-precision kernels rounded once to low precision. -/
theorem p46_c3_simulated_product_and_triangular_solve
    (fp : P46TriFPModel) (m n p : ℕ)
    (A : P46Matrix m n) (B : P46Matrix n p)
    (U : P46Matrix n n) (b : Fin n → ℝ)
    (hu : 0 < fp.u)
    (hvalid : P46GammaValid fp.u n)
    (hsize : (n : ℝ) ≤ fp.u_low / (fp.u * (1 + 2 * fp.u_low)))
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hUupper : ∀ i j : Fin n, j.val < i.val → U i j = 0) :
    (∀ i j,
      |p46SimulatedMatMul fp.toP46FPModel A B i j - p46MatMul A B i j| ≤
        2 * fp.u_low * p46MatMul (p46AbsMatrix A) (p46AbsMatrix B) i j) ∧
    (∀ i : Fin n,
      |(∑ j : Fin n, U i j * p46SimulatedBackSub fp n U b j) - b i| ≤
        (p46Gamma fp.u n + fp.u_low) *
          ∑ j : Fin n, |U i j| * |p46BackSub fp n U b j|) := by
  -- PROOF_START P46-C3-H001
  constructor
  · intro i j
    exact p46_simulated_matmul_entry fp.toP46FPModel m n p A B hu hvalid hsize i j
  · exact p46_simulated_backsub_residual fp n U b hvalid hUdiag hUupper

end VSCLReuse

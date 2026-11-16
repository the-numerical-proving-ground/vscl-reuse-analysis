import VSCLReuse.P38.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p38_gamma_nonneg (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u m) : 0 ≤ p38Gamma u m := by
  unfold p38Gamma P38GammaValid at *
  have hden : 0 < 1 - (m : ℝ) * u := by linarith
  positivity

private lemma p38_gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) :
    p38Gamma u m * (1 + u) + u ≤ p38Gamma u (m + 1) := by
  have hm' : P38GammaValid u m := by
    unfold P38GammaValid at *
    push_cast at hm
    nlinarith
  unfold p38Gamma P38GammaValid at *
  push_cast at *
  have hden : 0 < 1 - (m : ℝ) * u := by linarith
  have hden' : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  calc
    (m : ℝ) * u / (1 - (m : ℝ) * u) * (1 + u) + u =
        ((m : ℝ) + 1) * u / (1 - (m : ℝ) * u) := by
          field_simp
          ring
    _ ≤ ((m : ℝ) + 1) * u / (1 - ((m : ℝ) + 1) * u) := by
      apply (div_le_div_iff₀ hden hden').2
      have hnum : 0 ≤ ((m : ℝ) + 1) * u := by positivity
      nlinarith [mul_nonneg hnum hu]

private lemma p38_gamma_step_div (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) :
    (p38Gamma u m + u) / (1 - u) ≤ p38Gamma u (m + 1) := by
  have hm' : P38GammaValid u m := by
    unfold P38GammaValid at *
    push_cast at hm
    nlinarith
  unfold p38Gamma P38GammaValid at *
  push_cast at *
  have hden : 0 < 1 - (m : ℝ) * u := by linarith
  have hden' : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  have hu1 : 0 < 1 - u := by nlinarith
  calc
    ((m : ℝ) * u / (1 - (m : ℝ) * u) + u) / (1 - u) =
        (((m : ℝ) + 1) * u - (m : ℝ) * u ^ 2) /
          ((1 - (m : ℝ) * u) * (1 - u)) := by
            field_simp
            ring
    _ ≤ ((m : ℝ) + 1) * u / (1 - ((m : ℝ) + 1) * u) := by
      apply (div_le_div_iff₀ (mul_pos hden hu1) hden').2
      have hm0 : 0 ≤ (m : ℝ) := by positivity
      nlinarith [mul_nonneg hm0 (sq_nonneg u)]

private lemma p38_gamma_mono (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) :
    p38Gamma u m ≤ p38Gamma u (m + 1) := by
  have hm' : P38GammaValid u m := by
    unfold P38GammaValid at *
    push_cast at hm
    nlinarith
  have hnonneg := p38_gamma_nonneg u m hu hm'
  have hstep := p38_gamma_step u m hu hm
  nlinarith

private lemma p38_gamma_two (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hm : P38GammaValid u (m + 1)) (hpos : 1 ≤ m) :
    2 * u + u ^ 2 ≤ p38Gamma u (m + 1) := by
  unfold p38Gamma P38GammaValid at *
  push_cast at *
  have hden : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hpos
  apply (le_div_iff₀ hden).2
  have ha : 0 ≤ (((m : ℝ) + 1) - 2) * u := by
    apply mul_nonneg <;> nlinarith
  have hb : 0 ≤ (2 * ((m : ℝ) + 1) - 1) * u ^ 2 := by
    apply mul_nonneg
    · linarith
    · positivity
  have hc : 0 ≤ ((m : ℝ) + 1) * u ^ 3 := by positivity
  nlinarith

private lemma p38_gamma_valid_le (u : ℝ) (m n : ℕ) (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : P38GammaValid u n) : P38GammaValid u m := by
  unfold P38GammaValid at *
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith

private lemma p38_gamma_le (u : ℝ) (m n : ℕ) (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : P38GammaValid u n) :
    p38Gamma u m ≤ p38Gamma u n := by
  have hm := p38_gamma_valid_le u m n hu hmn hn
  unfold p38Gamma P38GammaValid at *
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hdenm : 0 < 1 - (m : ℝ) * u := by linarith
  have hdenn : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hdenm hdenn).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hmn') hu]

private lemma p38_mul_error (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_mul a b - a * b| ≤ fp.u * |a * b| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul a b
  rw [heq]
  have hident : (a * b) * (1 + δ) - a * b = (a * b) * δ := by ring
  rw [hident, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a * b))

private lemma p38_add_error (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add a b
  rw [heq]
  have hident : (a + b) * (1 + δ) - (a + b) = (a + b) * δ := by ring
  rw [hident, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))

private lemma p38_sub_error (fp : P38FPModel) (a b : ℝ) :
    |fp.fl_sub a b - (a - b)| ≤ fp.u * |a - b| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_sub a b
  rw [heq]
  have hident : (a - b) * (1 + δ) - (a - b) = (a - b) * δ := by ring
  rw [hident, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a - b))

private lemma p38_div_error (fp : P38FPModel) (s d : ℝ) (hd : d ≠ 0) :
    |d * fp.fl_div s d - s| ≤ fp.u * |s| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_div s d hd
  rw [heq]
  have hident : d * ((s / d) * (1 + δ)) - s = s * δ := by
    field_simp
    ring
  rw [hident, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg s)

private lemma p38_reverse_error (u a b : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (herr : |a - b| ≤ u * |b|) :
    |b| ≤ |a| / (1 - u) ∧ |a - b| ≤ u / (1 - u) * |a| := by
  have htri : |b| ≤ |a - b| + |a| := by
    calc
      |b| = |(b - a) + a| := by ring
      _ ≤ |b - a| + |a| := abs_add_le _ _
      _ = |a - b| + |a| := by rw [abs_sub_comm]
  have hu' : 0 < 1 - u := by linarith
  have hb : |b| ≤ |a| / (1 - u) := by
    apply (le_div_iff₀ hu').2
    nlinarith
  refine ⟨hb, ?_⟩
  calc
    |a - b| ≤ u * |b| := herr
    _ ≤ u * (|a| / (1 - u)) := mul_le_mul_of_nonneg_left hb hu
    _ = u / (1 - u) * |a| := by ring

private lemma p38_sub_step_bound (fp : P38FPModel) (m : ℕ)
    (hm : P38GammaValid fp.u (m + 1))
    (s A W b a x : ℝ) (hW : 0 ≤ W)
    (hold : |s + A - b| ≤ p38Gamma fp.u m * (|s| + W)) :
    |fp.fl_sub s (fp.fl_mul a x) + (A + a * x) - b| ≤
      p38Gamma fp.u (m + 1) *
        (|fp.fl_sub s (fp.fl_mul a x)| + W + |a * x|) := by
  let u := fp.u
  let q := fp.fl_mul a x
  let z := fp.fl_sub s q
  let t := a * x
  have hu : 0 ≤ u := fp.u_nonneg
  have hu1 : u < 1 := by
    have hh : P38GammaValid u 1 :=
      p38_gamma_valid_le u 1 (m + 1) hu (by omega) hm
    simpa [P38GammaValid] using hh
  have hmul : |q - t| ≤ u * |t| := p38_mul_error fp a x
  have hsub : |z - (s - q)| ≤ u * |s - q| := p38_sub_error fp s q
  obtain ⟨hback, hback_err⟩ := p38_reverse_error u z (s - q) hu hu1 hsub
  have hq : |q| ≤ (1 + u) * |t| := by
    calc
      |q| = |(q - t) + t| := by ring
      _ ≤ |q - t| + |t| := abs_add_le _ _
      _ ≤ u * |t| + |t| := add_le_add hmul (le_refl _)
      _ = (1 + u) * |t| := by ring
  have hs : |s| ≤ |z| / (1 - u) + (1 + u) * |t| := by
    calc
      |s| = |(s - q) + q| := by ring
      _ ≤ |s - q| + |q| := abs_add_le _ _
      _ ≤ |z| / (1 - u) + (1 + u) * |t| := add_le_add hback hq
  have hlocal : |(z + (A + t) - b) - (s + A - b)| ≤
      u / (1 - u) * |z| + u * |t| := by
    have hid : (z + (A + t) - b) - (s + A - b) =
        (z - (s - q)) + (t - q) := by ring
    rw [hid]
    calc
      |(z - (s - q)) + (t - q)| ≤ |z - (s - q)| + |t - q| := abs_add_le _ _
      _ ≤ u / (1 - u) * |z| + u * |t| := by
        rw [abs_sub_comm t q]
        exact add_le_add hback_err hmul
  have htri : |z + (A + t) - b| ≤
      |s + A - b| + |(z + (A + t) - b) - (s + A - b)| := by
    have hid : z + (A + t) - b =
        (s + A - b) + ((z + (A + t) - b) - (s + A - b)) := by ring
    calc
      |z + (A + t) - b| =
          |(s + A - b) + ((z + (A + t) - b) - (s + A - b))| := congrArg abs hid
      _ ≤ _ := abs_add_le _ _
  have hg : 0 ≤ p38Gamma u m :=
    p38_gamma_nonneg u m hu (p38_gamma_valid_le u m (m + 1) hu (by omega) hm)
  have hcoef1 := p38_gamma_step_div u m hu hm
  have hcoef2 := p38_gamma_step u m hu hm
  have hcoef3 := p38_gamma_mono u m hu hm
  have hmul1 := mul_le_mul_of_nonneg_right hcoef1 (abs_nonneg z)
  have hmul2 := mul_le_mul_of_nonneg_right hcoef2 (abs_nonneg t)
  have hmul3 := mul_le_mul_of_nonneg_right hcoef3 hW
  have hbound := calc
    |z + (A + t) - b| ≤
        p38Gamma u m * (|s| + W) +
          (u / (1 - u) * |z| + u * |t|) :=
      le_trans htri (add_le_add hold hlocal)
    _ ≤ p38Gamma u m *
          (|z| / (1 - u) + (1 + u) * |t| + W) +
          (u / (1 - u) * |z| + u * |t|) := by
      gcongr
    _ = (p38Gamma u m + u) / (1 - u) * |z| +
          p38Gamma u m * W +
          (p38Gamma u m * (1 + u) + u) * |t| := by ring
    _ ≤ p38Gamma u (m + 1) * (|z| + W + |t|) := by
      nlinarith [hmul1, hmul2, hmul3]
  exact hbound

private noncomputable def p38SubFold (fp : P38FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (b : ℝ) : ℝ :=
  Fin.foldl m (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) b

private lemma p38_sub_fold_bound (fp : P38FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (b : ℝ) (hm : P38GammaValid fp.u m) :
    |p38SubFold fp m a x b + (∑ i : Fin m, a i * x i) - b| ≤
      p38Gamma fp.u m *
        (|p38SubFold fp m a x b| + (∑ i : Fin m, |a i * x i|)) := by
  induction m with
  | zero =>
      simp [p38SubFold, p38Gamma]
  | succ m ih =>
      have hm0 : P38GammaValid fp.u m :=
        p38_gamma_valid_le fp.u m (m + 1) fp.u_nonneg (by omega) hm
      let ap : Fin m → ℝ := fun i => a i.castSucc
      let xp : Fin m → ℝ := fun i => x i.castSucc
      have hi := ih ap xp hm0
      have hW : 0 ≤ ∑ i : Fin m, |ap i * xp i| :=
        Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hstep := p38_sub_step_bound fp m hm
        (p38SubFold fp m ap xp b)
        (∑ i : Fin m, ap i * xp i)
        (∑ i : Fin m, |ap i * xp i|)
        b (a (Fin.last m)) (x (Fin.last m)) hW hi
      simpa only [p38SubFold, Fin.foldl_succ_last, Fin.sum_univ_castSucc,
        ap, xp, Function.comp_def, add_assoc] using hstep

private lemma p38_div_step_bound (fp : P38FPModel) (m : ℕ)
    (hm : P38GammaValid fp.u (m + 1))
    (s A W b d : ℝ) (hW : 0 ≤ W) (hd : d ≠ 0)
    (hold : |s + A - b| ≤ p38Gamma fp.u m * (|s| + W)) :
    |d * fp.fl_div s d + A - b| ≤
      p38Gamma fp.u (m + 1) * (|d * fp.fl_div s d| + W) := by
  let u := fp.u
  let z := d * fp.fl_div s d
  have hu : 0 ≤ u := fp.u_nonneg
  have hu1 : u < 1 := by
    have hh : P38GammaValid u 1 :=
      p38_gamma_valid_le u 1 (m + 1) hu (by omega) hm
    simpa [P38GammaValid] using hh
  have hdiv : |z - s| ≤ u * |s| := p38_div_error fp s d hd
  obtain ⟨hs, herr⟩ := p38_reverse_error u z s hu hu1 hdiv
  have htri : |z + A - b| ≤ |s + A - b| + |z - s| := by
    have hid : z + A - b = (s + A - b) + (z - s) := by ring
    calc
      |z + A - b| = |(s + A - b) + (z - s)| := congrArg abs hid
      _ ≤ _ := abs_add_le _ _
  have hcoef1 := p38_gamma_step_div u m hu hm
  have hcoef2 := p38_gamma_mono u m hu hm
  have hmul1 := mul_le_mul_of_nonneg_right hcoef1 (abs_nonneg z)
  have hmul2 := mul_le_mul_of_nonneg_right hcoef2 hW
  calc
    |z + A - b| ≤
        p38Gamma u m * (|s| + W) + u / (1 - u) * |z| :=
      le_trans htri (add_le_add hold herr)
    _ ≤ p38Gamma u m * (|z| / (1 - u) + W) +
          u / (1 - u) * |z| := by
      gcongr
      exact p38_gamma_nonneg u m hu
        (p38_gamma_valid_le u m (m + 1) hu (by omega) hm)
    _ = (p38Gamma u m + u) / (1 - u) * |z| +
          p38Gamma u m * W := by ring
    _ ≤ p38Gamma u (m + 1) * (|z| + W) := by
      nlinarith [hmul1, hmul2]

private lemma p38_dot_step_bound (fp : P38FPModel) (m : ℕ)
    (hm : P38GammaValid fp.u (m + 1)) (hpos : 1 ≤ m)
    (s A W a x : ℝ) (hW : 0 ≤ W) (hA : |A| ≤ W)
    (hold : |s - A| ≤ p38Gamma fp.u m * W) :
    |fp.fl_add s (fp.fl_mul a x) - (A + a * x)| ≤
      p38Gamma fp.u (m + 1) * (W + |a * x|) := by
  let u := fp.u
  let q := fp.fl_mul a x
  let z := fp.fl_add s q
  let t := a * x
  have hu : 0 ≤ u := fp.u_nonneg
  have hmul : |q - t| ≤ u * |t| := p38_mul_error fp a x
  have hadd : |z - (s + q)| ≤ u * |s + q| := p38_add_error fp s q
  have hq : |q| ≤ (1 + u) * |t| := by
    calc
      |q| = |(q - t) + t| := by ring
      _ ≤ |q - t| + |t| := abs_add_le _ _
      _ ≤ u * |t| + |t| := add_le_add hmul (le_refl _)
      _ = (1 + u) * |t| := by ring
  have hs : |s| ≤ |s - A| + W := by
    calc
      |s| = |(s - A) + A| := by ring
      _ ≤ |s - A| + |A| := abs_add_le _ _
      _ ≤ |s - A| + W := add_le_add (le_refl _) hA
  have hsq : |s + q| ≤ |s - A| + W + (1 + u) * |t| := by
    calc
      |s + q| ≤ |s| + |q| := abs_add_le _ _
      _ ≤ |s - A| + W + (1 + u) * |t| := add_le_add hs hq
  have htri : |z - (A + t)| ≤
      |z - (s + q)| + |s - A| + |q - t| := by
    have hid : z - (A + t) = (z - (s + q)) + (s - A) + (q - t) := by ring
    calc
      |z - (A + t)| = |(z - (s + q)) + (s - A) + (q - t)| := congrArg abs hid
      _ ≤ |z - (s + q)| + |s - A| + |q - t| := by
        calc
          _ ≤ |(z - (s + q)) + (s - A)| + |q - t| := abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
  have hcoef1 := p38_gamma_step u m hu hm
  have hcoef2 := p38_gamma_two u m hu hm hpos
  have hmul1 := mul_le_mul_of_nonneg_right hcoef1 hW
  have hmul2 := mul_le_mul_of_nonneg_right hcoef2 (abs_nonneg t)
  calc
    |z - (A + t)| ≤ u * |s + q| + |s - A| + u * |t| := by
      exact le_trans htri (add_le_add (add_le_add hadd (le_refl _)) hmul)
    _ ≤ u * (|s - A| + W + (1 + u) * |t|) + |s - A| + u * |t| := by
      gcongr
    _ ≤ u * (p38Gamma u m * W + W + (1 + u) * |t|) +
          p38Gamma u m * W + u * |t| := by
      gcongr
    _ = (p38Gamma u m * (1 + u) + u) * W +
          (2 * u + u ^ 2) * |t| := by ring
    _ ≤ p38Gamma u (m + 1) * (W + |t|) := by
      nlinarith [hmul1, hmul2]

private noncomputable def p38DotFold (fp : P38FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (s : ℝ) : ℝ :=
  Fin.foldl m (fun acc i => fp.fl_add acc (fp.fl_mul (a i) (x i))) s

private lemma p38_dot_fold_bound (fp : P38FPModel) (k m : ℕ)
    (a x : Fin m → ℝ) (s A W : ℝ)
    (hk : 1 ≤ k) (hkm : P38GammaValid fp.u (k + m))
    (hW : 0 ≤ W) (hA : |A| ≤ W)
    (hold : |s - A| ≤ p38Gamma fp.u k * W) :
    |p38DotFold fp m a x s - (A + ∑ i : Fin m, a i * x i)| ≤
      p38Gamma fp.u (k + m) *
        (W + ∑ i : Fin m, |a i * x i|) := by
  induction m generalizing k s A W with
  | zero =>
      simpa [p38DotFold] using hold
  | succ m ih =>
      have hk1 : P38GammaValid fp.u (k + 1) :=
        p38_gamma_valid_le fp.u (k + 1) (k + (m + 1))
          fp.u_nonneg (by omega) hkm
      let a' : Fin m → ℝ := fun i => a i.succ
      let x' : Fin m → ℝ := fun i => x i.succ
      let t := a 0 * x 0
      let s' := fp.fl_add s (fp.fl_mul (a 0) (x 0))
      have hstep := p38_dot_step_bound fp k (by simpa [Nat.add_comm] using hk1)
        hk s A W (a 0) (x 0) hW hA hold
      have hA' : |A + t| ≤ W + |t| := by
        calc
          |A + t| ≤ |A| + |t| := abs_add_le _ _
          _ ≤ W + |t| := add_le_add hA (le_refl _)
      have hW' : 0 ≤ W + |t| := add_nonneg hW (abs_nonneg _)
      have hkm' : P38GammaValid fp.u ((k + 1) + m) := by
        convert hkm using 1 <;> omega
      have hrest := ih (k + 1) a' x' s' (A + t) (W + |t|)
        (by omega) hkm' hW' hA' hstep
      simpa only [p38DotFold, Fin.foldl_succ, Fin.sum_univ_succ,
        a', x', t, s', add_assoc, Nat.add_comm 1 m] using hrest

private lemma p38_gamma_one_ge_u (u : ℝ) (hu : 0 ≤ u)
    (h1 : P38GammaValid u 1) : u ≤ p38Gamma u 1 := by
  have hu1 : u < 1 := by simpa [P38GammaValid] using h1
  have hden : 0 < 1 - u := by linarith
  simp only [p38Gamma, Nat.cast_one, one_mul]
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg u]

private lemma p38_rounded_dot_bound (fp : P38FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (hn : P38GammaValid fp.u n) :
    |p38RoundedDotProduct fp n a x - (∑ i : Fin n, a i * x i)| ≤
      p38Gamma fp.u n * (∑ i : Fin n, |a i * x i|) := by
  cases n with
  | zero => simp [p38RoundedDotProduct]
  | succ m =>
      let a' : Fin m → ℝ := fun i => a i.succ
      let x' : Fin m → ℝ := fun i => x i.succ
      have h1 : P38GammaValid fp.u 1 :=
        p38_gamma_valid_le fp.u 1 (m + 1) fp.u_nonneg (by omega) hn
      have hmul := p38_mul_error fp (a 0) (x 0)
      have hgamma := p38_gamma_one_ge_u fp.u fp.u_nonneg h1
      have hinit : |fp.fl_mul (a 0) (x 0) - a 0 * x 0| ≤
          p38Gamma fp.u 1 * |a 0 * x 0| := by
        exact le_trans hmul
          (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
      have hfold := p38_dot_fold_bound fp 1 m a' x'
        (fp.fl_mul (a 0) (x 0)) (a 0 * x 0) |a 0 * x 0|
        (by omega) (by simpa [Nat.add_comm] using hn) (abs_nonneg _)
        (le_refl _) hinit
      simpa only [p38RoundedDotProduct, p38DotFold, Fin.sum_univ_succ,
        a', x', add_assoc, Nat.add_comm 1 m] using hfold

private lemma p38_sum_lower (n : ℕ) (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  let F : ℕ → ℝ := fun k => if h : k < n then f ⟨k, h⟩ else 0
  have htotal : (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := by
    simpa [F] using (Fin.sum_univ_eq_sum_range F n)
  have hprefix : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
      ∑ k ∈ Finset.range i.val, F k := by
    calc
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
          ∑ t : Fin i.val, F t.val := by
        apply Finset.sum_congr rfl
        intro t _
        simp [F, lt_trans t.isLt i.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range F i.val
  have htail : ∑ k ∈ Finset.range (n - (i.val + 1)), F (i.val + 1 + k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : i.val + 1 + k < n := by
      have hkr : k < n - (i.val + 1) := Finset.mem_range.mp hk
      omega
    have hgt : i.val < i.val + 1 + k := by omega
    simp only [F, dif_pos hkn]
    exact hzero ⟨i.val + 1 + k, hkn⟩ hgt
  have hn : i.val + 1 + (n - (i.val + 1)) = n := by omega
  have hFi : F i.val = f i := by simp [F, i.isLt]
  calc
    (∑ j : Fin n, f j) = ∑ k ∈ Finset.range n, F k := htotal
    _ = (∑ k ∈ Finset.range (i.val + 1), F k) +
          (∑ k ∈ Finset.range (n - (i.val + 1)), F (i.val + 1 + k)) := by
      simpa only [hn] using
        (Finset.sum_range_add F (i.val + 1) (n - (i.val + 1)))
    _ = ∑ k ∈ Finset.range (i.val + 1), F k := by rw [htail, add_zero]
    _ = (∑ k ∈ Finset.range i.val, F k) + F i.val :=
      Finset.sum_range_succ F i.val
    _ = (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
      rw [hprefix, hFi]

private noncomputable def p38RowPrefix (n : ℕ) (L : P38Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ t : Fin i.val, L i ⟨t.val, by omega⟩ * x ⟨t.val, by omega⟩

private noncomputable def p38RowAbsPrefix (n : ℕ) (L : P38Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ t : Fin i.val, |L i ⟨t.val, by omega⟩ * x ⟨t.val, by omega⟩|

private def p38RowBound (fp : P38FPModel) (n : ℕ) (L : P38Matrix n n)
    (b x : Fin n → ℝ) (i : Fin n) : Prop :=
  |L i i * x i + p38RowPrefix n L x i - b i| ≤
    p38Gamma fp.u (i.val + 1) *
      (|L i i * x i| + p38RowAbsPrefix n L x i)

private lemma p38_row_bound_congr (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b x y : Fin n → ℝ) (i : Fin n)
    (hxy : ∀ j : Fin n, j.val ≤ i.val → x j = y j) :
    p38RowBound fp n L b x i ↔ p38RowBound fp n L b y i := by
  have hdiag : x i = y i := hxy i (le_refl _)
  have hp : p38RowPrefix n L x i = p38RowPrefix n L y i := by
    unfold p38RowPrefix
    apply Finset.sum_congr rfl
    intro t _
    rw [hxy ⟨t.val, by omega⟩ (by change t.val ≤ i.val; omega)]
  have ha : p38RowAbsPrefix n L x i = p38RowAbsPrefix n L y i := by
    unfold p38RowAbsPrefix
    apply Finset.sum_congr rfl
    intro t _
    rw [hxy ⟨t.val, by omega⟩ (by change t.val ≤ i.val; omega)]
  simp only [p38RowBound, hdiag, hp, ha]

private lemma p38_row_bound_update (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b x : Fin n → ℝ)
    (i j : Fin n) (v : ℝ) (hij : i.val < j.val) :
    p38RowBound fp n L b (Function.update x j v) i ↔
      p38RowBound fp n L b x i := by
  apply p38_row_bound_congr
  intro k hk
  exact Function.update_of_ne (Fin.ne_of_lt (show k < j by exact hk.trans_lt hij)) v x

private lemma p38_row_bound_new (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b x : Fin n → ℝ) (i : Fin n)
    (hd : L i i ≠ 0) (hn : P38GammaValid fp.u n) :
    let count := i.val
    let s := Fin.foldl count
      (fun acc (t : Fin count) =>
        fp.fl_sub acc (fp.fl_mul (L i ⟨t.val, by omega⟩)
          (x ⟨t.val, by omega⟩))) (b i)
    p38RowBound fp n L b (Function.update x i (fp.fl_div s (L i i))) i := by
  intro count s
  let a : Fin count → ℝ := fun t => L i ⟨t.val, by omega⟩
  let xx : Fin count → ℝ := fun t => x ⟨t.val, by omega⟩
  have hc : P38GammaValid fp.u count :=
    p38_gamma_valid_le fp.u count n fp.u_nonneg (by omega) hn
  have hci : P38GammaValid fp.u (count + 1) :=
    p38_gamma_valid_le fp.u (count + 1) n fp.u_nonneg (by omega) hn
  have hfold := p38_sub_fold_bound fp count a xx (b i) hc
  have hW : 0 ≤ ∑ t : Fin count, |a t * xx t| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hdiv := p38_div_step_bound fp count hci s
    (∑ t : Fin count, a t * xx t)
    (∑ t : Fin count, |a t * xx t|)
    (b i) (L i i) hW hd (by simpa [s, p38SubFold, a, xx] using hfold)
  have hup : ∀ t : Fin count,
      Function.update x i (fp.fl_div s (L i i)) ⟨t.val, by omega⟩ =
        x ⟨t.val, by omega⟩ := by
    intro t
    apply Function.update_of_ne
    exact Fin.ne_of_lt (show (⟨t.val, by omega⟩ : Fin n) < i by
      change t.val < i.val
      exact t.isLt)
  unfold p38RowBound p38RowPrefix p38RowAbsPrefix
  simp only [Function.update_self]
  simp_rw [hup]
  simpa only [a, xx, count] using hdiv

private lemma p38_forward_steps_bound (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0) (hn : P38GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (hprev : ∀ i : Fin n, i.val < n - k → p38RowBound fp n L b x i) :
    ∀ i : Fin n,
      p38RowBound fp n L b (p38ForwardSubSteps fp n L b k hk x) i := by
  induction k generalizing x with
  | zero =>
      intro i
      simpa [p38ForwardSubSteps] using hprev i (by omega)
  | succ k ih =>
      let count := n - k - 1
      have hlt : count < n := by omega
      let ik : Fin n := ⟨count, hlt⟩
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc (fp.fl_mul (L ik ⟨t.val, by omega⟩)
            (x ⟨t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hnew : p38RowBound fp n L b x' ik := by
        simpa only [x', s, count] using
          (p38_row_bound_new fp n L b x ik (hdiag ik) hn)
      have hprev' : ∀ i : Fin n, i.val < n - k →
          p38RowBound fp n L b x' i := by
        intro i hi
        by_cases hless : i.val < count
        · have hbefore : p38RowBound fp n L b x i :=
            hprev i (by omega)
          exact (p38_row_bound_update fp n L b x i ik
            (fp.fl_div s (L ik ik)) (by simpa [ik] using hless)).2 hbefore
        · have hieq : i = ik := Fin.ext (by simp [ik, count]; omega)
          simpa [hieq] using hnew
      have hfinal := ih (Nat.le_of_succ_le hk) x' hprev'
      simpa only [p38ForwardSubSteps, count, ik, s, x'] using hfinal

private lemma p38_forward_residual_bound (fp : P38FPModel) (n : ℕ)
    (L : P38Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : P38GammaValid fp.u n) :
    ∀ i : Fin n,
      |(∑ j : Fin n, L i j * p38ForwardSub fp n L b j) - b i| ≤
        p38Gamma fp.u n *
          (∑ j : Fin n, |L i j| * |p38ForwardSub fp n L b j|) := by
  let x := p38ForwardSub fp n L b
  have hall : ∀ i : Fin n, p38RowBound fp n L b x i := by
    simpa only [x, p38ForwardSub] using
      (p38_forward_steps_bound fp n L b hdiag hn n (le_refl n)
        (fun _ => 0) (by intro i hi; omega))
  intro i
  have hsum : (∑ j : Fin n, L i j * x j) =
      p38RowPrefix n L x i + L i i * x i := by
    simpa only [p38RowPrefix] using
      (p38_sum_lower n i (fun j => L i j * x j)
        (by intro j hij; simp [hlower i j hij]))
  have habs : (∑ j : Fin n, |L i j * x j|) =
      p38RowAbsPrefix n L x i + |L i i * x i| := by
    simpa only [p38RowAbsPrefix] using
      (p38_sum_lower n i (fun j => |L i j * x j|)
        (by intro j hij; simp [hlower i j hij]))
  have hgn : p38Gamma fp.u (i.val + 1) ≤ p38Gamma fp.u n :=
    p38_gamma_le fp.u (i.val + 1) n fp.u_nonneg (by omega) hn
  have hW : 0 ≤ |L i i * x i| + p38RowAbsPrefix n L x i := by
    unfold p38RowAbsPrefix
    positivity
  have hscale := mul_le_mul_of_nonneg_right hgn hW
  have hrow := hall i
  change |L i i * x i + p38RowPrefix n L x i - b i| ≤
    p38Gamma fp.u (i.val + 1) *
      (|L i i * x i| + p38RowAbsPrefix n L x i) at hrow
  change |(∑ j : Fin n, L i j * x j) - b i| ≤
    p38Gamma fp.u n * (∑ j : Fin n, |L i j| * |x j|)
  simp_rw [← abs_mul]
  calc
    |(∑ j : Fin n, L i j * x j) - b i| =
        |L i i * x i + p38RowPrefix n L x i - b i| := by
      rw [hsum]
      congr 1
      ring
    _ ≤ p38Gamma fp.u (i.val + 1) *
          (|L i i * x i| + p38RowAbsPrefix n L x i) := hrow
    _ ≤ p38Gamma fp.u n * (∑ j : Fin n, |L i j * x j|) := by
      rw [habs]
      convert hscale using 1 <;> ring

/-- The Method B off-diagonal block estimate in the proof of (6.1). -/
theorem p38_c3_methodB_offdiagonal_residual
    (fp : P38FPModel) (n r p : ℕ)
    (L22 : P38Matrix n n) (L21 : P38Matrix n r)
    (X11 : P38Matrix r p)
    (hdiag : ∀ i, L22 i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L22 i j = 0)
    (hn : P38GammaValid fp.u n)
    (hr : P38GammaValid fp.u r) :
    ∀ i j,
      |(∑ k : Fin n, L22 i k * p38MethodBOffDiagonal fp L22 L21 X11 k j) +
        (∑ k : Fin r, L21 i k * X11 k j)| ≤
      p38Gamma fp.u n *
        (∑ k : Fin n, |L22 i k| * |p38MethodBOffDiagonal fp L22 L21 X11 k j|) +
      p38Gamma fp.u r *
        (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
  -- PROOF_START P38-C3-H001
  intro i j
  let b : Fin n → ℝ := fun k => -(p38RoundedMatMul fp L21 X11 k j)
  let x : Fin n → ℝ := p38ForwardSub fp n L22 b
  have hsolve := p38_forward_residual_bound fp n L22 b hdiag hlower hn i
  have hdot := p38_rounded_dot_bound fp r (L21 i) (fun k => X11 k j) hr
  have hs : |(∑ k : Fin n, L22 i k * x k) +
      p38RoundedMatMul fp L21 X11 i j| ≤
      p38Gamma fp.u n * (∑ k : Fin n, |L22 i k| * |x k|) := by
    simpa only [b, sub_neg_eq_add] using hsolve
  have hp : |(∑ k : Fin r, L21 i k * X11 k j) -
      p38RoundedMatMul fp L21 X11 i j| ≤
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|) := by
    simpa only [p38RoundedMatMul, abs_sub_comm, abs_mul] using hdot
  change |(∑ k : Fin n, L22 i k * x k) +
      (∑ k : Fin r, L21 i k * X11 k j)| ≤
    p38Gamma fp.u n * (∑ k : Fin n, |L22 i k| * |x k|) +
      p38Gamma fp.u r * (∑ k : Fin r, |L21 i k| * |X11 k j|)
  calc
    |(∑ k : Fin n, L22 i k * x k) +
        (∑ k : Fin r, L21 i k * X11 k j)| =
      |((∑ k : Fin n, L22 i k * x k) +
          p38RoundedMatMul fp L21 X11 i j) +
        ((∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j)| := by
      congr 1
      ring
    _ ≤ |(∑ k : Fin n, L22 i k * x k) +
          p38RoundedMatMul fp L21 X11 i j| +
        |(∑ k : Fin r, L21 i k * X11 k j) -
          p38RoundedMatMul fp L21 X11 i j| := abs_add_le _ _
    _ ≤ _ := add_le_add hs hp

end VSCLReuse

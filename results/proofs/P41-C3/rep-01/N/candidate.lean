import VSCLReuse.P41.Definitions

namespace VSCLReuse

open scoped BigOperators

private lemma p41_gamma_nonneg (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (hv : P41GammaValid u n) : 0 ≤ p41Gamma u n := by
  unfold p41Gamma P41GammaValid at *
  have hnum : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  exact div_nonneg hnum (by linarith)

private lemma p41_gamma_mono (u : ℝ) (m n : ℕ) (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : P41GammaValid u n) :
    p41Gamma u m ≤ p41Gamma u n := by
  unfold p41Gamma P41GammaValid at *
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hle : (m : ℝ) * u ≤ (n : ℝ) * u := mul_le_mul_of_nonneg_right hmn' hu
  have hpm : 0 < 1 - (m : ℝ) * u := by linarith
  have hpn : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hpm hpn).2
  nlinarith

private lemma p41_gamma_step (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P41GammaValid u (m+1)) :
    (p41Gamma u m + u) / (1-u) ≤ p41Gamma u (m+1) := by
  unfold p41Gamma P41GammaValid at *
  have hm : 0 ≤ (m : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hp : 0 < 1 - (m : ℝ) * u := by push_cast at hv ⊢; nlinarith
  have hu1 : 0 < 1-u := by
    have hvc : ((m:ℝ)+1)*u < 1 := by simpa only [Nat.cast_add, Nat.cast_one] using hv
    have : u ≤ (m + 1 : ℝ) * u := by
      have hh : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
        exact_mod_cast (by omega : 1 ≤ m+1)
      simpa using (mul_le_mul_of_nonneg_right hh hu)
    linarith
  have hpn : 0 < 1 - ((m+1:ℕ):ℝ) * u := by linarith
  apply (div_le_div_iff₀ hu1 hpn).2
  have hcast : ((m+1:ℕ):ℝ) = (m:ℝ)+1 := by push_cast; ring
  rw [hcast] at hv hpn ⊢
  let t : ℝ := (m:ℝ)*u
  let g : ℝ := t/(1-t)
  have hg : 0 ≤ g := div_nonneg hm (le_of_lt hp)
  have hgid : g * (1-t) = t := by
    dsimp [g]
    exact div_mul_cancel₀ t (ne_of_gt hp)
  have hrel : ((m:ℝ)+1)*u=t+u := by dsimp [t]; ring
  rw [hrel]
  change (g+u)*(1-(t+u)) ≤ (t+u)*(1-u)
  nlinarith [mul_nonneg hg hu]

private lemma p41_round_back (u δ v s : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) (hd : |δ| ≤ u) (hs : s = v * (1+δ)) :
    |v-s| ≤ (u/(1-u))*|s| := by
  have hdlo : -u ≤ δ := (abs_le.mp hd).1
  have hp : 0 < 1+δ := by linarith
  have hvl : |v-s| ≤ u*|v| := by
    have heq : v-s = -(v*δ) := by rw [hs]; ring
    rw [heq, abs_neg, abs_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd (abs_nonneg v)
  have hsl : (1-u)*|v| ≤ |s| := by
    rw [hs, abs_mul, abs_of_pos hp]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (by linarith : 1-u ≤ 1+δ) (abs_nonneg v)
  have hprod := mul_le_mul_of_nonneg_left hsl hu
  have hprod2 := mul_le_mul_of_nonneg_right hvl (by linarith : 0 ≤ 1-u)
  have hmain : |v-s| * (1-u) ≤ u*|s| := by nlinarith
  calc
    |v-s| ≤ (u*|s|)/(1-u) := (le_div_iff₀ (by linarith : 0 < 1-u)).2 hmain
    _ = (u/(1-u))*|s| := by ring

private lemma p41_fl_sub_mul_back (fp : P41FPModel) (a x y : ℝ)
    (hu1 : fp.u < 1) :
    let s := fp.fl_sub a (fp.fl_mul x y)
    |a - s - x*y| ≤ (fp.u/(1-fp.u))*|s| + fp.u*|x*y| := by
  obtain ⟨dm, hdm, hm⟩ := fp.model_mul x y
  obtain ⟨ds, hds, hs⟩ := fp.model_sub a (fp.fl_mul x y)
  dsimp
  have hback := p41_round_back fp.u ds (a - fp.fl_mul x y)
    (fp.fl_sub a (fp.fl_mul x y)) fp.u_nonneg hu1 hds hs
  have hmul : |fp.fl_mul x y - x*y| ≤ fp.u*|x*y| := by
    rw [hm]
    have heq : (x*y)*(1+dm)-x*y = (x*y)*dm := by ring
    rw [heq, abs_mul]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hdm (abs_nonneg (x*y))
  have heq : a - fp.fl_sub a (fp.fl_mul x y) - x*y =
      (a - fp.fl_mul x y - fp.fl_sub a (fp.fl_mul x y)) +
        (fp.fl_mul x y - x*y) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hback hmul)

private lemma p41_gamma_coeffs (u : ℝ) (m : ℕ) (hu : 0 ≤ u)
    (hv : P41GammaValid u (m+1)) :
    let g := p41Gamma u m
    let q := u/(1-u)
    g + (g+1)*q ≤ p41Gamma u (m+1) ∧
      g + (g+1)*u ≤ p41Gamma u (m+1) := by
  dsimp
  have hu1 : u < 1 := by
    have hh : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
      exact_mod_cast (by omega : 1 ≤ m+1)
    have hm := mul_le_mul_of_nonneg_right hh hu
    have hv' := hv
    unfold P41GammaValid at hv'
    linarith
  have hgm : 0 ≤ p41Gamma u m := p41_gamma_nonneg u m hu (by
    unfold P41GammaValid at *
    have hc : ((m:ℝ)*u) ≤ ((m+1:ℕ):ℝ)*u := by
      apply mul_le_mul_of_nonneg_right _ hu
      exact_mod_cast (by omega : m ≤ m+1)
    linarith)
  have hstep := p41_gamma_step u m hu hv
  have hiden : p41Gamma u m + (p41Gamma u m+1)*(u/(1-u)) =
      (p41Gamma u m+u)/(1-u) := by
    have hne : 1-u ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  constructor
  · calc
      _ = (p41Gamma u m+u)/(1-u) := hiden
      _ ≤ _ := hstep
  · have hq : p41Gamma u m + (p41Gamma u m+1)*u ≤
        p41Gamma u m + (p41Gamma u m+1)*(u/(1-u)) := by
      have huq : u ≤ u/(1-u) := by
        apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
        nlinarith [sq_nonneg u]
      simpa only [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left huq (by linarith : 0 ≤ p41Gamma u m+1))
        (p41Gamma u m)
    exact hq.trans (hiden.le.trans hstep)

private lemma p41_sub_fold_back (fp : P41FPModel) :
    ∀ (m : ℕ) (x y : Fin m → ℝ) (b : ℝ),
      P41GammaValid fp.u m →
      let s := Fin.foldl m
        (fun a i => fp.fl_sub a (fp.fl_mul (x i) (y i))) b
      |b-s-(∑ i : Fin m, x i*y i)| ≤
        p41Gamma fp.u m * (|s| + ∑ i : Fin m, |x i*y i|) := by
  intro m
  induction m with
  | zero =>
      intro x y b hv
      simp [p41Gamma]
  | succ m ih =>
      intro x y b hv
      let xx : Fin m → ℝ := fun i => x i.castSucc
      let yy : Fin m → ℝ := fun i => y i.castSucc
      let s := Fin.foldl m
        (fun a i => fp.fl_sub a (fp.fl_mul (xx i) (yy i))) b
      let z := x (Fin.last m) * y (Fin.last m)
      let s' := fp.fl_sub s (fp.fl_mul (x (Fin.last m)) (y (Fin.last m)))
      let T := ∑ i : Fin m, |xx i*yy i|
      let S := ∑ i : Fin m, xx i*yy i
      let g := p41Gamma fp.u m
      let G := p41Gamma fp.u (m+1)
      let q := fp.u/(1-fp.u)
      have hvm : P41GammaValid fp.u m := by
        unfold P41GammaValid at *
        have hc : (m:ℝ)*fp.u ≤ ((m+1:ℕ):ℝ)*fp.u := by
          apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
          exact_mod_cast (by omega : m ≤ m+1)
        linarith
      have hi : |b-s-S| ≤ g*(|s|+T) := ih xx yy b hvm
      have hu1 : fp.u < 1 := by
        have hh : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
          exact_mod_cast (by omega : 1 ≤ m+1)
        have hm := mul_le_mul_of_nonneg_right hh fp.u_nonneg
        unfold P41GammaValid at hv
        linarith
      have hl : |s-s'-z| ≤ q*|s'| + fp.u*|z| :=
        p41_fl_sub_mul_back fp s (x (Fin.last m)) (y (Fin.last m)) hu1
      have hg : 0 ≤ g := p41_gamma_nonneg fp.u m fp.u_nonneg hvm
      have hsize : |s| ≤ |s'|+|z|+|s-s'-z| := by
        have heq : s = (s-s'-z)+(s'+z) := by ring
        have hh := abs_add_le (s-s'-z) (s'+z)
        have hh' := abs_add_le s' z
        calc
          |s| = |(s-s'-z)+(s'+z)| := congrArg abs heq
          _ ≤ |s-s'-z| + |s'+z| := hh
          _ ≤ |s'|+|z|+|s-s'-z| := by linarith
      have hc := p41_gamma_coeffs fp.u m fp.u_nonneg hv
      have hc1 : g + (g+1)*q ≤ G := hc.1
      have hc2 : g + (g+1)*fp.u ≤ G := hc.2
      have hgG : g ≤ G := p41_gamma_mono fp.u m (m+1) fp.u_nonneg (by omega) hv
      have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => abs_nonneg _)
      have hmidsize := mul_le_mul_of_nonneg_left hsize hg
      have hmidsub := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ g+1)
      have hmid : |b-s'-(S+z)| ≤
          (g+(g+1)*q)*|s'| + g*T + (g+(g+1)*fp.u)*|z| := by
        have heq : b-s'-(S+z) = (b-s-S)+(s-s'-z) := by ring
        rw [heq]
        have htri := abs_add_le (b-s-S) (s-s'-z)
        nlinarith
      have hb1 := mul_le_mul_of_nonneg_right hc1 (abs_nonneg s')
      have hb2 := mul_le_mul_of_nonneg_right hc2 (abs_nonneg z)
      have hb3 := mul_le_mul_of_nonneg_right hgG hT
      have hfinal : |b-s'-(S+z)| ≤ G*(|s'|+(T+|z|)) := by
        nlinarith
      simpa only [Fin.foldl_succ_last, Fin.sum_univ_castSucc] using hfinal

private lemma p41_fl_div_back (fp : P41FPModel) (s d : ℝ)
    (hd : d ≠ 0) (hu1 : fp.u < 1) :
    |s-d*fp.fl_div s d| ≤
      (fp.u/(1-fp.u))*|d*fp.fl_div s d| := by
  obtain ⟨δ, hδ, hmodel⟩ := fp.model_div s d hd
  have hback := p41_round_back fp.u δ (s/d) (fp.fl_div s d)
    fp.u_nonneg hu1 hδ hmodel
  have heq : s - d*fp.fl_div s d = d*(s/d - fp.fl_div s d) := by
    have hh : d*(s/d)=s := mul_div_cancel₀ s hd
    nlinarith
  rw [heq, abs_mul, abs_mul]
  have hh := mul_le_mul_of_nonneg_left hback (abs_nonneg d)
  nlinarith

private lemma p41_sub_div_back (fp : P41FPModel) (m : ℕ)
    (x y : Fin m → ℝ) (b d : ℝ) (hd : d ≠ 0)
    (hv : P41GammaValid fp.u (m+1)) :
    let s := Fin.foldl m
      (fun a i => fp.fl_sub a (fp.fl_mul (x i) (y i))) b
    let v := fp.fl_div s d
    |b-d*v-(∑ i : Fin m, x i*y i)| ≤
      p41Gamma fp.u (m+1) *
        (|d*v| + ∑ i : Fin m, |x i*y i|) := by
  dsimp
  let s := Fin.foldl m
    (fun a i => fp.fl_sub a (fp.fl_mul (x i) (y i))) b
  let v := fp.fl_div s d
  let S := ∑ i : Fin m, x i*y i
  let T := ∑ i : Fin m, |x i*y i|
  let g := p41Gamma fp.u m
  let G := p41Gamma fp.u (m+1)
  let q := fp.u/(1-fp.u)
  have hvm : P41GammaValid fp.u m := by
    unfold P41GammaValid at *
    have hc : (m:ℝ)*fp.u ≤ ((m+1:ℕ):ℝ)*fp.u := by
      apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
      exact_mod_cast (by omega : m ≤ m+1)
    linarith
  have hu1 : fp.u < 1 := by
    have hh : (1:ℝ) ≤ ((m+1:ℕ):ℝ) := by
      exact_mod_cast (by omega : 1 ≤ m+1)
    have hm := mul_le_mul_of_nonneg_right hh fp.u_nonneg
    unfold P41GammaValid at hv
    linarith
  have hi : |b-s-S| ≤ g*(|s|+T) := p41_sub_fold_back fp m x y b hvm
  have hl : |s-d*v| ≤ q*|d*v| := p41_fl_div_back fp s d hd hu1
  have hsize : |s| ≤ |d*v| + |s-d*v| := by
    have heq : s = d*v+(s-d*v) := by ring
    calc
      |s| = |d*v+(s-d*v)| := congrArg abs heq
      _ ≤ |d*v|+|s-d*v| := abs_add_le _ _
  have hg : 0 ≤ g := p41_gamma_nonneg fp.u m fp.u_nonneg hvm
  have hc := (p41_gamma_coeffs fp.u m fp.u_nonneg hv).1
  have hc' : g+(g+1)*q ≤ G := hc
  have hgG : g ≤ G := p41_gamma_mono fp.u m (m+1) fp.u_nonneg (by omega) hv
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have hmid1 := mul_le_mul_of_nonneg_left hsize hg
  have hmid2 := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ g+1)
  have h1 := mul_le_mul_of_nonneg_right hc' (abs_nonneg (d*v))
  have h2 := mul_le_mul_of_nonneg_right hgG hT
  have heq : b-d*v-S = (b-s-S)+(s-d*v) := by ring
  have htri : |b-d*v-S| ≤ |b-s-S| + |s-d*v| := by
    rw [heq]
    exact abs_add_le _ _
  nlinarith

private lemma p41_dot_step (fp : P41FPModel) (m : ℕ)
    (x y : Fin (m+2) → ℝ) :
    p41RoundedDotProduct fp (m+2) x y =
      fp.fl_add
        (p41RoundedDotProduct fp (m+1)
          (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (m+1))) (y (Fin.last (m+1)))) := by
  simp only [p41RoundedDotProduct, Fin.foldl_succ_last]
  rfl

private lemma p41_fl_add_mul_forward (fp : P41FPModel) (a x y : ℝ) :
    |fp.fl_add a (fp.fl_mul x y) - (a+x*y)| ≤
      fp.u*|a| + (2*fp.u+fp.u^2)*|x*y| := by
  obtain ⟨dm, hdm, hm⟩ := fp.model_mul x y
  obtain ⟨da, hda, ha⟩ := fp.model_add a (fp.fl_mul x y)
  have hm' : |dm| * |da| ≤ fp.u*fp.u :=
    mul_le_mul hdm hda (abs_nonneg _) fp.u_nonneg
  have hcoef : |dm+da+dm*da| ≤ 2*fp.u+fp.u^2 := by
    calc
      |dm+da+dm*da| ≤ |dm+da|+|dm*da| := abs_add_le _ _
      _ ≤ |dm|+|da|+|dm| * |da| := by
        rw [abs_mul]
        linarith [abs_add_le dm da]
      _ ≤ 2*fp.u+fp.u^2 := by nlinarith
  have heq : fp.fl_add a (fp.fl_mul x y) - (a+x*y) =
      a*da + (x*y)*(dm+da+dm*da) := by
    rw [ha, hm]
    ring
  rw [heq]
  calc
    |a*da + (x*y)*(dm+da+dm*da)| ≤
      |a*da|+|(x*y)*(dm+da+dm*da)| := abs_add_le _ _
    _ = |a| * |da|+|x*y| * |dm+da+dm*da| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * fp.u+|x*y| * (2*fp.u+fp.u^2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hda (abs_nonneg a))
        (mul_le_mul_of_nonneg_left hcoef (abs_nonneg (x*y)))
    _ = fp.u*|a|+(2*fp.u+fp.u^2)*|x*y| := by ring

private lemma p41_u_le_gamma_one (u : ℝ) (hu : 0 ≤ u)
    (hv : P41GammaValid u 1) : u ≤ p41Gamma u 1 := by
  have hu1 : u < 1 := by simpa [P41GammaValid] using hv
  unfold p41Gamma
  norm_num
  apply (le_div_iff₀ (by linarith : 0 < 1-u)).2
  nlinarith [sq_nonneg u]

private lemma p41_rounded_dot_bound (fp : P41FPModel) :
    ∀ (n : ℕ) (x y : Fin n → ℝ), P41GammaValid fp.u n →
      |p41RoundedDotProduct fp n x y - ∑ i : Fin n, x i*y i| ≤
        p41Gamma fp.u n * ∑ i : Fin n, |x i*y i| := by
  intro n
  induction n with
  | zero =>
      intro x y hv
      simp [p41RoundedDotProduct]
  | succ n ih =>
      cases n with
      | zero =>
          intro x y hv
          obtain ⟨δ, hδ, hm⟩ := fp.model_mul (x 0) (y 0)
          have hg := p41_u_le_gamma_one fp.u fp.u_nonneg hv
          have hprod : |fp.fl_mul (x 0) (y 0) - x 0*y 0| ≤
              fp.u*|x 0*y 0| := by
            rw [hm]
            have heq : x 0*y 0*(1+δ)-x 0*y 0 = (x 0*y 0)*δ := by ring
            rw [heq, abs_mul]
            simpa only [mul_comm] using
              mul_le_mul_of_nonneg_left hδ (abs_nonneg (x 0*y 0))
          have hb := mul_le_mul_of_nonneg_right hg (abs_nonneg (x 0*y 0))
          simpa [p41RoundedDotProduct] using hprod.trans hb
      | succ m =>
          intro x y hv
          let xx : Fin (m+1) → ℝ := fun i => x i.castSucc
          let yy : Fin (m+1) → ℝ := fun i => y i.castSucc
          let a := p41RoundedDotProduct fp (m+1) xx yy
          let z := x (Fin.last (m+1))*y (Fin.last (m+1))
          let a' := fp.fl_add a
            (fp.fl_mul (x (Fin.last (m+1))) (y (Fin.last (m+1))))
          let S := ∑ i : Fin (m+1), xx i*yy i
          let W := ∑ i : Fin (m+1), |xx i*yy i|
          let g := p41Gamma fp.u (m+1)
          let G := p41Gamma fp.u (m+2)
          have hvm : P41GammaValid fp.u (m+1) := by
            unfold P41GammaValid at *
            have hc : ((m+1:ℕ):ℝ)*fp.u ≤ ((m+2:ℕ):ℝ)*fp.u := by
              apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
              exact_mod_cast (by omega : m+1 ≤ m+2)
            linarith
          have hi : |a-S| ≤ g*W := ih xx yy hvm
          have hSW : |S| ≤ W :=
            Finset.abs_sum_le_sum_abs (fun i : Fin (m+1) => xx i*yy i) Finset.univ
          have hsize : |a| ≤ W+|a-S| := by
            have heq : a=(a-S)+S := by ring
            calc
              |a| = |(a-S)+S| := congrArg abs heq
              _ ≤ |a-S|+|S| := abs_add_le _ _
              _ ≤ W+|a-S| := by linarith
          have hl : |a'-(a+z)| ≤ fp.u*|a|+(2*fp.u+fp.u^2)*|z| :=
            p41_fl_add_mul_forward fp a (x (Fin.last (m+1)))
              (y (Fin.last (m+1)))
          have hc := (p41_gamma_coeffs fp.u (m+1) fp.u_nonneg hv).2
          have hc1 : g+(g+1)*fp.u ≤ G := hc
          have hv1 : P41GammaValid fp.u 1 := by
            unfold P41GammaValid
            simp only [Nat.cast_one, one_mul]
            have hh : (1:ℝ) ≤ ((m+2:ℕ):ℝ) := by
              exact_mod_cast (by omega : 1 ≤ m+2)
            have hmul := mul_le_mul_of_nonneg_right hh fp.u_nonneg
            have hv' := hv
            unfold P41GammaValid at hv'
            have hc : ((m+2:ℕ):ℝ) = ((m+1+1:ℕ):ℝ) := by congr 1
            rw [← hc] at hv'
            linarith
          have hgu : fp.u ≤ g :=
            (p41_u_le_gamma_one fp.u fp.u_nonneg hv1).trans
              (p41_gamma_mono fp.u 1 (m+1) fp.u_nonneg (by omega) hvm)
          have hc2 : 2*fp.u+fp.u^2 ≤ G := by
            have hnon := fp.u_nonneg
            have hh : 2*fp.u+fp.u^2 ≤ g+(g+1)*fp.u := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hgu)
                (by linarith : 0 ≤ 1+fp.u)]
            exact hh.trans hc1
          have hW : 0 ≤ W := Finset.sum_nonneg (fun i hi => abs_nonneg _)
          have hmulsize := mul_le_mul_of_nonneg_left hsize fp.u_nonneg
          have hmid : |a'-(S+z)| ≤ (g+(g+1)*fp.u)*W+
              (2*fp.u+fp.u^2)*|z| := by
            have heq : a'-(S+z) = (a-S)+(a'-(a+z)) := by ring
            have htri := abs_add_le (a-S) (a'-(a+z))
            have hmulerr := mul_le_mul_of_nonneg_left hi fp.u_nonneg
            calc
              |a'-(S+z)| = |(a-S)+(a'-(a+z))| := congrArg abs heq
              _ ≤ |a-S|+|a'-(a+z)| := htri
              _ ≤ (g+(g+1)*fp.u)*W+(2*fp.u+fp.u^2)*|z| := by
                nlinarith
          have hh1 := mul_le_mul_of_nonneg_right hc1 hW
          have hh2 := mul_le_mul_of_nonneg_right hc2 (abs_nonneg z)
          have hfinal : |a'-(S+z)| ≤ G*(W+|z|) := by nlinarith
          have hdot : p41RoundedDotProduct fp (m+2) x y = a' :=
            p41_dot_step fp m x y
          have hsum : (∑ i : Fin (m+2), x i*y i) = S+z :=
            Fin.sum_univ_castSucc _
          have habs : (∑ i : Fin (m+2), |x i*y i|) = W+|z| :=
            Fin.sum_univ_castSucc _
          rw [hdot, hsum, habs]
          exact hfinal

private lemma p41_fin_sum_split {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i +
        (∑ t : Fin (n-i.val-1), f ⟨i.val+1+t.val, by omega⟩) := by
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j,h⟩ else 0
  have htotal : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := by
    rw [← Fin.sum_univ_eq_sum_range g n]
    apply Finset.sum_congr rfl
    intro j hj
    simp [g]
  have hlow : (∑ j ∈ Finset.range i.val, g j) =
      ∑ t : Fin i.val, f ⟨t.val, by omega⟩ := by
    rw [← Fin.sum_univ_eq_sum_range g i.val]
    apply Finset.sum_congr rfl
    intro t ht
    simp [g, show t.val < n by omega]
  have hupp : (∑ j ∈ Finset.range (n-i.val-1), g (i.val+1+j)) =
      ∑ t : Fin (n-i.val-1), f ⟨i.val+1+t.val, by omega⟩ := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => g (i.val+1+j)) (n-i.val-1)]
    apply Finset.sum_congr rfl
    intro t ht
    simp [g, show i.val+1+t.val < n by omega]
  have hmid : g i.val = f i := by simp [g, i.isLt]
  have hn : n = (i.val+1)+(n-i.val-1) := by omega
  calc
    (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := htotal
    _ = ∑ j ∈ Finset.range (i.val+1), g j +
          ∑ j ∈ Finset.range (n-i.val-1), g (i.val+1+j) := by
            simpa only [← hn] using
              (Finset.sum_range_add g (i.val+1) (n-i.val-1))
    _ = (∑ j ∈ Finset.range i.val, g j) + g i.val +
          ∑ j ∈ Finset.range (n-i.val-1), g (i.val+1+j) := by
            rw [Finset.sum_range_succ]
    _ = (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i +
          (∑ t : Fin (n-i.val-1), f ⟨i.val+1+t.val, by omega⟩) := by
            rw [hlow, hmid, hupp]

private lemma p41_fin_sum_lower {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hz : ∀ j, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  rw [p41_fin_sum_split i f]
  have hh : (∑ t : Fin (n-i.val-1), f ⟨i.val+1+t.val, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    apply hz
    dsimp
    omega
  rw [hh, add_zero]

private lemma p41_fin_sum_upper {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hz : ∀ j, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      (∑ t : Fin (n-i.val-1), f ⟨i.val+1+t.val, by omega⟩) := by
  rw [p41_fin_sum_split i f]
  have hh : (∑ t : Fin i.val, f ⟨t.val, by omega⟩) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    apply hz
    exact t.isLt
  rw [hh, zero_add]

private lemma p41_forward_stable (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n-k → p41ForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n-k-1, by omega⟩
      let count := n-k-1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hstep : p41ForwardSubSteps fp n L b (k+1) hk x i =
          p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' i := by rfl
      rw [hstep]
      have hkeep : x' i = x i := by
        exact Function.update_of_ne
          (Fin.ne_of_val_ne (by dsimp [ik]; omega)) _ _
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega), hkeep]

private lemma p41_forward_steps_residual (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hv : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n-k ≤ i.val →
      let y := p41ForwardSubSteps fp n L b k hk x
      |b i - ∑ j : Fin n, L i j*y j| ≤
        p41Gamma fp.u n * ∑ j : Fin n, |L i j*y j| := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      exfalso
      exact (not_lt_of_ge hi) i.isLt
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n-k-1, by omega⟩
      let count := n-k-1
      let lower : Fin count → Fin n := fun t => ⟨t.val, by omega⟩
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc (fp.fl_mul (L ik (lower t)) (x (lower t)))) (b ik)
      let v := fp.fl_div s (L ik ik)
      let x' : Fin n → ℝ := Function.update x ik v
      let y := p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hstep : p41ForwardSubSteps fp n L b (k+1) hk x = y := by rfl
      rw [hstep]
      by_cases hlate : n-k ≤ i.val
      · exact ih (Nat.le_of_succ_le hk) x' i hlate
      · have hii : i = ik := Fin.ext (by dsimp [ik]; omega)
        rw [hii]
        have hcount : count+1 ≤ n := by dsimp [count]; omega
        have hvalidcount : P41GammaValid fp.u (count+1) := by
          unfold P41GammaValid at *
          have hc : ((count+1:ℕ):ℝ)*fp.u ≤ (n:ℝ)*fp.u := by
            apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
            exact_mod_cast hcount
          linarith
        have hscalar : |b ik - L ik ik*v -
            (∑ t : Fin count, L ik (lower t)*x (lower t))| ≤
            p41Gamma fp.u (count+1)*
              (|L ik ik*v|+
                ∑ t : Fin count, |L ik (lower t)*x (lower t)|) :=
          p41_sub_div_back fp count (fun t => L ik (lower t))
            (fun t => x (lower t)) (b ik) (L ik ik) (hdiag ik) hvalidcount
        have hyi : y ik = v := by
          change p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' ik = v
          rw [p41_forward_stable fp n L b k (Nat.le_of_succ_le hk) x' ik (by
            dsimp [ik]; omega)]
          exact Function.update_self ik v x
        have hylow (t : Fin count) : y (lower t) = x (lower t) := by
          change p41ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
            (lower t) = x (lower t)
          rw [p41_forward_stable fp n L b k (Nat.le_of_succ_le hk) x' (lower t) (by
            dsimp [lower, count]; omega)]
          exact Function.update_of_ne
            (Fin.ne_of_val_ne (by dsimp [lower, ik, count]; omega)) _ _
        have hsum : (∑ j : Fin n, L ik j*y j) =
            (∑ t : Fin count, L ik (lower t)*x (lower t)) + L ik ik*v := by
          have hh := p41_fin_sum_lower ik (fun j => L ik j*y j) (by
            intro j hj
            simp [hupper ik j hj])
          have hc : count = ik.val := by dsimp [count, ik]
          rw [hh]
          congr 1
          · apply Finset.sum_congr rfl
            intro t ht
            exact congrArg (fun z => L ik (lower t)*z) (hylow t)
          · exact congrArg (fun z => L ik ik*z) hyi
        have habs : (∑ j : Fin n, |L ik j*y j|) =
            (∑ t : Fin count, |L ik (lower t)*x (lower t)|) + |L ik ik*v| := by
          have hh := p41_fin_sum_lower ik (fun j => |L ik j*y j|) (by
            intro j hj
            simp [hupper ik j hj])
          rw [hh]
          congr 1
          · apply Finset.sum_congr rfl
            intro t ht
            exact congrArg (fun z => |L ik (lower t)*z|) (hylow t)
          · exact congrArg (fun z => |L ik ik*z|) hyi
        have hgam := p41_gamma_mono fp.u (count+1) n fp.u_nonneg hcount hv
        have hnon : 0 ≤ |L ik ik*v|+
            ∑ t : Fin count, |L ik (lower t)*x (lower t)| := by
          positivity
        have hprod := mul_le_mul_of_nonneg_right hgam hnon
        change |b ik - ∑ j : Fin n, L ik j*y j| ≤
          p41Gamma fp.u n * ∑ j : Fin n, |L ik j*y j|
        rw [hsum, habs]
        calc
          |b ik - ((∑ t : Fin count, L ik (lower t)*x (lower t)) +
              L ik ik*v)| =
            |b ik - L ik ik*v -
              (∑ t : Fin count, L ik (lower t)*x (lower t))| := by
                congr 1
                ring
          _ ≤ p41Gamma fp.u (count+1) *
            (|L ik ik*v| + ∑ t : Fin count, |L ik (lower t)*x (lower t)|) := hscalar
          _ ≤ p41Gamma fp.u n *
            (|L ik ik*v| + ∑ t : Fin count, |L ik (lower t)*x (lower t)|) := hprod
          _ = p41Gamma fp.u n *
            ((∑ t : Fin count, |L ik (lower t)*x (lower t)|)+|L ik ik*v|) := by ring

private lemma p41_forward_residual (fp : P41FPModel) (n : ℕ)
    (L : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hupper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hv : P41GammaValid fp.u n) (i : Fin n) :
    let y := p41ForwardSub fp n L b
    |b i - ∑ j : Fin n, L i j*y j| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |L i j*y j| := by
  exact p41_forward_steps_residual fp n L b hdiag hupper hv n (le_refl n)
    (fun _ => 0) i (by omega)

private lemma p41_back_stable (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      k ≤ i.val → p41BackSubSteps fp n U b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨k, hk⟩
      let count := n-k-1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k+1+t.val, by omega⟩)
              (x ⟨k+1+t.val, by omega⟩))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hstep : p41BackSubSteps fp n U b (k+1) hk x i =
          p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' i := by rfl
      rw [hstep]
      have hkeep : x' i = x i := by
        exact Function.update_of_ne
          (Fin.ne_of_val_ne (by dsimp [ik]; omega)) _ _
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega), hkeep]

private lemma p41_back_steps_residual (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hlower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hv : P41GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < k →
      let y := p41BackSubSteps fp n U b k hk x
      |b i - ∑ j : Fin n, U i j*y j| ≤
        p41Gamma fp.u n * ∑ j : Fin n, |U i j*y j| := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨k, hk⟩
      let count := n-k-1
      let upper : Fin count → Fin n := fun t => ⟨k+1+t.val, by omega⟩
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc (fp.fl_mul (U ik (upper t)) (x (upper t)))) (b ik)
      let v := fp.fl_div s (U ik ik)
      let x' : Fin n → ℝ := Function.update x ik v
      let y := p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      have hstep : p41BackSubSteps fp n U b (k+1) hk x = y := by rfl
      rw [hstep]
      by_cases hearly : i.val < k
      · exact ih (Nat.le_of_succ_le hk) x' i hearly
      · have hii : i = ik := Fin.ext (by dsimp [ik]; omega)
        rw [hii]
        have hcount : count+1 ≤ n := by dsimp [count]; omega
        have hvalidcount : P41GammaValid fp.u (count+1) := by
          unfold P41GammaValid at *
          have hc : ((count+1:ℕ):ℝ)*fp.u ≤ (n:ℝ)*fp.u := by
            apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
            exact_mod_cast hcount
          linarith
        have hscalar : |b ik - U ik ik*v -
            (∑ t : Fin count, U ik (upper t)*x (upper t))| ≤
            p41Gamma fp.u (count+1)*
              (|U ik ik*v|+
                ∑ t : Fin count, |U ik (upper t)*x (upper t)|) :=
          p41_sub_div_back fp count (fun t => U ik (upper t))
            (fun t => x (upper t)) (b ik) (U ik ik) (hdiag ik) hvalidcount
        have hyi : y ik = v := by
          change p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' ik = v
          rw [p41_back_stable fp n U b k (Nat.le_of_succ_le hk) x' ik (by
            dsimp [ik]; omega)]
          exact Function.update_self ik v x
        have hyupp (t : Fin count) : y (upper t) = x (upper t) := by
          change p41BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
            (upper t) = x (upper t)
          rw [p41_back_stable fp n U b k (Nat.le_of_succ_le hk) x' (upper t) (by
            dsimp [upper]; omega)]
          exact Function.update_of_ne
            (Fin.ne_of_val_ne (by dsimp [upper, ik, count]; omega)) _ _
        have hsum : (∑ j : Fin n, U ik j*y j) =
            U ik ik*v + (∑ t : Fin count, U ik (upper t)*x (upper t)) := by
          have hh := p41_fin_sum_upper ik (fun j => U ik j*y j) (by
            intro j hj
            simp [hlower ik j hj])
          rw [hh]
          congr 1
          · exact congrArg (fun z => U ik ik*z) hyi
          · apply Finset.sum_congr rfl
            intro t ht
            exact congrArg (fun z => U ik (upper t)*z) (hyupp t)
        have habs : (∑ j : Fin n, |U ik j*y j|) =
            |U ik ik*v| + (∑ t : Fin count, |U ik (upper t)*x (upper t)|) := by
          have hh := p41_fin_sum_upper ik (fun j => |U ik j*y j|) (by
            intro j hj
            simp [hlower ik j hj])
          rw [hh]
          congr 1
          · exact congrArg (fun z => |U ik ik*z|) hyi
          · apply Finset.sum_congr rfl
            intro t ht
            exact congrArg (fun z => |U ik (upper t)*z|) (hyupp t)
        have hgam := p41_gamma_mono fp.u (count+1) n fp.u_nonneg hcount hv
        have hnon : 0 ≤ |U ik ik*v|+
            ∑ t : Fin count, |U ik (upper t)*x (upper t)| := by
          positivity
        have hprod := mul_le_mul_of_nonneg_right hgam hnon
        change |b ik - ∑ j : Fin n, U ik j*y j| ≤
          p41Gamma fp.u n * ∑ j : Fin n, |U ik j*y j|
        rw [hsum, habs]
        calc
          |b ik - (U ik ik*v +
              (∑ t : Fin count, U ik (upper t)*x (upper t)))| =
            |b ik - U ik ik*v -
              (∑ t : Fin count, U ik (upper t)*x (upper t))| := by
                congr 1
                ring
          _ ≤ p41Gamma fp.u (count+1) *
            (|U ik ik*v| + ∑ t : Fin count, |U ik (upper t)*x (upper t)|) := hscalar
          _ ≤ p41Gamma fp.u n *
            (|U ik ik*v| + ∑ t : Fin count, |U ik (upper t)*x (upper t)|) := hprod

private lemma p41_back_residual (fp : P41FPModel) (n : ℕ)
    (U : P41Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hlower : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hv : P41GammaValid fp.u n) (i : Fin n) :
    let y := p41BackSub fp n U b
    |b i - ∑ j : Fin n, U i j*y j| ≤
      p41Gamma fp.u n * ∑ j : Fin n, |U i j*y j| := by
  exact p41_back_steps_residual fp n U b hdiag hlower hv n (le_refl n)
    (fun _ => 0) i i.isLt

private lemma p41_sum_assoc (n : ℕ) (a : Fin n → ℝ)
    (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ j : Fin n, (∑ k : Fin n, a k*B k j)*x j) =
      ∑ k : Fin n, a k*(∑ j : Fin n, B k j*x j) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p41_lu_solve_row_bound (fp : P41FPModel) (n : ℕ)
    (A L U : P41Matrix n n) (b : Fin n → ℝ)
    (hc : P41LUCertificate fp n A L U)
    (hUdiag : ∀ i : Fin n, U i i ≠ 0)
    (hv : P41GammaValid fp.u n) (i : Fin n) :
    let x := p41LUSolve fp n L U b
    |(∑ j : Fin n, A i j*x j)-b i| ≤
      (3*p41Gamma fp.u n+p41Gamma fp.u n^2)*
        ∑ j : Fin n, (∑ k : Fin n, |L i k| *|U k j|)*|x j| := by
  let y := p41ForwardSub fp n L b
  let x := p41LUSolve fp n L U b
  let g := p41Gamma fp.u n
  let C : Fin n → ℝ := fun j => ∑ k : Fin n, |L i k| *|U k j|
  let Z : Fin n → ℝ := fun k => ∑ j : Fin n, |U k j| *|x j|
  let W := ∑ j : Fin n, C j*|x j|
  have hg : 0 ≤ g := p41_gamma_nonneg fp.u n fp.u_nonneg hv
  have hZ (k : Fin n) : 0 ≤ Z k := Finset.sum_nonneg (by
    intro j hj
    exact mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hW : 0 ≤ W := Finset.sum_nonneg (by
    intro j hj
    apply mul_nonneg
    · exact Finset.sum_nonneg (by intro k hk; positivity)
    · exact abs_nonneg _)
  have hWassoc : W = ∑ k : Fin n, |L i k| *Z k :=
    p41_sum_assoc n (fun k => |L i k|) (fun k j => |U k j|) (fun j => |x j|)
  have hb (k : Fin n) :
      |y k - ∑ j : Fin n, U k j*x j| ≤ g*Z k := by
    simpa only [abs_mul] using
      (p41_back_residual fp n U y hUdiag hc.U_lower_zero hv k)
  have hf : |b i - ∑ k : Fin n, L i k*y k| ≤
      g*(∑ k : Fin n, |L i k| *|y k|) := by
    simpa only [abs_mul] using
      (p41_forward_residual fp n L b (by
        intro j
        rw [hc.L_diag j]
        norm_num) hc.L_upper_zero hv i)
  have hY (k : Fin n) : |y k| ≤ (1+g)*Z k := by
    have huabs : |∑ j : Fin n, U k j*x j| ≤ Z k := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (fun j : Fin n => U k j*x j) Finset.univ)
    have htri : |y k| ≤ |y k - ∑ j : Fin n, U k j*x j| +
        |∑ j : Fin n, U k j*x j| := by
      have heq : y k = (y k - ∑ j : Fin n, U k j*x j) +
          (∑ j : Fin n, U k j*x j) := by ring
      calc
        |y k| = |(y k - ∑ j : Fin n, U k j*x j) +
          (∑ j : Fin n, U k j*x j)| := congrArg abs heq
        _ ≤ |y k - ∑ j : Fin n, U k j*x j| +
          |∑ j : Fin n, U k j*x j| := abs_add_le _ _
    nlinarith [hb k, hZ k]
  let F := ∑ j : Fin n, (A i j - ∑ k : Fin n, L i k*U k j)*x j
  let E := ∑ k : Fin n, L i k*((∑ j : Fin n, U k j*x j)-y k)
  let H := (∑ k : Fin n, L i k*y k)-b i
  have hF : |F| ≤ g*W := by
    calc
      |F| ≤ ∑ j : Fin n, |(A i j - ∑ k : Fin n, L i k*U k j)*x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin n, |A i j - ∑ k : Fin n, L i k*U k j| *|x j| := by
        simp_rw [abs_mul]
      _ ≤ ∑ j : Fin n, (g*C j)*|x j| := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        simpa only [abs_sub_comm] using hc.backward_bound i j
      _ = g*W := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hE : |E| ≤ g*W := by
    calc
      |E| ≤ ∑ k : Fin n,
          |L i k*((∑ j : Fin n, U k j*x j)-y k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |L i k| *|y k - ∑ j : Fin n, U k j*x j| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [abs_mul, abs_sub_comm]
      _ ≤ ∑ k : Fin n, |L i k| *(g*Z k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hb k) (abs_nonneg _)
      _ = g*W := by
        rw [hWassoc]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hH : |H| ≤ g*((1+g)*W) := by
    have hYsum : (∑ k : Fin n, |L i k| *|y k|) ≤ (1+g)*W := by
      calc
        _ ≤ ∑ k : Fin n, |L i k| *((1+g)*Z k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (hY k) (abs_nonneg _)
        _ = (1+g)*W := by
          rw [hWassoc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    have hh := mul_le_mul_of_nonneg_left hYsum hg
    have hhf : |H| ≤ g*(∑ k : Fin n, |L i k| * |y k|) := by
      change |(∑ k : Fin n, L i k*y k)-b i| ≤
        g*(∑ k : Fin n, |L i k| * |y k|)
      rw [abs_sub_comm]
      exact hf
    exact hhf.trans hh
  have hdecomp : (∑ j : Fin n, A i j*x j)-b i = F+E+H := by
    dsimp [F, E, H]
    simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [p41_sum_assoc n (fun k => L i k) U x]
    ring
  change |(∑ j : Fin n, A i j*x j)-b i| ≤
    (3*g+g^2)*W
  calc
    |(∑ j : Fin n, A i j*x j)-b i| = |F+E+H| := congrArg abs hdecomp
    _ ≤ |F|+|E|+|H| := by
      have h1 := abs_add_le (F+E) H
      have h2 := abs_add_le F E
      linarith
    _ ≤ g*W+g*W+g*((1+g)*W) := by linarith
    _ = (3*g+g^2)*W := by ring

private noncomputable def p41_sign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private lemma p41_abs_sign (x : ℝ) : |p41_sign x| = 1 := by
  by_cases hx : 0 ≤ x
  · simp [p41_sign, hx]
  · simp [p41_sign, hx]

private lemma p41_sign_mul (x : ℝ) : p41_sign x*x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [p41_sign, hx, abs_of_nonneg hx]
  · have hneg : x < 0 := lt_of_not_ge hx
    simp [p41_sign, hx, abs_of_neg hneg]

private lemma p41_row_error_matrix (n : ℕ) (C : P41Matrix n n)
    (x r : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hC : ∀ i j, 0 ≤ C i j)
    (hr : ∀ i, |r i| ≤ c * ∑ j : Fin n, C i j*|x j|) :
    ∃ D : P41Matrix n n,
      (∀ i j, |D i j| ≤ c*C i j) ∧
      (∀ i, (∑ j : Fin n, D i j*x j) = r i) := by
  classical
  let S : Fin n → ℝ := fun i => ∑ j : Fin n, C i j*|x j|
  let D : P41Matrix n n := fun i j =>
    if S i = 0 then 0 else (r i/S i)*C i j*p41_sign (x j)
  refine ⟨D, ?_, ?_⟩
  · intro i j
    by_cases hzero : S i = 0
    · simp [D, hzero]
      exact mul_nonneg hc (hC i j)
    · have hSnon : 0 ≤ S i := Finset.sum_nonneg (by
        intro t ht
        exact mul_nonneg (hC i t) (abs_nonneg _))
      have hSpos : 0 < S i := lt_of_le_of_ne hSnon (Ne.symm hzero)
      have hα : |r i/S i| ≤ c := by
        rw [abs_div, abs_of_pos hSpos]
        exact (div_le_iff₀ hSpos).2 (hr i)
      simp only [D, hzero, ↓reduceIte, abs_mul, p41_abs_sign,
        mul_one, abs_of_nonneg (hC i j)]
      exact mul_le_mul_of_nonneg_right hα (hC i j)
  · intro i
    by_cases hzero : S i = 0
    · have hri : r i = 0 := by
        have hh' : |r i| ≤ c*S i := hr i
        have hh : |r i| ≤ 0 := by simpa only [hzero, mul_zero] using hh'
        exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
      simp [D, hzero, hri]
    · have hsum : (∑ j : Fin n, D i j*x j) =
          (r i/S i)*S i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [D, hzero, ↓reduceIte]
        calc
          (r i/S i*C i j*p41_sign (x j))*x j =
            (r i/S i*C i j)*(p41_sign (x j)*x j) := by ring
          _ = (r i/S i*C i j)*|x j| := by rw [p41_sign_mul]
          _ = (r i/S i)*(C i j*|x j|) := by ring
      rw [hsum]
      exact div_mul_cancel₀ (r i) hzero

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
  let g := p41Gamma fp.u n
  let c := 3*g+g^2
  let Cs : P41Matrix n n := fun i j =>
    ∑ k : Fin n, |Ls i k| *|Us k j|
  let Cn : P41Matrix n n := fun i j =>
    ∑ k : Fin n, |Ln i k| *|Un k j|
  let rs : Fin n → ℝ := fun i => uvec i - ∑ j : Fin n, Ase i j*gs j
  let rn : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Anw i j*gn j
  let dw : Fin n → ℝ := fun i => w i - ∑ j : Fin n, Ane i j*gs j
  have hg : 0 ≤ g := p41_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hc : 0 ≤ c := by dsimp [c]; nlinarith [sq_nonneg g]
  have hCs : ∀ i j, 0 ≤ Cs i j := by
    intro i j
    exact Finset.sum_nonneg (by intro k hk; positivity)
  have hCn : ∀ i j, 0 ≤ Cn i j := by
    intro i j
    exact Finset.sum_nonneg (by intro k hk; positivity)
  have hrs : ∀ i, |rs i| ≤ c*∑ j : Fin n, Cs i j*|gs j| := by
    intro i
    have hh := p41_lu_solve_row_bound fp n Ase Ls Us uvec hLs hUsdiag hvalid i
    change |(∑ j : Fin n, Ase i j*gs j)-uvec i| ≤
      c*∑ j : Fin n, Cs i j*|gs j| at hh
    simpa only [rs, abs_sub_comm] using hh
  have hrn : ∀ i, |rn i| ≤ c*∑ j : Fin n, Cn i j*|gn j| := by
    intro i
    have hh := p41_lu_solve_row_bound fp n Anw Ln Un w hLn hUndiag hvalid i
    change |(∑ j : Fin n, Anw i j*gn j)-w i| ≤
      c*∑ j : Fin n, Cn i j*|gn j| at hh
    simpa only [rn, abs_sub_comm] using hh
  obtain ⟨Ds, hDs, hDsSum⟩ :=
    p41_row_error_matrix n Cs gs rs c hc hCs hrs
  obtain ⟨Dn, hDn, hDnSum⟩ :=
    p41_row_error_matrix n Cn gn rn c hc hCn hrn
  have hdw : ∀ i, |dw i| ≤ g*∑ j : Fin n, |Ane i j| *|gs j| := by
    intro i
    have hh := p41_rounded_dot_bound fp n (Ane i) gs hvalid
    change |w i - ∑ j : Fin n, Ane i j*gs j| ≤
      g*∑ j : Fin n, |Ane i j*gs j| at hh
    simpa only [dw, abs_mul] using hh
  refine ⟨Ds, Dn, dw, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hDs i j
  · intro i j
    exact hDn i j
  · exact hdw
  · intro i
    constructor
    · have hh := hDsSum i
      dsimp [rs] at hh
      linarith
    · have hh := hDnSum i
      dsimp [rn, dw] at *
      linarith

end VSCLReuse


import VSCLReuse.P08.Definitions

namespace VSCLReuse

open scoped BigOperators Matrix.Norms.Frobenius

private theorem p08_rect_norm_eq_frobenius {m n : ℕ}
    (A : P08RectMatrix m n) : p08RectFrobNorm A = ‖A‖ := by
  rw [p08RectFrobNorm, Matrix.frobenius_norm_def]
  simp_rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [Real.sqrt_eq_rpow]

private theorem p08_rect_norm_entrywise {m n : ℕ}
    (A E : P08RectMatrix m n) {k : ℝ}
    (hk : 0 ≤ k) (h : ∀ i j, |E i j| ≤ k * |A i j|) :
    p08RectFrobNorm E ≤ k * p08RectFrobNorm A := by
  have hs : (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
      k ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hsq : (E i j) ^ 2 ≤ (k * |A i j|) ^ 2 := by
      apply sq_le_sq.mpr
      simpa [abs_mul, abs_of_nonneg hk] using h i j
    nlinarith [sq_abs (A i j)]
  unfold p08RectFrobNorm
  calc
    Real.sqrt (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
        Real.sqrt (k ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
      Real.sqrt_le_sqrt hs
    _ = k * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq_eq_abs, abs_of_nonneg hk]

private theorem p08_gamma_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u)
    (hvalid : k * u < 1) : 0 ≤ p08GammaReal k u := by
  unfold p08GammaReal
  exact div_nonneg (mul_nonneg hk hu) (by linarith)

private theorem p08_gamma_mul_bound {a b u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u)
    (hvalid : (a + b) * u < 1) :
    p08GammaReal a u + p08GammaReal b u +
      p08GammaReal a u * p08GammaReal b u ≤
        p08GammaReal (a + b) u := by
  have hau : 0 ≤ a * u := mul_nonneg ha hu
  have hbu : 0 ≤ b * u := mul_nonneg hb hu
  have ha1 : 0 < 1 - a * u := by nlinarith
  have hb1 : 0 < 1 - b * u := by nlinarith
  have hab1 : 0 < 1 - (a + b) * u := by linarith
  have ha1' : 1 - u * a ≠ 0 := by nlinarith [ha1]
  have hb1' : 1 - u * b ≠ 0 := by nlinarith [hb1]
  unfold p08GammaReal
  have hid : a * u / (1 - a * u) + b * u / (1 - b * u) +
      a * u / (1 - a * u) * (b * u / (1 - b * u)) =
      ((a + b) * u - a * b * u ^ 2) /
        ((1 - a * u) * (1 - b * u)) := by
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ha1', hb1']
    ring
  rw [hid]
  apply (div_le_div_iff₀ (mul_pos ha1 hb1) hab1).2
  ring_nf
  nlinarith [mul_nonneg hau hbu]

private theorem p08_gamma_mono {a b u : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : 0 ≤ u)
    (hvalid : b * u < 1) :
    p08GammaReal a u ≤ p08GammaReal b u := by
  have hau : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
  have ha1 : 0 < 1 - a * u := by linarith
  have hb1 : 0 < 1 - b * u := by linarith
  unfold p08GammaReal
  apply (div_le_div_iff₀ ha1 hb1).2
  nlinarith

private theorem p08_gamma_compose_error {a u e δ : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hvalid : (a + 1) * u < 1)
    (he : |e| ≤ p08GammaReal a u) (hδ : |δ| ≤ u) :
    |(1 + e) * (1 + δ) - 1| ≤ p08GammaReal (a + 1) u := by
  have ha_valid : a * u < 1 := by nlinarith
  have hγ : 0 ≤ p08GammaReal a u := p08_gamma_nonneg ha hu ha_valid
  have hγ1 : p08GammaReal a u + u + p08GammaReal a u * u ≤
      p08GammaReal (a + 1) u := by
    have h := p08_gamma_mul_bound ha (by norm_num : (0:ℝ) ≤ 1) hu hvalid
    have hu_le_gamma : u ≤ p08GammaReal 1 u := by
      unfold p08GammaReal
      have h1 : 0 < 1 - u := by nlinarith
      simp only [one_mul]
      apply (le_div_iff₀ h1).2
      nlinarith [mul_nonneg hu hu]
    have hγu : p08GammaReal a u * u ≤
        p08GammaReal a u * p08GammaReal 1 u :=
      mul_le_mul_of_nonneg_left hu_le_gamma hγ
    nlinarith
  calc
    |(1 + e) * (1 + δ) - 1| = |e + δ + e * δ| := by ring
    _ ≤ |e| + |δ| + |e * δ| := by
      calc
        |e + δ + e * δ| ≤ |e + δ| + |e * δ| := abs_add_le _ _
        _ ≤ |e| + |δ| + |e * δ| := by linarith [abs_add_le e δ]
    _ ≤ p08GammaReal a u + u + p08GammaReal a u * u := by
      rw [abs_mul]
      have hmul : |e| * |δ| ≤ p08GammaReal a u * u := by
        exact mul_le_mul he hδ (abs_nonneg _) hγ
      linarith
    _ ≤ _ := hγ1

private theorem p08_gamma_scale_bound {a s u : ℝ}
    (ha : 0 ≤ a) (hs : 0 ≤ s) (has : a ≤ a * s)
    (hu : 0 ≤ u) (hvalid : (a * s) * u < 1) :
    p08GammaReal a u * s ≤ p08GammaReal (a * s) u := by
  have hnum : 0 ≤ a * u * s := mul_nonneg (mul_nonneg ha hu) hs
  have ha1 : 0 < 1 - a * u := by nlinarith [mul_le_mul_of_nonneg_right has hu]
  have has1 : 0 < 1 - a * s * u := by linarith
  unfold p08GammaReal
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ ha1 has1).2
  nlinarith [mul_le_mul_of_nonneg_right has hu]

private theorem p08_nat_le_mul_sqrt (r : ℕ) :
    (r : ℝ) ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by
  cases r with
  | zero => simp
  | succ r =>
      have h1 : (1 : ℝ) ≤ (↑(r + 1) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
      have hs : (1 : ℝ) ≤ Real.sqrt (↑(r + 1) : ℝ) := Real.one_le_sqrt.mpr h1
      nlinarith [mul_nonneg (show (0:ℝ) ≤ ↑(r + 1) by positivity) (sub_nonneg.mpr hs)]

private theorem p08_gamma_inverse_compose {a u q δ : ℝ}
    (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hvalid : (a + 1) * u < 1)
    (hq : |q - 1| ≤ p08GammaReal a u) (hδ : |δ| ≤ u) :
    |q / (1 + δ) - 1| ≤ p08GammaReal (a + 1) u := by
  have hu1 : 0 < 1 - u := by nlinarith
  have hden : 0 < 1 + δ := by
    have := (abs_le.mp hδ).1
    linarith
  have hγ : 0 ≤ p08GammaReal a u :=
    p08_gamma_nonneg ha hu (by nlinarith [mul_nonneg ha hu])
  have hnum : |q - 1 - δ| ≤ p08GammaReal a u + u := by
    calc
      |q - 1 - δ| ≤ |q - 1| + |δ| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (q - 1) (-δ)
      _ ≤ _ := add_le_add hq hδ
  have hquot : |q / (1 + δ) - 1| ≤
      (p08GammaReal a u + u) / (1 - u) := by
    have hid : q / (1 + δ) - 1 = (q - 1 - δ) / (1 + δ) := by
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hden]
    apply (div_le_div_iff₀ hden hu1).2
    have hden_le : 1 - u ≤ 1 + δ := by linarith [(abs_le.mp hδ).1]
    calc
      |q - 1 - δ| * (1 - u) ≤
          (p08GammaReal a u + u) * (1 - u) :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt hu1)
      _ ≤ (p08GammaReal a u + u) * (1 + δ) :=
        mul_le_mul_of_nonneg_left hden_le (add_nonneg hγ hu)
  have hγcomp : (p08GammaReal a u + u) / (1 - u) ≤
      p08GammaReal (a + 1) u := by
    have h := p08_gamma_mul_bound ha (by norm_num : (0:ℝ) ≤ 1) hu hvalid
    have hident : (p08GammaReal a u + u) / (1 - u) =
        p08GammaReal a u + p08GammaReal 1 u +
          p08GammaReal a u * p08GammaReal 1 u := by
      unfold p08GammaReal
      simp only [one_mul]
      field_simp
      ring
    rw [hident]
    simpa using h
  exact hquot.trans hγcomp

private theorem p08_rounded_dot_eq_fold (fp : StandardFPModel) (n : ℕ)
    (a x : Fin n → ℝ) :
    roundedDotProduct fp n a x =
      Fin.foldl n (fun acc j => fp.fl_add acc (fp.fl_mul (a j) (x j))) 0 := by
  cases n with
  | zero => simp [roundedDotProduct]
  | succ n =>
      simp only [roundedDotProduct, Fin.foldl_succ]
      rw [fp.fl_add_zero]

private theorem p08_rounded_dot_backward (fp : StandardFPModel) :
    ∀ (n : ℕ) (a x : Fin n → ℝ), (n : ℝ) * fp.u < 1 →
      ∃ e : Fin n → ℝ,
        (∀ j, |e j| ≤ p08GammaReal (n : ℝ) fp.u) ∧
        roundedDotProduct fp n a x =
          ∑ j : Fin n, a j * x j * (1 + e j) := by
  intro n
  induction n with
  | zero =>
      intro a x _
      refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
      · intro j; exact Fin.elim0 j
      · simp [roundedDotProduct]
  | succ n ih =>
      intro a x hvalid
      by_cases hn : n = 0
      · subst n
        obtain ⟨δ, hδ, hm⟩ := fp.model_mul (a 0) (x 0)
        refine ⟨fun _ => δ, ?_, ?_⟩
        · intro j
          have hδ' : |(1 + (0 : ℝ)) * (1 + δ) - 1| ≤
              p08GammaReal ((0 : ℝ) + 1) fp.u :=
            p08_gamma_compose_error (by norm_num) fp.u_nonneg (by simpa using hvalid)
              (by simp [p08GammaReal]) hδ
          simpa using hδ'
        · simp [roundedDotProduct, Fin.foldl_zero, hm]
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hvalid' : ((n : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
        have hprev : (n : ℝ) * fp.u < 1 := by nlinarith [fp.u_nonneg]
        let a' : Fin n → ℝ := fun j => a j.castSucc
        let x' : Fin n → ℝ := fun j => x j.castSucc
        obtain ⟨e, he, hsum⟩ := ih a' x' hprev
        let s := Fin.foldl n
          (fun acc j => fp.fl_add acc (fp.fl_mul (a j.castSucc) (x j.castSucc))) 0
        have hs : s = ∑ j : Fin n, a j.castSucc * x j.castSucc * (1 + e j) := by
          simpa [s, a', x', p08_rounded_dot_eq_fold] using hsum
        obtain ⟨δm, hδm, hm⟩ := fp.model_mul (a (Fin.last n)) (x (Fin.last n))
        obtain ⟨δa, hδa, ha⟩ := fp.model_add s
          (fp.fl_mul (a (Fin.last n)) (x (Fin.last n)))
        let E : Fin (n + 1) → ℝ :=
          Fin.snoc (fun j => (1 + e j) * (1 + δa) - 1)
            ((1 + δm) * (1 + δa) - 1)
        refine ⟨E, ?_, ?_⟩
        · intro j
          refine Fin.lastCases ?_ (fun k => ?_) j
          · have h2 : ((1 : ℝ) + 1) * fp.u < 1 := by
              have hnonneg : 0 ≤ ((n : ℝ) - 1) * fp.u :=
                mul_nonneg (by linarith) fp.u_nonneg
              nlinarith [hvalid']
            have hu_gamma : |δm| ≤ p08GammaReal 1 fp.u := by
              have h := p08_gamma_compose_error (a := 0) (u := fp.u)
                (e := 0) (δ := δm) (by norm_num) fp.u_nonneg
                (by nlinarith [h2]) (by simp [p08GammaReal]) hδm
              simpa using h
            have hcomp := p08_gamma_compose_error (a := 1) (u := fp.u)
              (e := δm) (δ := δa) (by norm_num) fp.u_nonneg h2 hu_gamma hδa
            have hmono : p08GammaReal 2 fp.u ≤
                p08GammaReal ((n + 1 : ℕ) : ℝ) fp.u := by
              apply p08_gamma_mono (by norm_num) (by exact_mod_cast (Nat.succ_le_succ hn_pos))
                fp.u_nonneg
              simpa using hvalid
            have hcomp' : |(1 + δm) * (1 + δa) - 1| ≤
                p08GammaReal 2 fp.u := by
              convert hcomp using 1 <;> norm_num
            simpa [E] using le_trans hcomp' hmono
          · have hcomp := p08_gamma_compose_error (a := (n : ℝ))
              (u := fp.u) (e := e k) (δ := δa)
              (by positivity) fp.u_nonneg (by simpa using hvalid) (he k) hδa
            simpa [E] using hcomp
        · rw [p08_rounded_dot_eq_fold, Fin.foldl_succ_last]
          change fp.fl_add s (fp.fl_mul (a (Fin.last n)) (x (Fin.last n))) = _
          rw [ha, hm, hs, Fin.sum_univ_castSucc]
          simp only [E, Fin.snoc_castSucc, Fin.snoc_last]
          rw [add_mul, Finset.sum_mul]
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            ring
          · ring

private theorem p08_rounded_rect_matvec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P08RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ E : P08RectMatrix m n,
      p08RectFrobNorm E ≤ p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm A ∧
      p08RoundedRectMatVec fp A x = p08RectMatVec (A + E) x := by
  classical
  let hw (i : Fin m) := p08_rounded_dot_backward fp n (A i) x hvalid
  let e (i : Fin m) : Fin n → ℝ := Classical.choose (hw i)
  have he (i : Fin m) : ∀ j, |e i j| ≤ p08GammaReal (n : ℝ) fp.u :=
    (Classical.choose_spec (hw i)).1
  have hsum (i : Fin m) : roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, A i j * x j * (1 + e i j) :=
    (Classical.choose_spec (hw i)).2
  let E : P08RectMatrix m n := fun i j => A i j * e i j
  refine ⟨E, ?_, ?_⟩
  · apply p08_rect_norm_entrywise A E
      (p08_gamma_nonneg (by positivity) fp.u_nonneg hvalid)
    intro i j
    simpa [E, abs_mul, mul_comm] using
      mul_le_mul_of_nonneg_left (he i j) (abs_nonneg (A i j))
  · funext i
    change roundedDotProduct fp n (A i) x =
      ∑ j : Fin n, (A i j + E i j) * x j
    rw [hsum i]
    apply Finset.sum_congr rfl
    intro j _
    simp only [E]
    ring

private theorem p08_orthonormal_mulVec_sq {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (z : Fin r → ℝ) :
    (∑ i : Fin b, (∑ j : Fin r, X i j * z j) ^ 2) =
      ∑ j : Fin r, (z j) ^ 2 := by
  calc
    (∑ i : Fin b, (∑ j : Fin r, X i j * z j) ^ 2) =
        ∑ i : Fin b, ∑ j : Fin r, ∑ k : Fin r,
          (X i j * z j) * (X i k * z k) := by
      simp_rw [sq, Fintype.sum_mul_sum]
    _ = ∑ j : Fin r, ∑ k : Fin r, ∑ i : Fin b,
          (X i j * z j) * (X i k * z k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Fin r, ∑ k : Fin r,
          (∑ i : Fin b, X i j * X i k) * z j * z k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j : Fin r, (z j) ^ 2 := by
      change (∀ j k, (∑ i : Fin b, X i j * X i k) = if j = k then 1 else 0) at hX
      simp_rw [hX]
      simp [sq]

private theorem p08_orthonormal_matmul_norm {b r n : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X)
    (B : P08RectMatrix r n) :
    p08RectFrobNorm (p08RectMatMul X B) = p08RectFrobNorm B := by
  unfold p08RectFrobNorm p08RectMatMul
  congr 1
  rw [Finset.sum_comm]
  simp_rw [p08_orthonormal_mulVec_sq X hX]
  rw [Finset.sum_comm]

private theorem p08_orthonormal_frob_norm {b r : ℕ}
    (X : P08RectMatrix b r) (hX : p08OrthonormalColumns X) :
    p08RectFrobNorm X = Real.sqrt (r : ℝ) := by
  unfold p08RectFrobNorm
  rw [Finset.sum_comm]
  have hcol (j : Fin r) : (∑ i : Fin b, X i j ^ 2) = 1 := by
    have h := hX j j
    simpa [p08OrthonormalColumns, sq] using h
  simp_rw [hcol]
  simp

private theorem p08_rect_norm_add {m n : ℕ}
    (A B : P08RectMatrix m n) :
    p08RectFrobNorm (A + B) ≤ p08RectFrobNorm A + p08RectFrobNorm B := by
  rw [p08_rect_norm_eq_frobenius, p08_rect_norm_eq_frobenius,
    p08_rect_norm_eq_frobenius]
  exact norm_add_le A B

private theorem p08_rect_norm_mul {m n q : ℕ}
    (A : P08RectMatrix m n) (B : P08RectMatrix n q) :
    p08RectFrobNorm (p08RectMatMul A B) ≤
      p08RectFrobNorm A * p08RectFrobNorm B := by
  rw [p08_rect_norm_eq_frobenius, p08_rect_norm_eq_frobenius,
    p08_rect_norm_eq_frobenius]
  exact Matrix.frobenius_norm_mul A B

private theorem p08_rect_norm_transpose {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm (p08RectTranspose A) = p08RectFrobNorm A := by
  rw [p08_rect_norm_eq_frobenius, p08_rect_norm_eq_frobenius]
  exact Matrix.frobenius_norm_transpose A

private theorem p08_lowrank_matvec_backward (fp : StandardFPModel)
    {b r : ℕ} (X Y : P08RectMatrix b r)
    (x : Fin b → ℝ) (hX : p08OrthonormalColumns X)
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) * fp.u < 1) :
    ∃ F : P08Matrix b,
      p08RectFrobNorm F ≤
        p08GammaReal ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)) fp.u *
          p08RectFrobNorm (p08LowRankMatrix X Y) ∧
      p08RoundedLowRankMatVec fp X Y x =
        p08RectMatVec (p08LowRankMatrix X Y + F) x := by
  let q : ℝ := (r : ℝ) * Real.sqrt (r : ℝ)
  let d : ℝ := (b : ℝ) + q
  have hq : 0 ≤ q := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hb : 0 ≤ (b : ℝ) := by positivity
  have hd : 0 ≤ d := add_nonneg hb hq
  have hvalid' : d * fp.u < 1 := by simpa [d, q] using hvalid
  have hvalid_b : (b : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hq fp.u_nonneg]
  have hvalid_q : q * fp.u < 1 := by
    nlinarith [mul_nonneg hb fp.u_nonneg]
  have hvalid_r : (r : ℝ) * fp.u < 1 := by
    nlinarith [mul_le_mul_of_nonneg_right (p08_nat_le_mul_sqrt r) fp.u_nonneg]
  let Yt : P08RectMatrix r b := p08RectTranspose Y
  obtain ⟨E1, hE1, hinner⟩ :=
    p08_rounded_rect_matvec_backward fp Yt x hvalid_b
  let z : Fin r → ℝ := p08RoundedRectMatVec fp Yt x
  obtain ⟨E2, hE2, houter⟩ :=
    p08_rounded_rect_matvec_backward fp X z hvalid_r
  let F : P08Matrix b := X * E1 + E2 * (Yt + E1)
  have hmat : (X + E2) * (Yt + E1) = p08LowRankMatrix X Y + F := by
    change (X + E2) * (Yt + E1) = X * Yt + (X * E1 + E2 * (Yt + E1))
    rw [Matrix.add_mul, Matrix.mul_add]
    abel
  have hresult : p08RoundedLowRankMatVec fp X Y x =
      p08RectMatVec (p08LowRankMatrix X Y + F) x := by
    change p08RoundedRectMatVec fp X z =
      p08RectMatVec (p08LowRankMatrix X Y + F) x
    rw [houter]
    dsimp [z]
    rw [hinner]
    change (X + E2).mulVec ((Yt + E1).mulVec x) =
      (p08LowRankMatrix X Y + F).mulVec x
    rw [Matrix.mulVec_mulVec, hmat]
  have hYt : p08RectFrobNorm Yt = p08RectFrobNorm Y :=
    p08_rect_norm_transpose Y
  have hT : p08RectFrobNorm (p08LowRankMatrix X Y) =
      p08RectFrobNorm Y := by
    change p08RectFrobNorm (p08RectMatMul X Yt) = p08RectFrobNorm Y
    rw [p08_orthonormal_matmul_norm X hX Yt, hYt]
  have hE1' : p08RectFrobNorm E1 ≤
      p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm Y := by
    simpa [hYt] using hE1
  have hE2' : p08RectFrobNorm E2 ≤ p08GammaReal q fp.u := by
    have hscale : p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) ≤
        p08GammaReal q fp.u := by
      apply p08_gamma_scale_bound (by positivity) (Real.sqrt_nonneg _)
        (p08_nat_le_mul_sqrt r) fp.u_nonneg
      simpa [q] using hvalid_q
    calc
      p08RectFrobNorm E2 ≤
          p08GammaReal (r : ℝ) fp.u * p08RectFrobNorm X := hE2
      _ = p08GammaReal (r : ℝ) fp.u * Real.sqrt (r : ℝ) := by
        rw [p08_orthonormal_frob_norm X hX]
      _ ≤ _ := hscale
  have hγb : 0 ≤ p08GammaReal (b : ℝ) fp.u :=
    p08_gamma_nonneg hb fp.u_nonneg hvalid_b
  have hγq : 0 ≤ p08GammaReal q fp.u :=
    p08_gamma_nonneg hq fp.u_nonneg hvalid_q
  have hYnonneg : 0 ≤ p08RectFrobNorm Y := Real.sqrt_nonneg _
  have hYplus : p08RectFrobNorm (Yt + E1) ≤
      (1 + p08GammaReal (b : ℝ) fp.u) * p08RectFrobNorm Y := by
    calc
      p08RectFrobNorm (Yt + E1) ≤
          p08RectFrobNorm Yt + p08RectFrobNorm E1 := p08_rect_norm_add Yt E1
      _ ≤ p08RectFrobNorm Y +
          p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm Y := by
        rw [hYt]
        exact add_le_add_right hE1' _
      _ = _ := by ring
  have hF : p08RectFrobNorm F ≤
      p08GammaReal d fp.u * p08RectFrobNorm Y := by
    have hmul : p08RectFrobNorm (E2 * (Yt + E1)) ≤
        p08GammaReal q fp.u *
          ((1 + p08GammaReal (b : ℝ) fp.u) * p08RectFrobNorm Y) := by
      calc
        p08RectFrobNorm (E2 * (Yt + E1)) ≤
            p08RectFrobNorm E2 * p08RectFrobNorm (Yt + E1) :=
          p08_rect_norm_mul E2 (Yt + E1)
        _ ≤ p08GammaReal q fp.u * p08RectFrobNorm (Yt + E1) :=
          mul_le_mul_of_nonneg_right hE2' (Real.sqrt_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hYplus hγq
    have hXE1 : p08RectFrobNorm (X * E1) = p08RectFrobNorm E1 :=
      p08_orthonormal_matmul_norm X hX E1
    have hcomb : p08GammaReal (b : ℝ) fp.u + p08GammaReal q fp.u +
        p08GammaReal (b : ℝ) fp.u * p08GammaReal q fp.u ≤
        p08GammaReal d fp.u := by
      simpa [d] using p08_gamma_mul_bound hb hq fp.u_nonneg hvalid'
    calc
      p08RectFrobNorm F ≤
          p08RectFrobNorm (X * E1) +
            p08RectFrobNorm (E2 * (Yt + E1)) := p08_rect_norm_add _ _
      _ ≤ p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm Y +
          p08GammaReal q fp.u *
            ((1 + p08GammaReal (b : ℝ) fp.u) * p08RectFrobNorm Y) := by
        rw [hXE1]
        exact add_le_add hE1' hmul
      _ ≤ p08GammaReal d fp.u * p08RectFrobNorm Y := by
        have := mul_le_mul_of_nonneg_right hcomb hYnonneg
        nlinarith
  refine ⟨F, ?_, hresult⟩
  simpa [d, q, hT] using hF

private theorem p08_fold_sub_backward (fp : StandardFPModel) :
    ∀ (k : ℕ) (v : ℝ) (a : Fin k → ℝ), (k : ℝ) * fp.u < 1 →
      ∃ e0 : ℝ, ∃ e : Fin k → ℝ,
        |e0| ≤ p08GammaReal (k : ℝ) fp.u ∧
        (∀ j, |e j| ≤ p08GammaReal (k : ℝ) fp.u) ∧
        Fin.foldl k (fun acc j => fp.fl_sub acc (a j)) v =
          v * (1 + e0) - ∑ j : Fin k, a j * (1 + e j) := by
  intro k
  induction k with
  | zero =>
      intro v a _
      refine ⟨0, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [p08GammaReal]
      · intro j; exact Fin.elim0 j
      · simp
  | succ k ih =>
      intro v a hvalid
      have hvalid' : ((k : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
      have hprev : (k : ℝ) * fp.u < 1 := by nlinarith [fp.u_nonneg]
      have hk : 0 ≤ (k : ℝ) := by positivity
      let a' : Fin k → ℝ := fun j => a j.castSucc
      obtain ⟨e0, e, he0, he, hsum⟩ := ih v a' hprev
      let s := Fin.foldl k (fun acc j => fp.fl_sub acc (a j.castSucc)) v
      have hs : s = v * (1 + e0) -
          ∑ j : Fin k, a j.castSucc * (1 + e j) := by
        simpa [s, a'] using hsum
      obtain ⟨δ, hδ, hfl⟩ := fp.model_sub s (a (Fin.last k))
      let e0' := (1 + e0) * (1 + δ) - 1
      let e' : Fin (k + 1) → ℝ :=
        Fin.snoc (fun j => (1 + e j) * (1 + δ) - 1) δ
      refine ⟨e0', e', ?_, ?_, ?_⟩
      · simpa [e0'] using
          (p08_gamma_compose_error hk fp.u_nonneg hvalid' he0 hδ)
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · have hγ : 0 ≤ p08GammaReal (k : ℝ) fp.u :=
            p08_gamma_nonneg hk fp.u_nonneg hprev
          have h := p08_gamma_compose_error (a := (k : ℝ))
            (u := fp.u) (e := 0) (δ := δ) hk fp.u_nonneg hvalid'
            (by simpa using hγ) hδ
          simpa [e'] using h
        · have h := p08_gamma_compose_error hk fp.u_nonneg hvalid' (he j) hδ
          simpa [e'] using h
      · rw [Fin.foldl_succ_last]
        change fp.fl_sub s (a (Fin.last k)) = _
        rw [hfl, hs, Fin.sum_univ_castSucc]
        simp only [e0', e', Fin.snoc_castSucc, Fin.snoc_last]
        rw [sub_sub, sub_mul, add_mul, Finset.sum_mul]
        congr 1
        · ring
        · congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring

private theorem p08_fold_sub_mul_reverse (fp : StandardFPModel) :
    ∀ (k : ℕ) (v : ℝ) (a x : Fin k → ℝ), (k : ℝ) * fp.u < 1 →
      ∃ q : ℝ, ∃ c : Fin k → ℝ,
        |q - 1| ≤ p08GammaReal (k : ℝ) fp.u ∧
        (∀ j, |c j - 1| ≤ p08GammaReal (k : ℝ) fp.u) ∧
        v = Fin.foldl k
          (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) v * q +
          ∑ j : Fin k, a j * x j * c j := by
  intro k
  induction k with
  | zero =>
      intro v a x _
      refine ⟨1, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [p08GammaReal]
      · intro j; exact Fin.elim0 j
      · simp
  | succ k ih =>
      intro v a x hvalid
      have hvalid' : ((k : ℝ) + 1) * fp.u < 1 := by simpa using hvalid
      have hprev : (k : ℝ) * fp.u < 1 := by nlinarith [fp.u_nonneg]
      have hk : 0 ≤ (k : ℝ) := by positivity
      let a' : Fin k → ℝ := fun j => a j.castSucc
      let x' : Fin k → ℝ := fun j => x j.castSucc
      obtain ⟨q, c, hq, hc, hsum⟩ := ih v a' x' hprev
      let s := Fin.foldl k
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a j.castSucc) (x j.castSucc))) v
      have hs : v = s * q +
          ∑ j : Fin k, a j.castSucc * x j.castSucc * c j := by
        simpa [s, a', x'] using hsum
      obtain ⟨δm, hδm, hm⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨δs, hδs, hfl⟩ :=
        fp.model_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      have hden : 1 + δs ≠ 0 := by
        have := (abs_le.mp hδs).1
        nlinarith
      let q' : ℝ := q / (1 + δs)
      let c' : Fin (k + 1) → ℝ :=
        Fin.snoc c ((1 + δm) * q)
      refine ⟨q', c', ?_, ?_, ?_⟩
      · simpa [q'] using
          (p08_gamma_inverse_compose hk fp.u_nonneg hvalid' hq hδs)
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · have hcomp := p08_gamma_compose_error (a := (k : ℝ))
            (u := fp.u) (e := q - 1) (δ := δm) hk fp.u_nonneg hvalid'
            hq hδm
          have heq : (1 + δm) * q - 1 = (1 + (q - 1)) * (1 + δm) - 1 := by ring
          simpa only [c', Fin.snoc_last, heq, Nat.cast_add, Nat.cast_one] using hcomp
        · have hmono : p08GammaReal (k : ℝ) fp.u ≤
              p08GammaReal ((k + 1 : ℕ) : ℝ) fp.u := by
            apply p08_gamma_mono hk (by norm_num) fp.u_nonneg
            simpa using hvalid
          simpa [c'] using (hc j).trans hmono
      · rw [Fin.foldl_succ_last]
        change v = fp.fl_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) * q' + _
        rw [hfl, hm, Fin.sum_univ_castSucc]
        simp only [q', c', Fin.snoc_castSucc, Fin.snoc_last]
        rw [hs]
        field_simp
        ring

private noncomputable def p08_forward_row (fp : StandardFPModel) {n : ℕ}
    (L : P08Matrix n) (rhs x : Fin n → ℝ) (i : Fin n) : ℝ :=
  Fin.foldl i.val
    (fun acc (j : Fin i.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L i ⟨j.val, by omega⟩) (x ⟨j.val, by omega⟩)))
    (rhs i)

private theorem p08_forward_steps_characterization (fp : StandardFPModel)
    {n : ℕ} (L : P08Matrix n) (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := roundedForwardSubSteps fp n L rhs k hk x
      (∀ i : Fin n, i.val < n - k → y i = x i) ∧
      (∀ i : Fin n, n - k ≤ i.val →
        y i = fp.fl_div (p08_forward_row fp L rhs y i) (L i i)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro i _
        rfl
      · intro i hi
        omega
  | succ k ih =>
      intro hk x
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      have hdef : roundedForwardSubSteps fp n L rhs (k + 1) hk x =
          roundedForwardSubSteps fp n L rhs k (Nat.le_of_succ_le hk) x' := rfl
      let y := roundedForwardSubSteps fp n L rhs k (Nat.le_of_succ_le hk) x'
      obtain ⟨hunchanged, hprocessed⟩ := ih (Nat.le_of_succ_le hk) x'
      change (∀ i : Fin n, i.val < n - (k + 1) →
          roundedForwardSubSteps fp n L rhs (k + 1) hk x i = x i) ∧
        (∀ i : Fin n, n - (k + 1) ≤ i.val →
          roundedForwardSubSteps fp n L rhs (k + 1) hk x i =
            fp.fl_div (p08_forward_row fp L rhs
              (roundedForwardSubSteps fp n L rhs (k + 1) hk x) i) (L i i))
      rw [hdef]
      constructor
      · intro i hi
        have hprev : i.val < n - k := by omega
        have hne : i ≠ ik := by
          intro heq
          have hv := congrArg Fin.val heq
          dsimp [ik] at hv
          omega
        rw [hunchanged i hprev]
        simp [x', Function.update, hne]
      · intro i hi
        by_cases hieq : i = ik
        · subst i
          have hik : ik.val < n - k := by dsimp [ik]; omega
          have hyik : y ik = fp.fl_div s (L ik ik) := by
            change roundedForwardSubSteps fp n L rhs k (Nat.le_of_succ_le hk) x' ik = _
            rw [hunchanged ik hik]
            simp [x']
          have hrow : p08_forward_row fp L rhs y ik = s := by
            unfold p08_forward_row s
            change Fin.foldl (n - k - 1)
              (fun acc (t : Fin (n - k - 1)) =>
                fp.fl_sub acc
                  (fp.fl_mul (L ik ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩)))
              (rhs ik) = _
            congr 1
            funext acc t
            have ht : t.val < n - k := by omega
            have htne : (⟨t.val, by omega⟩ : Fin n) ≠ ik := by
              intro heq
              have hv := congrArg Fin.val heq
              dsimp [ik] at hv
              omega
            have hy : y (⟨t.val, by omega⟩ : Fin n) =
                x (⟨t.val, by omega⟩ : Fin n) := by
              change roundedForwardSubSteps fp n L rhs k (Nat.le_of_succ_le hk) x'
                (⟨t.val, by omega⟩ : Fin n) = _
              rw [hunchanged _ ht]
              simp [x', htne]
            rw [hy]
          simpa [y, hrow] using hyik
        · have hproc : n - k ≤ i.val := by
            have hneq : i.val ≠ n - k - 1 := by
              intro hv
              apply hieq
              exact Fin.ext hv
            omega
          exact hprocessed i hproc

private theorem p08_forward_characterization (fp : StandardFPModel)
    {n : ℕ} (L : P08Matrix n) (rhs : Fin n → ℝ) (i : Fin n) :
    roundedForwardSub fp n L rhs i =
      fp.fl_div (p08_forward_row fp L rhs (roundedForwardSub fp n L rhs) i)
        (L i i) := by
  have h := (p08_forward_steps_characterization fp L rhs n (le_refl n)
    (fun _ => 0)).2 i (by omega)
  simpa [roundedForwardSub] using h

private theorem p08_sum_fin_prefix {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin i.val, f ⟨j.val, by omega⟩) = (Finset.Iio i).sum f := by
  classical
  apply Finset.sum_bij (fun j _ => (⟨j.val, by omega⟩ : Fin n))
  · intro j _
    simp only [Finset.mem_Iio, Fin.lt_def]
    exact j.isLt
  · intro j₁ _ j₂ _ hj
    exact Fin.ext (congrArg (fun t : Fin n => t.val) hj)
  · intro j hj
    refine ⟨⟨j.val, by simpa using hj⟩, by simp, ?_⟩
    exact Fin.ext rfl
  · intro j _
    rfl

private theorem p08_sum_lower {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j : Fin n, i < j → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
  classical
  have hsub : (Finset.Iic i).sum f = ∑ j : Fin n, f j := by
    apply Finset.sum_subset (by simp)
    intro j _ hj
    apply hzero j
    simpa only [Finset.mem_Iic, not_le] using hj
  calc
    (∑ j : Fin n, f j) = (Finset.Iic i).sum f := hsub.symm
    _ = f i + (Finset.Iio i).sum f := by
      rw [← Finset.Iio_insert, Finset.sum_insert]
      simp
    _ = (∑ j : Fin i.val, f ⟨j.val, by omega⟩) + f i := by
      rw [p08_sum_fin_prefix]
      ring

private theorem p08_forward_row_backward (fp : StandardFPModel)
    {n : ℕ} (L : P08Matrix n) (rhs x : Fin n → ℝ)
    (i : Fin n) (hdiag : L i i ≠ 0)
    (hlower : p08LowerTriangular L)
    (hvalid : (n : ℝ) * fp.u < 1)
    (hlocal : x i = fp.fl_div (p08_forward_row fp L rhs x i) (L i i)) :
    ∃ Frow : Fin n → ℝ,
      (∀ j, |Frow j| ≤ p08GammaReal (n : ℝ) fp.u * |L i j|) ∧
      (∑ j : Fin n, (L i j + Frow j) * x j) = rhs i := by
  let a : Fin i.val → ℝ := fun j => L i ⟨j.val, by omega⟩
  let z : Fin i.val → ℝ := fun j => x ⟨j.val, by omega⟩
  have hi_le : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hi_le_real : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hi_le
  have hi_valid : (i.val : ℝ) * fp.u < 1 := by
    have hle : (i.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_lt i.isLt)
    nlinarith [mul_le_mul_of_nonneg_right hle fp.u_nonneg]
  have hi_succ_valid : ((i.val : ℝ) + 1) * fp.u < 1 := by
    have hle : ((i.val : ℝ) + 1) ≤ (n : ℝ) := by simpa using hi_le_real
    nlinarith [mul_le_mul_of_nonneg_right hle fp.u_nonneg]
  obtain ⟨q, c, hq, hc, hsum⟩ :=
    p08_fold_sub_mul_reverse fp i.val (rhs i) a z hi_valid
  have hsum' : rhs i = p08_forward_row fp L rhs x i * q +
      ∑ j : Fin i.val, a j * z j * c j := by
    simpa [p08_forward_row, a, z] using hsum
  let s := p08_forward_row fp L rhs x i
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (L i i) hdiag
  have hden : 1 + δ ≠ 0 := by
    have hle := (abs_le.mp hδ).1
    nlinarith [hi_succ_valid]
  have hlocal' : x i = (s / L i i) * (1 + δ) := by
    simpa [s, hdiv] using hlocal
  have hsx : s * q = (L i i * x i) * (q / (1 + δ)) := by
    rw [hlocal']
    field_simp [hdiag, hden]
  have hqdiv : |q / (1 + δ) - 1| ≤
      p08GammaReal ((i.val : ℝ) + 1) fp.u :=
    p08_gamma_inverse_compose (by positivity) fp.u_nonneg hi_succ_valid hq hδ
  have hmono_prev : p08GammaReal (i.val : ℝ) fp.u ≤
      p08GammaReal (n : ℝ) fp.u := by
    apply p08_gamma_mono (by positivity)
      (by exact_mod_cast (Nat.le_of_lt i.isLt)) fp.u_nonneg hvalid
  have hmono_diag : p08GammaReal ((i.val : ℝ) + 1) fp.u ≤
      p08GammaReal (n : ℝ) fp.u := by
    apply p08_gamma_mono (by positivity)
      (by simpa using hi_le_real) fp.u_nonneg hvalid
  let coeff (j : Fin n) : ℝ :=
    if h : j.val < i.val then c ⟨j.val, h⟩
    else if j = i then q / (1 + δ) else 1
  let Frow (j : Fin n) : ℝ := L i j * (coeff j - 1)
  have hcoeff (j : Fin n) : |coeff j - 1| ≤
      p08GammaReal (n : ℝ) fp.u := by
    by_cases hj : j.val < i.val
    · have hj' : j < i := hj
      simpa [coeff, hj'] using (hc ⟨j.val, hj⟩).trans hmono_prev
    · by_cases hji : j = i
      · subst j
        simpa [coeff] using hqdiv.trans hmono_diag
      · have hγ : 0 ≤ p08GammaReal (n : ℝ) fp.u :=
          p08_gamma_nonneg (by positivity) fp.u_nonneg hvalid
        have hj' : ¬j < i := hj
        simpa [coeff, hj', hji] using hγ
  have hFrow (j : Fin n) : |Frow j| ≤
      p08GammaReal (n : ℝ) fp.u * |L i j| := by
    rw [show Frow j = L i j * (coeff j - 1) by rfl, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hcoeff j) (abs_nonneg (L i j))]
  refine ⟨Frow, hFrow, ?_⟩
  have hzero (j : Fin n) (hij : i < j) :
      (L i j + Frow j) * x j = 0 := by
    have hL : L i j = 0 := hlower i j hij
    simp [Frow, hL]
  rw [p08_sum_lower i (fun j => (L i j + Frow j) * x j) hzero]
  have hprefix : (∑ j : Fin i.val,
      (L i ⟨j.val, by omega⟩ + Frow ⟨j.val, by omega⟩) *
        x ⟨j.val, by omega⟩) =
      ∑ j : Fin i.val, a j * z j * c j := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : j.val < i.val := j.isLt
    simp only [Frow, coeff, dif_pos hj, a, z]
    ring
  have hdiagcoeff : (L i i + Frow i) * x i =
      (L i i * x i) * (q / (1 + δ)) := by
    have hii : ¬i.val < i.val := Nat.lt_irrefl _
    simp [Frow, coeff, hii]
    ring
  rw [hprefix, hdiagcoeff]
  rw [hsum', hsx]
  ring

private theorem p08_forward_backward (fp : StandardFPModel)
    {n : ℕ} (L : P08Matrix n) (rhs : Fin n → ℝ)
    (hdiag : ∀ i : Fin n, L i i ≠ 0)
    (hlower : p08LowerTriangular L)
    (hvalid : (n : ℝ) * fp.u < 1) :
    let x := roundedForwardSub fp n L rhs
    ∃ F : P08Matrix n,
      p08RectFrobNorm F ≤ p08GammaReal (n : ℝ) fp.u * p08RectFrobNorm L ∧
      p08RectMatVec (L + F) x = rhs := by
  classical
  intro x
  have hrow (i : Fin n) :=
    p08_forward_row_backward fp L rhs x i (hdiag i) hlower hvalid
      (by simpa [x] using p08_forward_characterization fp L rhs i)
  let F : P08Matrix n := fun i j => Classical.choose (hrow i) j
  refine ⟨F, ?_, ?_⟩
  · apply p08_rect_norm_entrywise L F
      (p08_gamma_nonneg (by positivity) fp.u_nonneg hvalid)
    intro i j
    exact (Classical.choose_spec (hrow i)).1 j
  · funext i
    exact (Classical.choose_spec (hrow i)).2

private theorem p08_rect_norm_sq {m n : ℕ}
    (A : P08RectMatrix m n) :
    p08RectFrobNorm A ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2 := by
  unfold p08RectFrobNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem p08_block_norm_of_blocks_le {p b : ℕ}
    (T DT : P08BlockMatrix p b) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i j, p08RectFrobNorm (DT i j) ≤
      k * p08RectFrobNorm (T i j)) :
    p08BlockFrobNorm DT ≤ k * p08BlockFrobNorm T := by
  have hs : (∑ i : Fin p, ∑ j : Fin p,
      ∑ α : Fin b, ∑ β : Fin b, (DT i j α β) ^ 2) ≤
      k ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
        ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hsq : (p08RectFrobNorm (DT i j)) ^ 2 ≤
        (k * p08RectFrobNorm (T i j)) ^ 2 := by
      apply sq_le_sq.mpr
      have hA : 0 ≤ p08RectFrobNorm (DT i j) := Real.sqrt_nonneg _
      have hB : 0 ≤ p08RectFrobNorm (T i j) := Real.sqrt_nonneg _
      simpa [abs_mul, abs_of_nonneg hk,
        abs_of_nonneg hA, abs_of_nonneg hB] using h i j
    rw [mul_pow, p08_rect_norm_sq, p08_rect_norm_sq] at hsq
    exact hsq
  unfold p08BlockFrobNorm
  calc
    Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
      ∑ α : Fin b, ∑ β : Fin b, (DT i j α β) ^ 2) ≤
        Real.sqrt (k ^ 2 * (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2)) :=
      Real.sqrt_le_sqrt hs
    _ = k * Real.sqrt (∑ i : Fin p, ∑ j : Fin p,
          ∑ α : Fin b, ∑ β : Fin b, (T i j α β) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq_eq_abs, abs_of_nonneg hk]

private theorem p08_block_vec_norm_entrywise {p b : ℕ}
    (v dv : P08BlockVector p b) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ i α, |dv i α| ≤ k * |v i α|) :
    p08BlockVecNorm dv ≤ k * p08BlockVecNorm v := by
  exact p08_rect_norm_entrywise v dv hk h

private theorem p08_fold_sub_vec_apply (fp : StandardFPModel)
    {b : ℕ} (k : ℕ) (v : Fin b → ℝ)
    (w : Fin k → Fin b → ℝ) (α : Fin b) :
    (Fin.foldl k
      (fun acc j => fun β => fp.fl_sub (acc β) (w j β)) v) α =
      Fin.foldl k (fun acc j => fp.fl_sub acc (w j α)) (v α) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      have h := ih v (fun j => w j.castSucc)
      simpa using congrArg (fun t : ℝ => fp.fl_sub t (w (Fin.last k) α)) h

private theorem p08_scaled_block_norm {b : ℕ}
    (A F : P08Matrix b) (e : Fin b → ℝ)
    {g h k : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h)
    (he : ∀ α, |e α| ≤ h)
    (hF : p08RectFrobNorm F ≤ g * p08RectFrobNorm A)
    (hcomb : h + g + h * g ≤ k) :
    p08RectFrobNorm
      (fun α β => A α β * e α + F α β * (1 + e α)) ≤
      k * p08RectFrobNorm A := by
  let AE : P08Matrix b := fun α β => A α β * e α
  let FE : P08Matrix b := fun α β => F α β * (1 + e α)
  have hAE : p08RectFrobNorm AE ≤ h * p08RectFrobNorm A := by
    apply p08_rect_norm_entrywise A AE hh
    intro α β
    rw [show AE α β = A α β * e α by rfl, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (he α) (abs_nonneg (A α β))
  have hFE : p08RectFrobNorm FE ≤
      (1 + h) * p08RectFrobNorm F := by
    apply p08_rect_norm_entrywise F FE (by linarith)
    intro α β
    rw [show FE α β = F α β * (1 + e α) by rfl, abs_mul]
    have h1 : |1 + e α| ≤ 1 + h := by
      have htri : |1 + e α| ≤ 1 + |e α| := by
        simpa using abs_add_le (1 : ℝ) (e α)
      linarith [he α]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left h1 (abs_nonneg (F α β))
  have hAn : 0 ≤ p08RectFrobNorm A := Real.sqrt_nonneg _
  have hFE' : p08RectFrobNorm FE ≤
      (1 + h) * (g * p08RectFrobNorm A) :=
    hFE.trans (mul_le_mul_of_nonneg_left hF (by linarith))
  have hsum : p08RectFrobNorm (AE + FE) ≤
      h * p08RectFrobNorm A +
        (1 + h) * (g * p08RectFrobNorm A) :=
    (p08_rect_norm_add AE FE).trans (add_le_add hAE hFE')
  have hlast := mul_le_mul_of_nonneg_right hcomb hAn
  change p08RectFrobNorm (AE + FE) ≤ k * p08RectFrobNorm A
  nlinarith

private theorem p08_assemble_mulVec_apply {p b : ℕ}
    (T DT : P08BlockMatrix p b) (x : P08BlockVector p b)
    (i : Fin p) (α : Fin b) :
    Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
      (p08AssembleVector x) (i, α) =
        ∑ j : Fin p, ∑ β : Fin b,
          (T i j α β + DT i j α β) * x j β := by
  change (∑ z : Fin p × Fin b,
    (T i z.1 α z.2 + DT i z.1 α z.2) * x z.1 z.2) = _
  rw [Fintype.sum_prod_type]

/-- P08-C3: complete Theorem 4.4 for a triangular BLR block system. -/
theorem p08_c3_blr_triangular_backward_error
    {p b r : ℕ} (fp : StandardFPModel)
    (T : P08BlockMatrix p b)
    (X Y : Fin p → Fin p → P08RectMatrix b r)
    (v : P08BlockVector p b)
    (trace : P08BLRTrace fp T X Y v)
    (hp : 0 < p) (hb : 0 < b)
    (hdiag : ∀ i : Fin p, ∀ α : Fin b, T i i α α ≠ 0)
    (hlower : ∀ i : Fin p, p08LowerTriangular (T i i))
    (hupper : ∀ i j : Fin p, i < j → T i j = 0)
    (hlr : ∀ i j : Fin p, j < i →
      T i j = p08LowRankMatrix (X i j) (Y i j))
    (hX : ∀ i j : Fin p, j < i → p08OrthonormalColumns (X i j))
    (hvalid : ((b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)) * fp.u < 1) :
    let x := trace.x
    let c := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ) + (p : ℝ)
    ∃ DT : P08BlockMatrix p b, ∃ dv : P08BlockVector p b,
      Matrix.mulVec (p08AssembleMatrix T + p08AssembleMatrix DT)
          (p08AssembleVector x) =
        p08AssembleVector v + p08AssembleVector dv ∧
      p08BlockFrobNorm DT ≤
        p08GammaReal c fp.u * p08BlockFrobNorm T ∧
      p08BlockVecNorm dv ≤
        p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
  -- PROOF_START P08-C3-H001
  classical
  dsimp only
  let x : P08BlockVector p b := trace.x
  let d : ℝ := (b : ℝ) + (r : ℝ) * Real.sqrt (r : ℝ)
  let c : ℝ := d + (p : ℝ)
  have hd : 0 ≤ d := by
    dsimp [d]
    positivity
  have hp_real : 0 ≤ (p : ℝ) := by positivity
  have hc : 0 ≤ c := add_nonneg hd hp_real
  have hvalid' : c * fp.u < 1 := by simpa [c, d, add_assoc] using hvalid
  have hvalid_d : d * fp.u < 1 := by
    nlinarith [mul_nonneg hp_real fp.u_nonneg]
  have hvalid_b : (b : ℝ) * fp.u < 1 := by
    have hq : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
    nlinarith [mul_nonneg hq fp.u_nonneg]
  have hvalid_p : (p : ℝ) * fp.u < 1 := by
    nlinarith [mul_nonneg hd fp.u_nonneg]
  have hγd : 0 ≤ p08GammaReal d fp.u :=
    p08_gamma_nonneg hd fp.u_nonneg hvalid_d
  have hγp : 0 ≤ p08GammaReal (p : ℝ) fp.u :=
    p08_gamma_nonneg hp_real fp.u_nonneg hvalid_p
  have hγc : 0 ≤ p08GammaReal c fp.u :=
    p08_gamma_nonneg hc fp.u_nonneg hvalid'
  have hcomb : p08GammaReal (p : ℝ) fp.u + p08GammaReal d fp.u +
      p08GammaReal (p : ℝ) fp.u * p08GammaReal d fp.u ≤
        p08GammaReal c fp.u := by
    have hvalid_pd : ((p : ℝ) + d) * fp.u < 1 := by
      simpa [c, add_comm] using hvalid'
    simpa [c, add_comm] using
      p08_gamma_mul_bound hp_real hd fp.u_nonneg hvalid_pd
  have hmono_b : p08GammaReal (b : ℝ) fp.u ≤ p08GammaReal c fp.u := by
    apply p08_gamma_mono (by positivity) ?_ fp.u_nonneg hvalid'
    dsimp [c, d]
    have hq : 0 ≤ (r : ℝ) * Real.sqrt (r : ℝ) := by positivity
    linarith
  let low : (i : Fin p) → Fin i.val → Fin b → ℝ :=
    fun i j =>
      p08RoundedLowRankMatVec fp
        (X i ⟨j.val, by omega⟩) (Y i ⟨j.val, by omega⟩)
        (x ⟨j.val, by omega⟩)
  have hlowstage (i j : Fin p) (hji : j < i) :
      ∃ Fij : P08Matrix b,
        p08RectFrobNorm Fij ≤
          p08GammaReal d fp.u * p08RectFrobNorm (T i j) ∧
        p08RoundedLowRankMatVec fp (X i j) (Y i j) (x j) =
          p08RectMatVec (T i j + Fij) (x j) := by
    obtain ⟨Fij, hFij, hEq⟩ :=
      p08_lowrank_matvec_backward fp (X i j) (Y i j) (x j)
        (hX i j hji) (by simpa [d] using hvalid_d)
    refine ⟨Fij, ?_, ?_⟩
    · simpa [hlr i j hji, d] using hFij
    · simpa [hlr i j hji] using hEq
  let F : P08BlockMatrix p b := fun i j =>
    if h : j < i then (hlowstage i j h).choose else 0
  have hF_norm (i j : Fin p) (hji : j < i) :
      p08RectFrobNorm (F i j) ≤
        p08GammaReal d fp.u * p08RectFrobNorm (T i j) := by
    simpa [F, hji] using (hlowstage i j hji).choose_spec.1
  have hF_eq (i j : Fin p) (hji : j < i) :
      p08RoundedLowRankMatVec fp (X i j) (Y i j) (x j) =
        p08RectMatVec (T i j + F i j) (x j) := by
    simpa [F, hji] using (hlowstage i j hji).choose_spec.2
  have hdiagstage (i : Fin p) :
      ∃ Gi : P08Matrix b,
        p08RectFrobNorm Gi ≤
          p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm (T i i) ∧
        p08RectMatVec (T i i + Gi) (x i) = trace.rhs i := by
    obtain ⟨Gi, hGi, hEq⟩ :=
      p08_forward_backward fp (T i i) (trace.rhs i)
        (hdiag i) (hlower i) hvalid_b
    refine ⟨Gi, hGi, ?_⟩
    simpa [x, trace.x_eq i] using hEq
  let G : Fin p → P08Matrix b := fun i => (hdiagstage i).choose
  have hG_norm (i : Fin p) :
      p08RectFrobNorm (G i) ≤
        p08GammaReal (b : ℝ) fp.u * p08RectFrobNorm (T i i) :=
    (hdiagstage i).choose_spec.1
  have hG_eq (i : Fin p) :
      p08RectMatVec (T i i + G i) (x i) = trace.rhs i :=
    (hdiagstage i).choose_spec.2
  have hvalid_i (i : Fin p) : (i.val : ℝ) * fp.u < 1 := by
    have hi : (i.val : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.le_of_lt i.isLt
    nlinarith [mul_le_mul_of_nonneg_right hi fp.u_nonneg]
  have hsub (i : Fin p) (α : Fin b) :=
    p08_fold_sub_backward fp i.val (v i α)
      (fun j => low i j α) (hvalid_i i)
  let e0 : P08BlockVector p b := fun i α => (hsub i α).choose
  let e : (i : Fin p) → Fin b → Fin i.val → ℝ :=
    fun i α => ((hsub i α).choose_spec).choose
  have he0 (i : Fin p) (α : Fin b) :
      |e0 i α| ≤ p08GammaReal (i.val : ℝ) fp.u :=
    ((hsub i α).choose_spec).choose_spec.1
  have he (i : Fin p) (α : Fin b) (j : Fin i.val) :
      |e i α j| ≤ p08GammaReal (i.val : ℝ) fp.u :=
    ((hsub i α).choose_spec).choose_spec.2.1 j
  have hfold (i : Fin p) (α : Fin b) :
      Fin.foldl i.val
        (fun acc j => fp.fl_sub acc (low i j α)) (v i α) =
        v i α * (1 + e0 i α) -
          ∑ j : Fin i.val, low i j α * (1 + e i α j) :=
    ((hsub i α).choose_spec).choose_spec.2.2
  have hrhs (i : Fin p) (α : Fin b) :
      trace.rhs i α = v i α * (1 + e0 i α) -
        ∑ j : Fin i.val, low i j α * (1 + e i α j) := by
    calc
      trace.rhs i α =
          (Fin.foldl i.val
            (fun acc j => fun β => fp.fl_sub (acc β) (low i j β)) (v i)) α := by
        rw [trace.rhs_eq i]
      _ = Fin.foldl i.val
          (fun acc j => fp.fl_sub acc (low i j α)) (v i α) :=
        p08_fold_sub_vec_apply fp i.val (v i) (low i) α
      _ = _ := hfold i α
  have hmono_i (i : Fin p) :
      p08GammaReal (i.val : ℝ) fp.u ≤
        p08GammaReal (p : ℝ) fp.u := by
    apply p08_gamma_mono (by positivity)
      (by exact_mod_cast (Nat.le_of_lt i.isLt)) fp.u_nonneg hvalid_p
  let dv : P08BlockVector p b := fun i α => v i α * e0 i α
  have hdv : p08BlockVecNorm dv ≤
      p08GammaReal (p : ℝ) fp.u * p08BlockVecNorm v := by
    apply p08_block_vec_norm_entrywise v dv hγp
    intro i α
    rw [show dv i α = v i α * e0 i α by rfl, abs_mul]
    have := (he0 i α).trans (hmono_i i)
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left this (abs_nonneg (v i α))
  let DT : P08BlockMatrix p b := fun i j =>
    if h : j < i then
      fun α β => T i j α β * e i α ⟨j.val, by omega⟩ +
        F i j α β * (1 + e i α ⟨j.val, by omega⟩)
    else if j = i then G i else 0
  have hDT_lower (i j : Fin p) (hji : j < i) :
      p08RectFrobNorm (DT i j) ≤
        p08GammaReal c fp.u * p08RectFrobNorm (T i j) := by
    have he' (α : Fin b) :
        |e i α ⟨j.val, by omega⟩| ≤ p08GammaReal (p : ℝ) fp.u :=
      (he i α ⟨j.val, by omega⟩).trans (hmono_i i)
    have h := p08_scaled_block_norm (T i j) (F i j)
      (fun α => e i α ⟨j.val, by omega⟩)
      hγd hγp he' (hF_norm i j hji) hcomb
    simpa [DT, hji] using h
  have hDT_diag (i : Fin p) :
      p08RectFrobNorm (DT i i) ≤
        p08GammaReal c fp.u * p08RectFrobNorm (T i i) := by
    have hnorm : 0 ≤ p08RectFrobNorm (T i i) := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hmono_b hnorm
    simpa [DT] using (hG_norm i).trans hmul
  have hDT_upper (i j : Fin p) (hij : i < j) :
      p08RectFrobNorm (DT i j) ≤
        p08GammaReal c fp.u * p08RectFrobNorm (T i j) := by
    have hnot : ¬j < i := not_lt.mpr (le_of_lt hij)
    have hne : j ≠ i := ne_of_gt hij
    simp [DT, hnot, hne, hupper i j hij, p08RectFrobNorm]
  have hDT : p08BlockFrobNorm DT ≤
      p08GammaReal c fp.u * p08BlockFrobNorm T := by
    apply p08_block_norm_of_blocks_le T DT hγc
    intro i j
    rcases lt_trichotomy j i with hji | hji | hij
    · exact hDT_lower i j hji
    · subst j; exact hDT_diag i
    · exact hDT_upper i j hij
  have hroweq (i : Fin p) (α : Fin b) :
      (∑ j : Fin p, ∑ β : Fin b,
        (T i j α β + DT i j α β) * x j β) =
        v i α + dv i α := by
    let f : Fin p → ℝ := fun j =>
      ∑ β : Fin b, (T i j α β + DT i j α β) * x j β
    have hzero (j : Fin p) (hij : i < j) : f j = 0 := by
      have hnot : ¬j < i := not_lt.mpr (le_of_lt hij)
      have hne : j ≠ i := ne_of_gt hij
      simp [f, DT, hnot, hne, hupper i j hij]
    have hdiagterm : f i = trace.rhs i α := by
      have hEq := congrArg (fun z : Fin b → ℝ => z α) (hG_eq i)
      simpa [f, DT, p08RectMatVec] using hEq
    have hlowterm (j : Fin i.val) :
        f ⟨j.val, by omega⟩ =
          low i j α * (1 + e i α j) := by
      let j' : Fin p := ⟨j.val, by omega⟩
      have hji : j' < i := by exact j.isLt
      have hEq := congrArg (fun z : Fin b → ℝ => z α) (hF_eq i j' hji)
      change low i j α =
        ∑ β : Fin b, (T i j' α β + F i j' α β) * x j' β at hEq
      have hpoint (β : Fin b) :
          T i j' α β + DT i j' α β =
            (T i j' α β + F i j' α β) * (1 + e i α j) := by
        simp only [DT, dif_pos hji]
        ring
      change (∑ β : Fin b,
        (T i j' α β + DT i j' α β) * x j' β) = _
      simp_rw [hpoint]
      calc
        (∑ β : Fin b,
          (T i j' α β + F i j' α β) *
            (1 + e i α j) * x j' β) =
            (∑ β : Fin b,
              (T i j' α β + F i j' α β) * x j' β) *
                (1 + e i α j) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro β _
          ring
        _ = _ := by rw [← hEq]
    change (∑ j : Fin p, f j) = _
    rw [p08_sum_lower i f hzero]
    simp_rw [hlowterm]
    rw [hdiagterm, hrhs i α]
    simp [dv]
    ring
  refine ⟨DT, dv, ?_, ?_, hdv⟩
  · funext z
    rcases z with ⟨i, α⟩
    rw [p08_assemble_mulVec_apply]
    exact hroweq i α
  · simpa [c, d, add_assoc] using hDT

end VSCLReuse

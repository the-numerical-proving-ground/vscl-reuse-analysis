import VSCLReuse.P39.Definitions

namespace VSCLReuse

private lemma p39_gamma_nonneg (u : ℝ) (hu : 0 ≤ u) (m : ℕ)
    (hm : (m : ℝ) * u < 1) : 0 ≤ p39Gamma u m := by
  unfold p39Gamma
  apply div_nonneg
  · positivity
  · linarith

private lemma p39_gamma_mono (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℝ) * u < 1) :
    p39Gamma u a ≤ p39Gamma u b := by
  have ha : (a : ℝ) * u < 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    nlinarith
  unfold p39Gamma
  have hda : 0 < 1 - (a : ℝ) * u := by linarith
  have hdb : 0 < 1 - (b : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hda hdb).2
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  nlinarith

private lemma p39_gamma_step (u : ℝ) (hu : 0 ≤ u) (m : ℕ)
    (hm : ((m + 1 : ℕ) : ℝ) * u < 1) :
    (1 + u) * p39Gamma u m + u ≤ p39Gamma u (m + 1) := by
  have hm' : (m : ℝ) * u < 1 := by
    push_cast at hm ⊢
    nlinarith
  unfold p39Gamma
  have hd : 0 < 1 - (m : ℝ) * u := by linarith
  have hd' : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by linarith
  calc
    (1 + u) * ((m : ℝ) * u / (1 - (m : ℝ) * u)) + u =
        (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) := by
          field_simp [ne_of_gt hd, show 1 - u * (m : ℝ) ≠ 0 by nlinarith [hd]]
          push_cast
          ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hd hd').2
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity) (sq_nonneg u)]

private lemma p39_gamma_two (u : ℝ) (hu : 0 ≤ u) (m : ℕ)
    (hm : ((m + 1 : ℕ) : ℝ) * u < 1) (h1 : 1 ≤ m) :
    2 * u + u ^ 2 ≤ p39Gamma u (m + 1) := by
  have h2 : (2 : ℝ) * u < 1 := by
    have : (2 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ m + 1)
    nlinarith
  have hmono := p39_gamma_mono u hu (show 2 ≤ m + 1 by omega) hm
  have hbase : 2 * u + u ^ 2 ≤ p39Gamma u 2 := by
    unfold p39Gamma
    norm_num at *
    apply (le_div_iff₀ (by linarith : 0 < 1 - 2 * u)).2
    nlinarith [sq_nonneg u]
  exact hbase.trans hmono

private lemma p39_mul_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_mul x y - x * y| ≤ fp.u * |x * y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_mul x y
  rw [heq]
  have he : x * y * (1 + δ) - x * y = (x * y) * δ := by ring
  rw [he, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x * y))

private lemma p39_add_error (fp : P39FPModel) (x y : ℝ) :
    |fp.fl_add x y - (x + y)| ≤ fp.u * |x + y| := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_add x y
  rw [heq]
  have he : (x + y) * (1 + δ) - (x + y) = (x + y) * δ := by ring
  rw [he, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (x + y))

private lemma p39_accumulate_error (u g S a A q Q Z : ℝ)
    (hu : 0 ≤ u) (hg : 0 ≤ g) (hS : 0 ≤ S)
    (ha : |a| ≤ S) (hA : |A - a| ≤ g * S)
    (hQ : |Q - q| ≤ u * |q|)
    (hZ : |Z - (A + Q)| ≤ u * |A + Q|) :
    |Z - (a + q)| ≤ ((1 + u) * g + u) * S + (2 * u + u ^ 2) * |q| := by
  have hAabs : |A| ≤ (1 + g) * S := by
    have h := abs_add_le (A - a) a
    have he : A - a + a = A := by ring
    rw [he] at h
    calc
      |A| ≤ |A - a| + |a| := h
      _ ≤ g * S + S := add_le_add hA ha
      _ = (1 + g) * S := by ring
  have hQabs : |Q| ≤ (1 + u) * |q| := by
    have h := abs_add_le (Q - q) q
    have he : Q - q + q = Q := by ring
    rw [he] at h
    calc
      |Q| ≤ |Q - q| + |q| := h
      _ ≤ u * |q| + |q| := by gcongr
      _ = (1 + u) * |q| := by ring
  have hsum : |A + Q| ≤ (1 + g) * S + (1 + u) * |q| := by
    calc
      |A + Q| ≤ |A| + |Q| := abs_add_le A Q
      _ ≤ _ := add_le_add hAabs hQabs
  have htri : |Z - (a + q)| ≤ |Z - (A + Q)| + |A - a| + |Q - q| := by
    have he : Z - (a + q) = (Z - (A + Q)) + ((A - a) + (Q - q)) := by ring
    rw [he]
    calc
      |_ + _| ≤ |Z - (A + Q)| + |(A - a) + (Q - q)| := abs_add_le _ _
      _ ≤ |Z - (A + Q)| + (|A - a| + |Q - q|) :=
        add_le_add_right (abs_add_le _ _) _
      _ = _ := by ring
  calc
    |Z - (a + q)| ≤ u * |A + Q| + g * S + u * |q| := by
      exact htri.trans (by gcongr)
    _ ≤ u * ((1 + g) * S + (1 + u) * |q|) + g * S + u * |q| := by
      gcongr
    _ = _ := by ring

private lemma p39_dot_succ_last (fp : P39FPModel) (m : ℕ)
    (x y : Fin (m + 2) → ℝ) :
    p39RoundedDotProduct fp (m + 2) x y =
      fp.fl_add
        (p39RoundedDotProduct fp (m + 1) (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))) := by
  simp only [p39RoundedDotProduct, Fin.foldl_succ_last]
  rfl

private lemma p39_dot_error (fp : P39FPModel) (m : ℕ)
    (hm : (m : ℝ) * fp.u < 1) (x y : Fin m → ℝ) :
    |p39RoundedDotProduct fp m x y - ∑ k : Fin m, x k * y k| ≤
      p39Gamma fp.u m * ∑ k : Fin m, |x k * y k| := by
  induction m with
  | zero =>
      simp [p39RoundedDotProduct]
  | succ m ih =>
      cases m with
      | zero =>
          have hu := p39_gamma_step fp.u fp.u_nonneg 0 hm
          simpa [p39RoundedDotProduct, Fin.sum_univ_one, p39Gamma] using
            (p39_mul_error fp (x 0) (y 0)).trans
              (mul_le_mul_of_nonneg_right (by simpa [p39Gamma] using hu) (abs_nonneg _))
      | succ m =>
          let x' : Fin (m + 1) → ℝ := fun k => x k.castSucc
          let y' : Fin (m + 1) → ℝ := fun k => y k.castSucc
          let a : ℝ := ∑ k : Fin (m + 1), x' k * y' k
          let S : ℝ := ∑ k : Fin (m + 1), |x' k * y' k|
          let A : ℝ := p39RoundedDotProduct fp (m + 1) x' y'
          let q : ℝ := x (Fin.last (m + 1)) * y (Fin.last (m + 1))
          let Q : ℝ := fp.fl_mul (x (Fin.last (m + 1))) (y (Fin.last (m + 1)))
          let Z : ℝ := fp.fl_add A Q
          have hm' : ((m + 1 : ℕ) : ℝ) * fp.u < 1 := by
            push_cast at hm ⊢
            nlinarith [fp.u_nonneg]
          have hA : |A - a| ≤ p39Gamma fp.u (m + 1) * S := ih hm' x' y'
          have ha : |a| ≤ S := by
            exact Finset.abs_sum_le_sum_abs _ _
          have hS : 0 ≤ S := by positivity
          have hQ : |Q - q| ≤ fp.u * |q| := p39_mul_error fp _ _
          have hZ : |Z - (A + Q)| ≤ fp.u * |A + Q| := p39_add_error fp A Q
          have hbound := p39_accumulate_error fp.u (p39Gamma fp.u (m + 1))
            S a A q Q Z fp.u_nonneg (p39_gamma_nonneg fp.u fp.u_nonneg _ hm')
            hS ha hA hQ hZ
          have hc1 := p39_gamma_step fp.u fp.u_nonneg (m + 1) hm
          have hc2 := p39_gamma_two fp.u fp.u_nonneg (m + 1) hm (by omega)
          calc
            |p39RoundedDotProduct fp (m + 2) x y -
                ∑ k : Fin (m + 2), x k * y k| = |Z - (a + q)| := by
                  rw [p39_dot_succ_last, Fin.sum_univ_castSucc]
            _ ≤ ((1 + fp.u) * p39Gamma fp.u (m + 1) + fp.u) * S +
                  (2 * fp.u + fp.u ^ 2) * |q| := hbound
            _ ≤ p39Gamma fp.u (m + 2) * (S + |q|) := by
                  calc
                    _ ≤ p39Gamma fp.u (m + 2) * S +
                        p39Gamma fp.u (m + 2) * |q| :=
                      add_le_add (mul_le_mul_of_nonneg_right hc1 hS)
                        (mul_le_mul_of_nonneg_right hc2 (abs_nonneg q))
                    _ = _ := by ring
            _ = p39Gamma fp.u (m + 2) *
                  ∑ k : Fin (m + 2), |x k * y k| := by
                    rw [Fin.sum_univ_castSucc]

private lemma p39_step_other (fp : P39FPModel) (n : ℕ)
    (L X : P39Matrix n n) (j i k : Fin n) (h : k ≠ j) :
    p39Method2SourceStep fp n L X j i k = X i k := by
  simp [p39Method2SourceStep, h]

private lemma p39_steps_stable (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (k : ℕ) :
    ∀ (hk : k ≤ n) (X : P39Matrix n n) (i j : Fin n), k ≤ j.val →
      p39Method2SourceSteps fp n L k hk X i j = X i j := by
  induction k with
  | zero =>
      intro hk X i j hj
      rfl
  | succ k ih =>
      intro hk X i j hj
      have hkj : j ≠ (⟨k, hk⟩ : Fin n) := by
        intro he
        have : j.val = k := congrArg Fin.val he
        omega
      change p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk)
        (p39Method2SourceStep fp n L X ⟨k, hk⟩) i j = X i j
      rw [ih _ _ _ _ (by omega), p39_step_other fp n L X ⟨k, hk⟩ i j hkj]

private lemma p39_step_column_congr (fp : P39FPModel) (n : ℕ)
    (L A B : P39Matrix n n) (j i : Fin n)
    (h : ∀ t : Fin n, j.val < t.val → A i t = B i t) :
    p39Method2SourceStep fp n L A j i j =
      p39Method2SourceStep fp n L B j i j := by
  by_cases hij : i = j
  · simp [p39Method2SourceStep, hij]
  by_cases hji : j.val < i.val
  · have he : (fun t : Fin (n - j.val - 1) =>
        A i ⟨j.val + 1 + t.val, by omega⟩) =
        (fun t : Fin (n - j.val - 1) =>
        B i ⟨j.val + 1 + t.val, by omega⟩) := by
      funext t
      let T : Fin n := ⟨j.val + 1 + t.val, by omega⟩
      change A i T = B i T
      exact h T (by change j.val < j.val + 1 + t.val; omega)
    simp [p39Method2SourceStep, hij, hji, he]
  · have hji' : ¬ j < i := hji
    simp [p39Method2SourceStep, hij, hji']

private lemma p39_steps_column (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (k : ℕ) :
    ∀ (hk : k ≤ n) (X : P39Matrix n n) (i j : Fin n), j.val < k →
      let Y := p39Method2SourceSteps fp n L k hk X
      Y i j = p39Method2SourceStep fp n L Y j i j := by
  induction k with
  | zero =>
      intro hk X i j hj
      omega
  | succ k ih =>
      intro hk X i j hj
      let J : Fin n := ⟨k, hk⟩
      let X' := p39Method2SourceStep fp n L X J
      let Y := p39Method2SourceSteps fp n L k (Nat.le_of_succ_le hk) X'
      change Y i j = p39Method2SourceStep fp n L Y j i j
      by_cases hlt : j.val < k
      · exact ih _ X' i j hlt
      · have hjk : j = J := Fin.ext (by simp [J]; omega)
        subst j
        have hY : Y i J = X' i J :=
          p39_steps_stable fp n L k (Nat.le_of_succ_le hk) X' i J (by simp [J])
        rw [hY]
        apply p39_step_column_congr fp n L X Y J i
        intro t ht
        have ht' : t ≠ J := by
          intro he
          subst t
          omega
        calc
          X i t = X' i t := (p39_step_other fp n L X J i t ht').symm
          _ = Y i t :=
            (p39_steps_stable fp n L k (Nat.le_of_succ_le hk) X' i t
              (by simp [J] at ht; omega)).symm

private lemma p39_inverse_diag (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (j : Fin n) :
    p39Method2SourceInverse fp n L j j = fp.fl_div 1 (L j j) := by
  have h := p39_steps_column fp n L n (le_refl n) (0 : P39Matrix n n) j j j.isLt
  simpa [p39Method2SourceInverse, p39Method2SourceStep] using h

private lemma p39_inverse_below (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hji : j.val < i.val) :
    p39Method2SourceInverse fp n L i j =
      fp.fl_mul (-(fp.fl_div 1 (L j j)))
        (p39RoundedDotProduct fp (n - j.val - 1)
          (fun t => p39Method2SourceInverse fp n L i
            ⟨j.val + 1 + t.val, by omega⟩)
          (fun t => L ⟨j.val + 1 + t.val, by omega⟩ j)) := by
  have h := p39_steps_column fp n L n (le_refl n) (0 : P39Matrix n n) i j j.isLt
  have hij : i ≠ j := by intro he; subst i; omega
  have hji' : j < i := hji
  simpa [p39Method2SourceInverse, p39Method2SourceStep, hij, hji'] using h

private lemma p39_inverse_above (fp : P39FPModel) (n : ℕ)
    (L : P39Matrix n n) (i j : Fin n) (hij : i.val < j.val) :
    p39Method2SourceInverse fp n L i j = 0 := by
  have h := p39_steps_column fp n L n (le_refl n) (0 : P39Matrix n n) i j j.isLt
  have hne : i ≠ j := by intro he; subst i; omega
  have hnot : ¬ j < i := by simp only [Fin.lt_def]; omega
  simpa [p39Method2SourceInverse, p39Method2SourceStep, hne, hnot] using h

private lemma p39_sum_tail (n : ℕ) (j : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ k : Fin n, k.val < j.val → f k = 0) :
    (∑ k : Fin n, f k) = f j +
      ∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩ := by
  let T : Finset (Fin n) := Finset.univ.filter (fun k => j.val < k.val)
  have htail :
      (∑ t : Fin (n - j.val - 1), f ⟨j.val + 1 + t.val, by omega⟩) =
        ∑ k ∈ T, f k := by
    apply Finset.sum_bij (fun t _ => (⟨j.val + 1 + t.val, by omega⟩ : Fin n))
    · intro t ht
      change (⟨j.val + 1 + t.val, by omega⟩ : Fin n) ∈ T
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      change j.val < j.val + 1 + t.val
      omega
    · intro t₁ ht₁ t₂ ht₂ he
      apply Fin.ext
      have hv := congrArg Fin.val he
      dsimp at hv ⊢
      omega
    · intro k hk
      have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
      let t : Fin (n - j.val - 1) := ⟨k.val - j.val - 1, by have := k.isLt; omega⟩
      refine ⟨t, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      dsimp [t]
      omega
    · intro t ht
      rfl
  have hsub : T ⊆ Finset.univ.erase j := by
    intro k hk
    have hjk : j.val < k.val := (Finset.mem_filter.mp hk).2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    subst k
    omega
  have hsum : (∑ k ∈ Finset.univ.erase j, f k) = ∑ k ∈ T, f k := by
    apply (Finset.sum_subset hsub ?_).symm
    intro k hk hkn
    have hne : k ≠ j := (Finset.mem_erase.mp hk).1
    have hnot : ¬ j.val < k.val := by
      intro hlt
      exact hkn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    have hvalne : k.val ≠ j.val := by
      intro he
      exact hne (Fin.ext he)
    exact hzero k (by omega)
  calc
    (∑ k : Fin n, f k) = (∑ k ∈ Finset.univ.erase j, f k) + f j := by
      exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)).symm
    _ = f j + ∑ k ∈ T, f k := by rw [hsum, add_comm]
    _ = f j + ∑ t : Fin (n - j.val - 1),
        f ⟨j.val + 1 + t.val, by omega⟩ := by rw [htail]

private lemma p39_scaled_dot_error (fp : P39FPModel) (l D : ℝ) (hl : l ≠ 0) :
    |fp.fl_mul (-(fp.fl_div 1 l)) D * l + D| ≤
      (2 * fp.u + fp.u ^ 2) * |D| := by
  obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 l hl
  obtain ⟨η, hη, hx⟩ := fp.model_mul (-(fp.fl_div 1 l)) D
  have hdl : fp.fl_div 1 l * l = 1 + δ := by
    rw [hd]
    field_simp [hl]
  have hxl : fp.fl_mul (-(fp.fl_div 1 l)) D * l =
      -((1 + δ) * (1 + η)) * D := by
    calc
      fp.fl_mul (-(fp.fl_div 1 l)) D * l =
          -(fp.fl_div 1 l * l) * ((1 + η) * D) := by rw [hx]; ring
      _ = -((1 + δ) * (1 + η)) * D := by rw [hdl]; ring
  have hprod : |δ| * |η| ≤ fp.u * fp.u := by
    exact mul_le_mul hδ hη (abs_nonneg _) fp.u_nonneg
  have herr : |δ + η + δ * η| ≤ 2 * fp.u + fp.u ^ 2 := by
    calc
      |δ + η + δ * η| ≤ |δ + η| + |δ * η| := abs_add_le _ _
      _ ≤ (|δ| + |η|) + |δ| * |η| := by
        rw [abs_mul]
        gcongr
        exact abs_add_le δ η
      _ ≤ (fp.u + fp.u) + fp.u * fp.u :=
        add_le_add (add_le_add hδ hη) hprod
      _ = _ := by ring
  have he : fp.fl_mul (-(fp.fl_div 1 l)) D * l + D =
      -(δ + η + δ * η) * D := by
    rw [hxl]
    ring
  rw [he, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_right herr (abs_nonneg D)

private lemma p39_reciprocal_error (fp : P39FPModel) (l : ℝ)
    (hl : l ≠ 0) (hu : fp.u < 1) :
    |fp.fl_div 1 l * l - 1| ≤
      (fp.u / (1 - fp.u)) * |fp.fl_div 1 l * l| := by
  obtain ⟨δ, hδ, hd⟩ := fp.model_div 1 l hl
  have hdl : fp.fl_div 1 l * l = 1 + δ := by
    rw [hd]
    field_simp [hl]
  have hbelow : 1 - fp.u ≤ |fp.fl_div 1 l * l| := by
    rw [hdl]
    have hlow : -fp.u ≤ δ := (abs_le.mp hδ).1
    calc
      1 - fp.u ≤ 1 + δ := by linarith
      _ ≤ |1 + δ| := le_abs_self _
  have hfrac : 0 ≤ fp.u / (1 - fp.u) :=
    div_nonneg fp.u_nonneg (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hbelow hfrac
  have hcancel : (fp.u / (1 - fp.u)) * (1 - fp.u) = fp.u := by
    field_simp [show 1 - fp.u ≠ 0 by linarith]
  rw [hcancel] at hmul
  calc
    |fp.fl_div 1 l * l - 1| = |δ| := by simp [hdl]
    _ ≤ fp.u := hδ
    _ ≤ _ := hmul

private lemma p39_lower_column_error (fp : P39FPModel) (n m : ℕ)
    (hm : m ≤ n) (hvalid : P39GammaValid fp.u n)
    (l : ℝ) (hl : l ≠ 0) (x y : Fin m → ℝ) :
    let D := p39RoundedDotProduct fp m x y
    let a := ∑ t : Fin m, x t * y t
    let S := ∑ t : Fin m, |x t * y t|
    |fp.fl_mul (-(fp.fl_div 1 l)) D * l + a| ≤
      (p39Gamma fp.u n + (2 * fp.u + fp.u ^ 2) * (1 + p39Gamma fp.u n)) * S := by
  dsimp
  let D := p39RoundedDotProduct fp m x y
  let a := ∑ t : Fin m, x t * y t
  let S := ∑ t : Fin m, |x t * y t|
  have hmn : (m : ℝ) * fp.u < 1 := by
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hm
    unfold P39GammaValid at hvalid
    nlinarith [fp.u_nonneg]
  have hg := p39_gamma_mono fp.u fp.u_nonneg hm hvalid
  have hdot0 : |D - a| ≤ p39Gamma fp.u m * S := p39_dot_error fp m hmn x y
  have hS : 0 ≤ S := by positivity
  have hdot : |D - a| ≤ p39Gamma fp.u n * S :=
    hdot0.trans (mul_le_mul_of_nonneg_right hg hS)
  have ha : |a| ≤ S := Finset.abs_sum_le_sum_abs _ _
  have hD : |D| ≤ (1 + p39Gamma fp.u n) * S := by
    have he : D - a + a = D := by ring
    calc
      |D| = |D - a + a| := by rw [he]
      _ ≤ |D - a| + |a| := abs_add_le _ _
      _ ≤ p39Gamma fp.u n * S + S := add_le_add hdot ha
      _ = _ := by ring
  have hscale := p39_scaled_dot_error fp l D hl
  have htri : |fp.fl_mul (-(fp.fl_div 1 l)) D * l + a| ≤
      |fp.fl_mul (-(fp.fl_div 1 l)) D * l + D| + |D - a| := by
    have he : fp.fl_mul (-(fp.fl_div 1 l)) D * l + a =
        (fp.fl_mul (-(fp.fl_div 1 l)) D * l + D) + (a - D) := by ring
    calc
      |fp.fl_mul (-(fp.fl_div 1 l)) D * l + a| =
          |(fp.fl_mul (-(fp.fl_div 1 l)) D * l + D) + (a - D)| := by rw [he]
      _ ≤ |fp.fl_mul (-(fp.fl_div 1 l)) D * l + D| + |a - D| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm]
  have hβ : 0 ≤ 2 * fp.u + fp.u ^ 2 := by nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  calc
    |fp.fl_mul (-(fp.fl_div 1 l)) D * l + a| ≤
        (2 * fp.u + fp.u ^ 2) * |D| + p39Gamma fp.u n * S :=
      htri.trans (add_le_add hscale hdot)
    _ ≤ (2 * fp.u + fp.u ^ 2) * ((1 + p39Gamma fp.u n) * S) +
        p39Gamma fp.u n * S :=
      add_le_add_left (mul_le_mul_of_nonneg_left hD hβ) _
    _ = _ := by ring

/-- Complete Method 2 left-residual result of Lemma 2.1. -/
theorem p39_c2_method2_lemma21_left_residual
    (fp : P39FPModel) (n : ℕ) (L : P39Matrix n n)
    (hL : ∀ a b : Fin n, a.val < b.val → L a b = 0)
    (hdiag : ∀ j : Fin n, L j j ≠ 0)
    (hvalid : P39GammaValid fp.u n) (i j : Fin n) :
    let X := p39Method2SourceInverse fp n L
    |p39MatMul X L i j - if i = j then 1 else 0| ≤
      p39Method2SourceUniformCoefficient fp n *
        ∑ k : Fin n, |X i k| * |L k j| := by
  -- PROOF_START P39-C2-H001
  let X := p39Method2SourceInverse fp n L
  let m := n - j.val - 1
  let x : Fin m → ℝ := fun t => X i ⟨j.val + 1 + t.val, by omega⟩
  let y : Fin m → ℝ := fun t => L ⟨j.val + 1 + t.val, by omega⟩ j
  let A : ℝ := ∑ t : Fin m, x t * y t
  let S : ℝ := ∑ t : Fin m, |x t * y t|
  let W : ℝ := ∑ k : Fin n, |X i k * L k j|
  let γ := p39Gamma fp.u n
  let β := 2 * fp.u + fp.u ^ 2
  let r := fp.u / (1 - fp.u)
  let α := γ + β * (1 + γ)
  let C := p39Method2SourceUniformCoefficient fp n
  change |p39MatMul X L i j - (if i = j then 1 else 0)| ≤
    C * ∑ k : Fin n, |X i k| * |L k j|
  simp_rw [← abs_mul]
  change |p39MatMul X L i j - (if i = j then 1 else 0)| ≤ C * W
  have hmul : p39MatMul X L i j = X i j * L j j + A := by
    simpa only [p39MatMul, A, x, y, m] using
      (p39_sum_tail n j (fun k => X i k * L k j) (by
        intro k hk
        change X i k * L k j = 0
        rw [hL k j hk, mul_zero]))
  have hweight : W = |X i j * L j j| + S := by
    simpa only [W, S, x, y, m] using
      (p39_sum_tail n j (fun k => |X i k * L k j|) (by
        intro k hk
        change |X i k * L k j| = 0
        rw [hL k j hk, mul_zero, abs_zero]))
  have hS : 0 ≤ S := by positivity
  have hγ : 0 ≤ γ := p39_gamma_nonneg fp.u fp.u_nonneg n hvalid
  have hβ : 0 ≤ β := by dsimp [β]; nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hn1 : (1 : ℝ) ≤ n := by
    have hn1' : 1 ≤ n := by have := j.isLt; omega
    exact_mod_cast hn1'
  have hu : fp.u < 1 := by
    have hnu : fp.u ≤ (n : ℝ) * fp.u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) fp.u_nonneg]
    unfold P39GammaValid at hvalid
    linarith
  have hr : 0 ≤ r := div_nonneg fp.u_nonneg (by show 0 ≤ 1 - fp.u; linarith)
  have hα : 0 ≤ α := by dsimp [α]; nlinarith [mul_nonneg hβ (by linarith : 0 ≤ 1 + γ)]
  have hC : C = α + r := by
    dsimp [C, α, γ, β, r, p39Method2SourceUniformCoefficient]
  have hCnonneg : 0 ≤ C := by rw [hC]; positivity
  have hαC : α ≤ C := by rw [hC]; linarith
  have hrC : r ≤ C := by rw [hC]; linarith
  by_cases hij : i.val < j.val
  · have hx : X i j = 0 := p39_inverse_above fp n L i j hij
    have hA : A = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hxt : x t = 0 := p39_inverse_above fp n L i
        ⟨j.val + 1 + t.val, by omega⟩ (by change i.val < j.val + 1 + t.val; omega)
      simp [hxt]
    have hS0 : S = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hxt : x t = 0 := p39_inverse_above fp n L i
        ⟨j.val + 1 + t.val, by omega⟩ (by change i.val < j.val + 1 + t.val; omega)
      simp [hxt]
    have hne : i ≠ j := by intro he; subst i; omega
    rw [hmul, hweight, hx, hA, hS0]
    simp [hne]
  · by_cases hji : j.val < i.val
    · have hne : i ≠ j := by intro he; subst i; omega
      have hx := p39_inverse_below fp n L i j hji
      have hlocal : |X i j * L j j + A| ≤ α * S := by
        change |p39Method2SourceInverse fp n L i j * L j j + A| ≤ α * S
        rw [hx]
        exact p39_lower_column_error fp n m (by dsimp [m]; omega)
          hvalid (L j j) (hdiag j) x y
      rw [hmul, if_neg hne]
      calc
        |X i j * L j j + A - 0| ≤ α * S := by simpa using hlocal
        _ ≤ C * S := mul_le_mul_of_nonneg_right hαC hS
        _ ≤ C * (|X i j * L j j| + S) := by
          nlinarith [mul_nonneg hCnonneg (abs_nonneg (X i j * L j j))]
        _ = C * W := by rw [hweight]
    · have heq : i = j := Fin.ext (by omega)
      subst i
      have hA : A = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        have hxt : x t = 0 := p39_inverse_above fp n L j
          ⟨j.val + 1 + t.val, by omega⟩ (by change j.val < j.val + 1 + t.val; omega)
        simp [hxt]
      have hS0 : S = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        have hxt : x t = 0 := p39_inverse_above fp n L j
          ⟨j.val + 1 + t.val, by omega⟩ (by change j.val < j.val + 1 + t.val; omega)
        simp [hxt]
      have hx : X j j = fp.fl_div 1 (L j j) := p39_inverse_diag fp n L j
      have hrec := p39_reciprocal_error fp (L j j) (hdiag j) hu
      rw [hmul, hweight, hA, hS0, hx]
      simp only [ite_true, add_zero]
      exact hrec.trans (mul_le_mul_of_nonneg_right hrC (abs_nonneg _))

end VSCLReuse

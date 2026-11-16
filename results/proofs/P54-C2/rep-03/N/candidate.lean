import VSCLReuse.P54.Definitions

namespace VSCLReuse

private lemma p54_poly_append (x : ℝ) (l : List ℝ) (a : ℝ) :
    p54PolyDesc x (l ++ [a]) = x * p54PolyDesc x l + a := by
  induction l with
  | nil => simp [p54PolyDesc]
  | cons b l ih =>
    simp only [List.cons_append, p54PolyDesc, List.length_append,
      List.length_singleton, pow_add, pow_one, ih]
    ring

private lemma p54_abs_append (x : ℝ) (l : List ℝ) (a : ℝ) :
    p54AbsDesc x (l ++ [a]) = |x| * p54AbsDesc x l + |a| := by
  induction l with
  | nil => simp [p54AbsDesc]
  | cons b l ih =>
    simp only [List.cons_append, p54AbsDesc, List.length_append,
      List.length_singleton, pow_add, pow_one, ih]
    ring

private lemma p54_horner_append (fp : P54FPModel) (x : ℝ)
    (a : ℝ) (l : List ℝ) (b : ℝ) :
    p54Horner fp x ((a :: l) ++ [b]) =
      fp.fl_add (fp.fl_mul x (p54Horner fp x (a :: l))) b := by
  simp [p54Horner, List.foldl_append]

private lemma p54_horner_append_ne (fp : P54FPModel) (x : ℝ)
    (l : List ℝ) (b : ℝ) (hne : l ≠ []) :
    p54Horner fp x (l ++ [b]) =
      fp.fl_add (fp.fl_mul x (p54Horner fp x l)) b := by
  cases l with
  | nil => contradiction
  | cons a l => exact p54_horner_append fp x a l b

private lemma p54_round_forward (fp : P54FPModel) (s t : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ fp.u ∧ t = s * (1 + δ)) :
    |t - s| ≤ fp.u * |s| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  rw [show s * (1 + δ) - s = s * δ by ring, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg s)

private lemma p54_round_inverse (fp : P54FPModel) (s t : ℝ)
    (h : ∃ ε : ℝ, |ε| ≤ fp.u ∧ s = t * (1 + ε)) :
    |s| ≤ (1 + fp.u) * |t| := by
  obtain ⟨ε, hε, rfl⟩ := h
  rw [abs_mul]
  have he : |1 + ε| ≤ 1 + fp.u := by
    calc
      |1 + ε| ≤ |(1 : ℝ)| + |ε| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hε 1
  nlinarith [abs_nonneg t]

private lemma p54_round_mag (fp : P54FPModel) (s t : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ fp.u ∧ t = s * (1 + δ)) :
    |t| ≤ (1 + fp.u) * |s| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  rw [abs_mul]
  have he : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  nlinarith [abs_nonneg s]

private lemma p54_round_nonneg (fp : P54FPModel) (hu : fp.u < 1)
    (s t : ℝ) (hs : 0 ≤ s)
    (h : ∃ δ : ℝ, |δ| ≤ fp.u ∧ t = s * (1 + δ)) : 0 ≤ t := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have : -fp.u ≤ δ := (abs_le.mp hδ).1
  exact mul_nonneg hs (by linarith)

private lemma p54_abs_nonneg (x : ℝ) (l : List ℝ) :
    0 ≤ p54AbsDesc x l := by
  induction l with
  | nil => simp [p54AbsDesc]
  | cons a l ih =>
    simp only [p54AbsDesc]
    positivity

private lemma p54_poly_le_abs (x : ℝ) (l : List ℝ) :
    |p54PolyDesc x l| ≤ p54AbsDesc x l := by
  induction l with
  | nil => simp [p54PolyDesc, p54AbsDesc]
  | cons a l ih =>
    simp only [p54PolyDesc, p54AbsDesc]
    calc
      |a * x ^ l.length + p54PolyDesc x l| ≤
          |a * x ^ l.length| + |p54PolyDesc x l| := abs_add_le _ _
      _ ≤ |a| * |x| ^ l.length + p54AbsDesc x l := by
        rw [abs_mul, abs_pow]
        linarith

private lemma p54_step_bounds (fp : P54FPModel) (hu : fp.u < 1)
    (x P R A H s r C : ℝ)
    (hC : 1 ≤ C) (hH : 0 ≤ H)
    (hPA : |P| ≤ A) (hE : |P - R| ≤ (C - 1) * A)
    (hI : A ≤ C * H)
    (hrf : ∃ δ : ℝ, |δ| ≤ fp.u ∧ r = s * (1 + δ))
    (hri : ∃ ε : ℝ, |ε| ≤ fp.u ∧ s = r * (1 + ε)) :
    let t := fp.fl_mul x R
    let z := fp.fl_add t r
    let m := fp.fl_mul |x| H
    let h := fp.fl_add m |r|
    |x * P + s - z| ≤ (C * (1 + fp.u) ^ 2 - 1) * (|x| * A + |s|) ∧
    |x| * A + |s| ≤ C * (1 + fp.u) ^ 2 * h ∧
    0 ≤ h := by
  dsimp
  let t := fp.fl_mul x R
  let z := fp.fl_add t r
  let m := fp.fl_mul |x| H
  let h := fp.fl_add m |r|
  have hmf := fp.model_mul |x| H
  have hmi := fp.inverse_mul |x| H
  have hzf := fp.model_add t r
  have hhf := fp.model_add m |r|
  have hhi := fp.inverse_add m |r|
  have hm : 0 ≤ m := p54_round_nonneg fp hu _ _ (mul_nonneg (abs_nonneg _) hH) hmf
  have hh : 0 ≤ h := p54_round_nonneg fp hu _ _ (add_nonneg hm (abs_nonneg _)) hhf
  have hmInv : |x| * H ≤ (1 + fp.u) * m := by
    have htmp := p54_round_inverse fp (|x| * H) m hmi
    rwa [abs_of_nonneg (mul_nonneg (abs_nonneg _) hH), abs_of_nonneg hm] at htmp
  have hhInv : m + |r| ≤ (1 + fp.u) * h := by
    have htmp := p54_round_inverse fp (m + |r|) h hhi
    rwa [abs_of_nonneg (add_nonneg hm (abs_nonneg _)), abs_of_nonneg hh] at htmp
  have hrInv : |s| ≤ (1 + fp.u) * |r| := p54_round_inverse fp s r hri
  have hrF : |s - r| ≤ fp.u * |s| := by
    simpa [abs_sub_comm] using p54_round_forward fp s r hrf
  have hrMag : |r| ≤ (1 + fp.u) * |s| := p54_round_mag fp s r hrf
  have hR : |R| ≤ C * A := by
    have ht : |R| ≤ |P| + |P - R| := by
      calc
        |R| = |P - (P - R)| := by congr 1; ring
        _ ≤ |P| + |P - R| := by
          simpa [abs_sub_comm] using (abs_sub_le P 0 (P - R))
    nlinarith
  have htF : |x * R - t| ≤ fp.u * |x * R| := by
    simpa [abs_sub_comm] using p54_round_forward fp (x * R) t (fp.model_mul x R)
  have htMag : |t| ≤ (1 + fp.u) * |x * R| :=
    p54_round_mag fp (x * R) t (fp.model_mul x R)
  have hzF : |t + r - z| ≤ fp.u * |t + r| := by
    simpa [abs_sub_comm] using p54_round_forward fp (t + r) z hzf
  have hxr : |x * R| ≤ |x| * (C * A) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hR (abs_nonneg x)
  have h1 : |x * (P - R)| ≤ |x| * ((C - 1) * A) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hE (abs_nonneg x)
  have h2 : |x * R - t| ≤ fp.u * (|x| * (C * A)) := by
    calc
      _ ≤ fp.u * |x * R| := htF
      _ ≤ fp.u * (|x| * (C * A)) :=
        mul_le_mul_of_nonneg_left hxr fp.u_nonneg
  have h4 : |t + r - z| ≤
      fp.u * ((1 + fp.u) * (|x| * (C * A)) + (1 + fp.u) * |s|) := by
    calc
      _ ≤ fp.u * |t + r| := hzF
      _ ≤ fp.u * (|t| + |r|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) fp.u_nonneg
      _ ≤ fp.u * ((1 + fp.u) * (|x| * (C * A)) + (1 + fp.u) * |s|) := by
        apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
        apply add_le_add _ hrMag
        exact htMag.trans (mul_le_mul_of_nonneg_left hxr (by linarith [fp.u_nonneg]))
  have htri : |x * P + s - z| ≤
      |x * (P - R)| + |x * R - t| + |s - r| + |t + r - z| := by
    calc
      _ = |(x * (P - R) + (x * R - t)) + ((s - r) + (t + r - z))| := by
        congr 1; ring
      _ ≤ |x * (P - R) + (x * R - t)| + |(s - r) + (t + r - z)| :=
        abs_add_le _ _
      _ ≤ _ := by
        have hleft := abs_add_le (x * (P - R)) (x * R - t)
        have hright := abs_add_le (s - r) (t + r - z)
        linarith
  have hError : |x * P + s - z| ≤
      (C * (1 + fp.u) ^ 2 - 1) * (|x| * A + |s|) := by
    calc
      _ ≤ |x * (P - R)| + |x * R - t| + |s - r| + |t + r - z| := htri
      _ ≤ |x| * ((C - 1) * A) + fp.u * (|x| * (C * A)) +
          fp.u * |s| + fp.u * ((1 + fp.u) * (|x| * (C * A)) +
          (1 + fp.u) * |s|) := by linarith [h1, h2, hrF, h4]
      _ ≤ _ := by
        have hc1 : 0 ≤ C - 1 := by linarith
        have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        have hnon : 0 ≤ (C - 1) * (1 + fp.u) ^ 2 * |s| := by positivity
        nlinarith
  have hAScaled : |x| * A ≤ C * (|x| * H) := by
    have := mul_le_mul_of_nonneg_left hI (abs_nonneg x)
    nlinarith
  have hmScaled : C * (|x| * H) ≤ C * ((1 + fp.u) * m) :=
    mul_le_mul_of_nonneg_left hmInv (by linarith)
  have hmiddle : C * (1 + fp.u) * m + (1 + fp.u) * |r| ≤
      C * (1 + fp.u) * (m + |r|) := by
    have hc1 : 0 ≤ C - 1 := by linarith
    have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    have : 0 ≤ (C - 1) * (1 + fp.u) * |r| := by positivity
    nlinarith
  have hlast : C * (1 + fp.u) * (m + |r|) ≤
      C * (1 + fp.u) ^ 2 * h := by
    have hc : 0 ≤ C * (1 + fp.u) := by nlinarith [fp.u_nonneg]
    have := mul_le_mul_of_nonneg_left hhInv hc
    nlinarith
  have hAbs : |x| * A + |s| ≤ C * (1 + fp.u) ^ 2 * h := by
    calc
      _ ≤ C * (|x| * H) + (1 + fp.u) * |r| := add_le_add hAScaled hrInv
      _ ≤ C * (1 + fp.u) * m + (1 + fp.u) * |r| := by linarith
      _ ≤ C * (1 + fp.u) * (m + |r|) := hmiddle
      _ ≤ _ := hlast
  exact ⟨hError, hAbs, hh⟩

private noncomputable def p54PairExact (cs : List (ℝ × ℝ)) : List ℝ :=
  cs.map (fun p => p.1 + p.2)

private noncomputable def p54PairRound (fp : P54FPModel)
    (cs : List (ℝ × ℝ)) : List ℝ :=
  cs.map (fun p => fp.fl_add p.1 p.2)

private lemma p54_pair_exact_append (cs : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    p54PairExact (cs ++ [p]) = p54PairExact cs ++ [p.1 + p.2] := by
  simp [p54PairExact]

private lemma p54_pair_round_append (fp : P54FPModel)
    (cs : List (ℝ × ℝ)) (p : ℝ × ℝ) :
    p54PairRound fp (cs ++ [p]) =
      p54PairRound fp cs ++ [fp.fl_add p.1 p.2] := by
  simp [p54PairRound]

private lemma p54_pair_bounds (fp : P54FPModel) (hu : fp.u < 1)
    (x : ℝ) (cs : List (ℝ × ℝ)) (hne : cs ≠ []) :
    |p54PolyDesc x (p54PairExact cs) -
      p54Horner fp x (p54PairRound fp cs)| ≤
      ((1 + fp.u) ^ (2 * cs.length - 1) - 1) *
        p54AbsDesc x (p54PairExact cs) ∧
    p54AbsDesc x (p54PairExact cs) ≤
      (1 + fp.u) ^ (2 * cs.length - 1) *
        p54Horner fp |x| ((p54PairRound fp cs).map abs) ∧
    0 ≤ p54Horner fp |x| ((p54PairRound fp cs).map abs) := by
  induction cs using List.reverseRecOn with
  | nil => contradiction
  | @append_singleton cs p ih =>
    cases cs with
    | nil =>
      have hf := p54_round_forward fp (p.1 + p.2) (fp.fl_add p.1 p.2)
        (fp.model_add p.1 p.2)
      have hi := p54_round_inverse fp (p.1 + p.2) (fp.fl_add p.1 p.2)
        (fp.inverse_add p.1 p.2)
      simpa [p54PairExact, p54PairRound, p54PolyDesc,
        p54AbsDesc, p54Horner] using
        (show |p.1 + p.2 - fp.fl_add p.1 p.2| ≤
            fp.u * |p.1 + p.2| ∧
          |p.1 + p.2| ≤ (1 + fp.u) * |fp.fl_add p.1 p.2| ∧
          0 ≤ |fp.fl_add p.1 p.2| from ⟨by simpa [abs_sub_comm] using hf, hi, abs_nonneg _⟩)
    | cons q qs =>
      have ih' := ih (by simp)
      let ys := p54PairExact (q :: qs)
      let rs := p54PairRound fp (q :: qs)
      let P := p54PolyDesc x ys
      let R := p54Horner fp x rs
      let A := p54AbsDesc x ys
      let H := p54Horner fp |x| (rs.map abs)
      let s := p.1 + p.2
      let r := fp.fl_add p.1 p.2
      let C := (1 + fp.u) ^ (2 * (q :: qs).length - 1)
      have hpow : 2 * ((q :: qs).length + 1) - 1 =
          (2 * (q :: qs).length - 1) + 2 := by
        simp only [List.length_cons]
        omega
      have hC : 1 ≤ C := by
        dsimp [C]
        exact one_le_pow₀ (by linarith [fp.u_nonneg])
      have hstep := p54_step_bounds fp hu x P R A H s r C hC
        ih'.2.2 (p54_poly_le_abs x ys)
        ih'.1 ih'.2.1 (fp.model_add p.1 p.2) (fp.inverse_add p.1 p.2)
      have hrne : p54PairRound fp (q :: qs) ≠ [] := by
        simp [p54PairRound]
      have hmapne : (p54PairRound fp (q :: qs)).map abs ≠ [] := by
        simp [p54PairRound]
      simpa only [p54_pair_exact_append, p54_pair_round_append,
        p54_poly_append, p54_abs_append, List.map_append,
        List.map_singleton,
        p54_horner_append_ne fp x _ _ hrne,
        p54_horner_append_ne fp |x| _ _ hmapne,
        List.length_append, List.length_singleton, hpow, pow_add,
        pow_two, ys, rs, P, R, A, H, s, r, C] using hstep

private lemma p54_pow_gamma (u : ℝ) (hu : 0 ≤ u)
    (k : ℕ) (hk : P54GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p54Gamma u k := by
  have hprod : ∀ j : ℕ, P54GammaValid u j →
      (1 + u) ^ j * (1 - (j : ℝ) * u) ≤ 1 := by
    intro j
    induction j with
    | zero => simp [P54GammaValid]
    | succ j ih =>
      intro hj
      have hj' : P54GammaValid u j := by
        dsimp [P54GammaValid] at *
        push_cast at hj
        nlinarith
      have hstep : (1 + u) * (1 - ((j + 1 : ℕ) : ℝ) * u) ≤
          1 - (j : ℝ) * u := by
        push_cast
        have hn : 0 ≤ (j : ℝ) + 1 := by positivity
        have hsq : 0 ≤ ((j : ℝ) + 1) * u ^ 2 := by positivity
        nlinarith
      have hp : 0 ≤ (1 + u) ^ j := pow_nonneg (by linarith) _
      have hm := mul_le_mul_of_nonneg_left hstep hp
      have hi := ih hj'
      rw [pow_succ]
      nlinarith
  have hd : 0 < 1 - (k : ℝ) * u := by
    dsimp [P54GammaValid] at hk
    linarith
  have hp := hprod k hk
  unfold p54Gamma
  apply (le_div_iff₀ hd).2
  nlinarith

private lemma p54_pair_exact_zip (a b : List ℝ) :
    p54PairExact (List.zip a b) = p54SumCoeffs a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      change (x + y) :: p54PairExact (List.zip xs ys) =
        (x + y) :: p54SumCoeffs xs ys
      exact congrArg (List.cons (x + y)) (ih ys)

private lemma p54_pair_round_zip (fp : P54FPModel) (a b : List ℝ) :
    p54PairRound fp (List.zip a b) = p54RoundedSumCoeffs fp a b := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      change fp.fl_add x y :: p54PairRound fp (List.zip xs ys) =
        fp.fl_add x y :: p54RoundedSumCoeffs fp xs ys
      exact congrArg (List.cons (fp.fl_add x y)) (ih ys)

/-- Both displayed conclusions (7) and (8) of Langlois--Louvet Lemma 1. -/
theorem p54_c2_lemma1 (fp : P54FPModel) (x : ℝ)
    (n : ℕ) (a b : List ℝ)
    (ha : a.length = n + 1) (hb : b.length = n + 1)
    (hvalid : P54GammaValid fp.u (2 * n + 1)) :
    |p54PolyDesc x (p54SumCoeffs a b) -
      p54Horner fp x (p54RoundedSumCoeffs fp a b)| ≤
        p54Gamma fp.u (2 * n + 1) *
          p54AbsDesc x (p54SumCoeffs a b) ∧
    p54AbsDesc x (p54SumCoeffs a b) ≤
      (1 + fp.u) ^ (2 * n + 1) *
        p54Horner fp |x|
          ((p54RoundedSumCoeffs fp a b).map abs) := by
  -- PROOF_START P54-C2-H001
  let cs := List.zip a b
  have hlen : cs.length = n + 1 := by
    simp [cs, List.length_zip, ha, hb]
  have hne : cs ≠ [] := by
    intro he
    have := congrArg List.length he
    rw [hlen] at this
    simp at this
  have hku : (1 : ℝ) ≤ (2 * n + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
  have hu : fp.u < 1 := by
    have hm := mul_le_mul_of_nonneg_right hku fp.u_nonneg
    dsimp [P54GammaValid] at hvalid
    nlinarith
  have hpair := p54_pair_bounds fp hu x cs hne
  have hk : 2 * cs.length - 1 = 2 * n + 1 := by
    rw [hlen]
    omega
  rw [hk] at hpair
  have he : p54PairExact cs = p54SumCoeffs a b :=
    p54_pair_exact_zip a b
  have hr : p54PairRound fp cs = p54RoundedSumCoeffs fp a b :=
    p54_pair_round_zip fp a b
  rw [he, hr] at hpair
  have hγ := p54_pow_gamma fp.u fp.u_nonneg (2 * n + 1) hvalid
  constructor
  · exact hpair.1.trans
      (mul_le_mul_of_nonneg_right hγ
        (p54_abs_nonneg x (p54SumCoeffs a b)))
  · exact hpair.2.1

end VSCLReuse

import VSCLReuse.P54.Definitions

namespace VSCLReuse

private lemma p54_mul_zero (fp : P54FPModel) (x : ℝ) : fp.fl_mul x 0 = 0 := by
  obtain ⟨δ, _, hδ⟩ := fp.model_mul x 0
  simpa using hδ

private lemma p54_poly_fold_aux (x z : ℝ) (l : List ℝ) :
    l.foldl (fun y a => x * y + a) z = z * x ^ l.length + p54PolyDesc x l := by
  induction l generalizing z with
  | nil => simp [p54PolyDesc]
  | cons a l ih =>
      simp only [List.foldl_cons, List.length_cons, p54PolyDesc]
      rw [ih]
      simp only [pow_succ]
      ring

private lemma p54_poly_fold (x : ℝ) (l : List ℝ) :
    p54PolyDesc x l = l.foldl (fun y a => x * y + a) 0 := by
  rw [p54_poly_fold_aux]
  simp

private lemma p54_abs_fold_aux (x z : ℝ) (l : List ℝ) :
    l.foldl (fun y a => |x| * y + |a|) z =
      z * |x| ^ l.length + p54AbsDesc x l := by
  induction l generalizing z with
  | nil => simp [p54AbsDesc]
  | cons a l ih =>
      simp only [List.foldl_cons, List.length_cons, p54AbsDesc]
      rw [ih]
      simp only [pow_succ]
      ring

private lemma p54_abs_fold (x : ℝ) (l : List ℝ) :
    p54AbsDesc x l = l.foldl (fun y a => |x| * y + |a|) 0 := by
  rw [p54_abs_fold_aux]
  simp

private lemma p54_horner_fold (fp : P54FPModel) (x : ℝ) (l : List ℝ) :
    p54Horner fp x l =
      l.foldl (fun y a => fp.fl_add (fp.fl_mul x y) a) 0 := by
  cases l with
  | nil => simp [p54Horner]
  | cons a l =>
      simp [p54Horner, p54_mul_zero, fp.fl_add_zero]

private lemma p54_forward_abs (u c r : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ r = c * (1 + δ)) :
    |r| ≤ (1 + u) * |c| ∧ |r - c| ≤ u * |c| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have ht : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  constructor
  · rw [abs_mul]
    calc
      |c| * |1 + δ| ≤ |c| * (1 + u) := mul_le_mul_of_nonneg_left ht (abs_nonneg c)
      _ = (1 + u) * |c| := by ring
  · have heq : c * (1 + δ) - c = c * δ := by ring
    rw [heq, abs_mul, mul_comm u]
    exact mul_le_mul_of_nonneg_left hδ (abs_nonneg c)

private lemma p54_inverse_abs (u c r : ℝ)
    (h : ∃ ε : ℝ, |ε| ≤ u ∧ c = r * (1 + ε)) :
    |c| ≤ (1 + u) * |r| := by
  obtain ⟨ε, hε, rfl⟩ := h
  rw [abs_mul]
  have ht : |1 + ε| ≤ 1 + u := by
    calc
      |1 + ε| ≤ |(1 : ℝ)| + |ε| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hε 1
  calc
    |r| * |1 + ε| ≤ |r| * (1 + u) := mul_le_mul_of_nonneg_left ht (abs_nonneg r)
    _ = (1 + u) * |r| := by ring

private lemma p54_round_nonneg (u c r : ℝ) (hu : u < 1) (hc : 0 ≤ c)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ r = c * (1 + δ)) : 0 ≤ r := by
  obtain ⟨δ, hδ, rfl⟩ := h
  apply mul_nonneg hc
  nlinarith [neg_abs_le δ]

private lemma p54_forward_step (fp : P54FPModel) (x e h B C a b : ℝ)
    (hB : 0 ≤ B) (hC : 1 ≤ C)
    (he : |e| ≤ B) (hh : |h| ≤ C * B)
    (herr : |e - h| ≤ (C - 1) * B) :
    let e' := x * e + (a + b)
    let h' := fp.fl_add (fp.fl_mul x h) (fp.fl_add a b)
    let B' := |x| * B + |a + b|
    0 ≤ B' ∧ |e'| ≤ B' ∧
      |h'| ≤ (1 + fp.u) ^ 2 * C * B' ∧
      |e' - h'| ≤ ((1 + fp.u) ^ 2 * C - 1) * B' := by
  dsimp
  let c := a + b
  let s := fp.fl_add a b
  let m := fp.fl_mul x h
  let h' := fp.fl_add m s
  let t := 1 + fp.u
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc : 0 ≤ |c| := abs_nonneg _
  have hx : 0 ≤ |x| := abs_nonneg _
  have hmul := p54_forward_abs fp.u (x * h) m (fp.model_mul x h)
  have hcoef := p54_forward_abs fp.u c s (fp.model_add a b)
  have hadd := p54_forward_abs fp.u (m + s) h' (fp.model_add m s)
  have hm : |m| ≤ t * |x| * |h| := by
    simpa only [abs_mul, t, mul_assoc] using hmul.1
  have hme : |m - x * h| ≤ fp.u * |x| * |h| := by
    simpa only [abs_mul, mul_assoc] using hmul.2
  have hs : |s| ≤ t * |c| := hcoef.1
  have hse : |s - c| ≤ fp.u * |c| := hcoef.2
  have hround : |h'| ≤ t * (|m| + |s|) := by
    calc
      |h'| ≤ t * |m + s| := hadd.1
      _ ≤ t * (|m| + |s|) := mul_le_mul_of_nonneg_left (abs_add_le m s) ht
  have hround_err : |h' - (m + s)| ≤ fp.u * (|m| + |s|) := by
    calc
      |h' - (m + s)| ≤ fp.u * |m + s| := hadd.2
      _ ≤ fp.u * (|m| + |s|) := mul_le_mul_of_nonneg_left (abs_add_le m s) hu
  have hB' : 0 ≤ |x| * B + |c| := add_nonneg (mul_nonneg hx hB) hc
  have he' : |x * e + c| ≤ |x| * B + |c| := by
    calc
      |x * e + c| ≤ |x * e| + |c| := abs_add_le _ _
      _ ≤ |x| * B + |c| := by rw [abs_mul]; gcongr
  have hhh : |h'| ≤ t ^ 2 * C * (|x| * B + |c|) := by
    calc
      |h'| ≤ t * (|m| + |s|) := hround
      _ ≤ t * (t * |x| * |h| + t * |c|) := by gcongr
      _ ≤ t * (t * |x| * (C * B) + t * |c|) := by gcongr
      _ ≤ t ^ 2 * C * (|x| * B + |c|) := by
        have hC0 : 0 ≤ C := by linarith
        have hct : |c| ≤ C * |c| := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hc]
        nlinarith [mul_nonneg (mul_nonneg ht ht) (mul_nonneg hC0 (mul_nonneg hx hB))]
  have hEcomp : |(x * e + c) - h'| ≤
      |x| * |e - h| + |m - x * h| + |s - c| + |h' - (m + s)| := by
    have hid : (x * e + c) - h' = x * (e - h) - (m - x * h) - (s - c) - (h' - (m + s)) := by ring
    rw [hid]
    calc
      |x * (e - h) - (m - x * h) - (s - c) - (h' - (m + s))| ≤
          |x * (e - h)| + |m - x * h| + |s - c| + |h' - (m + s)| := by
            calc
              _ ≤ |x * (e - h) - (m - x * h) - (s - c)| + |h' - (m + s)| := by
                simpa only [sub_zero, zero_sub, abs_neg] using
                  (abs_sub_le (x * (e - h) - (m - x * h) - (s - c)) 0 (h' - (m + s)))
              _ ≤ _ := by
                have h1 : |x * (e - h) - (m - x * h) - (s - c)| ≤
                    |x * (e - h) - (m - x * h)| + |s - c| := by
                  simpa only [sub_zero, zero_sub, abs_neg] using
                    (abs_sub_le (x * (e - h) - (m - x * h)) 0 (s - c))
                have h2 : |x * (e - h) - (m - x * h)| ≤
                    |x * (e - h)| + |m - x * h| := by
                  simpa only [sub_zero, zero_sub, abs_neg] using
                    (abs_sub_le (x * (e - h)) 0 (m - x * h))
                linarith
      _ = _ := by rw [abs_mul]
  have herr' : |(x * e + c) - h'| ≤
      (t ^ 2 * C - 1) * (|x| * B + |c|) := by
    have h1 : |x| * |e - h| ≤ |x| * ((C - 1) * B) :=
      mul_le_mul_of_nonneg_left herr hx
    have h2 : fp.u * |x| * |h| ≤ fp.u * |x| * (C * B) := by gcongr
    have h3 : |m| ≤ t * |x| * (C * B) := hm.trans (by gcongr)
    have h4 : |s| ≤ t * |c| := hs
    have h5 : (t ^ 2 - 1) * |c| ≤ (t ^ 2 * C - 1) * |c| := by
      have hC0 : 0 ≤ C - 1 := by linarith
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (mul_nonneg ht2 hC0) hc]
    nlinarith [hEcomp, hme, hse, hround_err,
      mul_le_mul_of_nonneg_left h3 hu,
      mul_le_mul_of_nonneg_left h4 hu]
  exact ⟨hB', he', hhh, herr'⟩

private lemma p54_inverse_step (fp : P54FPModel) (x B R C a b : ℝ)
    (hu : fp.u < 1) (hR : 0 ≤ R) (hC : 1 ≤ C)
    (hBR : B ≤ C * R) :
    let B' := |x| * B + |a + b|
    let R' := fp.fl_add (fp.fl_mul |x| R) |fp.fl_add a b|
    0 ≤ R' ∧ B' ≤ (1 + fp.u) ^ 2 * C * R' := by
  dsimp
  let c := a + b
  let s := fp.fl_add a b
  let m := fp.fl_mul |x| R
  let R' := fp.fl_add m |s|
  let t := 1 + fp.u
  have hx : 0 ≤ |x| := abs_nonneg _
  have hc : 0 ≤ |c| := abs_nonneg _
  have hs : 0 ≤ |s| := abs_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; linarith [fp.u_nonneg]
  have hm : 0 ≤ m := p54_round_nonneg fp.u (|x| * R) m hu (mul_nonneg hx hR) (fp.model_mul |x| R)
  have hR' : 0 ≤ R' := p54_round_nonneg fp.u (m + |s|) R' hu (add_nonneg hm hs) (fp.model_add m |s|)
  have hcoef : |c| ≤ t * |s| := p54_inverse_abs fp.u c s (fp.inverse_add a b)
  have hmul : |x| * R ≤ t * m := by
    have h := p54_inverse_abs fp.u (|x| * R) m (fp.inverse_mul |x| R)
    simpa only [abs_mul, abs_of_nonneg hx, abs_of_nonneg hR, abs_of_nonneg hm, t] using h
  have hadd : m + |s| ≤ t * R' := by
    have h := p54_inverse_abs fp.u (m + |s|) R' (fp.inverse_add m |s|)
    simpa only [abs_of_nonneg (add_nonneg hm hs), abs_of_nonneg hR', t] using h
  constructor
  · exact hR'
  · calc
      |x| * B + |c| ≤ |x| * (C * R) + t * |s| := by gcongr
      _ ≤ C * (|x| * R) + C * t * |s| := by
        have hct : t * |s| ≤ C * (t * |s|) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg ht hs)]
        nlinarith
      _ ≤ C * (t * m) + C * t * |s| := by gcongr
      _ = C * t * (m + |s|) := by ring
      _ ≤ C * t * (t * R') := by gcongr
      _ = t ^ 2 * C * R' := by ring

private noncomputable def p54_exact_pairs (x : ℝ) (l : List (ℝ × ℝ)) : ℝ :=
  l.foldl (fun y p => x * y + (p.1 + p.2)) 0

private noncomputable def p54_abs_pairs (x : ℝ) (l : List (ℝ × ℝ)) : ℝ :=
  l.foldl (fun y p => |x| * y + |p.1 + p.2|) 0

private noncomputable def p54_round_pairs (fp : P54FPModel) (x : ℝ)
    (l : List (ℝ × ℝ)) : ℝ :=
  l.foldl (fun y p => fp.fl_add (fp.fl_mul x y) (fp.fl_add p.1 p.2)) 0

private noncomputable def p54_abs_round_pairs (fp : P54FPModel) (x : ℝ)
    (l : List (ℝ × ℝ)) : ℝ :=
  l.foldl (fun y p => fp.fl_add (fp.fl_mul |x| y) |fp.fl_add p.1 p.2|) 0

private lemma p54_pairs_bound (fp : P54FPModel) (x : ℝ) (p : ℝ × ℝ)
    (tail : List (ℝ × ℝ)) (hu : fp.u < 1) :
    let l := p :: tail
    let C := (1 + fp.u) ^ (2 * tail.length + 1)
    0 ≤ p54_abs_pairs x l ∧
    |p54_exact_pairs x l| ≤ p54_abs_pairs x l ∧
    |p54_round_pairs fp x l| ≤ C * p54_abs_pairs x l ∧
    |p54_exact_pairs x l - p54_round_pairs fp x l| ≤
      (C - 1) * p54_abs_pairs x l ∧
    0 ≤ p54_abs_round_pairs fp x l ∧
    p54_abs_pairs x l ≤ C * p54_abs_round_pairs fp x l := by
  induction tail using List.reverseRecOn with
  | nil =>
      dsimp
      simp only [p54_exact_pairs, p54_abs_pairs, p54_round_pairs,
        p54_abs_round_pairs, List.foldl_cons, List.foldl_nil,
        mul_zero, zero_add, pow_one, p54_mul_zero, fp.fl_add_zero]
      have hf := p54_forward_abs fp.u (p.1 + p.2) (fp.fl_add p.1 p.2)
        (fp.model_add p.1 p.2)
      have hi := p54_inverse_abs fp.u (p.1 + p.2) (fp.fl_add p.1 p.2)
        (fp.inverse_add p.1 p.2)
      have herr : |p.1 + p.2 - fp.fl_add p.1 p.2| ≤
          (1 + fp.u - 1) * |p.1 + p.2| := by
        rw [abs_sub_comm]
        simpa using hf.2
      exact ⟨abs_nonneg _, le_refl _, hf.1, herr, abs_nonneg _, hi⟩
  | @append_singleton tail q ih =>
      dsimp at ih ⊢
      let B := p54_abs_pairs x (p :: tail)
      let E := p54_exact_pairs x (p :: tail)
      let H := p54_round_pairs fp x (p :: tail)
      let R := p54_abs_round_pairs fp x (p :: tail)
      let C := (1 + fp.u) ^ (2 * tail.length + 1)
      have hC : 1 ≤ C := by
        apply one_le_pow₀
        dsimp
        linarith [fp.u_nonneg]
      have hf := p54_forward_step fp x E H B C q.1 q.2 ih.1 hC ih.2.1 ih.2.2.1 ih.2.2.2.1
      have hi := p54_inverse_step fp x B R C q.1 q.2 hu ih.2.2.2.2.1 hC ih.2.2.2.2.2
      have hpow : (1 + fp.u) ^ (2 * (tail ++ [q]).length + 1) =
          (1 + fp.u) ^ 2 * C := by
        dsimp [C]
        rw [List.length_append, List.length_singleton]
        have hn : 2 * (tail.length + 1) + 1 = (2 * tail.length + 1) + 2 := by omega
        rw [hn, pow_add]
        ring
      rw [hpow]
      have hl : p :: (tail ++ [q]) = (p :: tail) ++ [q] := by rfl
      rw [hl]
      simp only [p54_exact_pairs, p54_abs_pairs, p54_round_pairs,
        p54_abs_round_pairs, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at hf hi ⊢
      exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hi.1, hi.2⟩

private lemma p54_pow_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P54GammaValid u k) : (1 + u) ^ k - 1 ≤ p54Gamma u k := by
  have hpow : ∀ j : ℕ, P54GammaValid u j →
      (1 + u) ^ j * (1 - (j : ℝ) * u) ≤ 1 := by
    intro j
    induction j with
    | zero => simp [P54GammaValid]
    | succ j ih =>
        intro hj
        have hj' : P54GammaValid u j := by
          dsimp [P54GammaValid] at hj ⊢
          have hle : (j : ℝ) * u ≤ ((j + 1 : ℕ) : ℝ) * u := by
            push_cast
            nlinarith
          linarith
        have hp := ih hj'
        have ht : 0 ≤ 1 + u := by linarith
        have hs : (1 + u) * (1 - (((j + 1 : ℕ) : ℝ) * u)) ≤
            1 - (j : ℝ) * u := by
          have hnonneg : 0 ≤ (((j + 1 : ℕ) : ℝ) * u) * u :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hu
          push_cast at *
          nlinarith
        calc
          (1 + u) ^ (j + 1) * (1 - (((j + 1 : ℕ) : ℝ) * u)) =
              (1 + u) ^ j * ((1 + u) * (1 - (((j + 1 : ℕ) : ℝ) * u))) := by
                rw [pow_succ]; ring
          _ ≤ (1 + u) ^ j * (1 - (j : ℝ) * u) :=
            mul_le_mul_of_nonneg_left hs (pow_nonneg ht _)
          _ ≤ 1 := hp
  have hden : 0 < 1 - (k : ℝ) * u := by
    dsimp [P54GammaValid] at hk
    linarith
  have hp := hpow k hk
  unfold p54Gamma
  apply (le_div_iff₀ hden).2
  nlinarith

private lemma p54_exact_pairs_eq (x : ℝ) (a b : List ℝ) :
    p54_exact_pairs x (List.zip a b) = p54PolyDesc x (p54SumCoeffs a b) := by
  rw [p54_poly_fold]
  simp only [p54_exact_pairs, p54SumCoeffs, List.zipWith_foldl_eq_zip_foldl]

private lemma p54_abs_pairs_eq (x : ℝ) (a b : List ℝ) :
    p54_abs_pairs x (List.zip a b) = p54AbsDesc x (p54SumCoeffs a b) := by
  rw [p54_abs_fold]
  simp only [p54_abs_pairs, p54SumCoeffs, List.zipWith_foldl_eq_zip_foldl]

private lemma p54_round_pairs_eq (fp : P54FPModel) (x : ℝ) (a b : List ℝ) :
    p54_round_pairs fp x (List.zip a b) =
      p54Horner fp x (p54RoundedSumCoeffs fp a b) := by
  rw [p54_horner_fold]
  simp only [p54_round_pairs, p54RoundedSumCoeffs, List.zipWith_foldl_eq_zip_foldl]

private lemma p54_abs_round_pairs_eq (fp : P54FPModel) (x : ℝ) (a b : List ℝ) :
    p54_abs_round_pairs fp x (List.zip a b) =
      p54Horner fp |x| ((p54RoundedSumCoeffs fp a b).map abs) := by
  rw [p54_horner_fold]
  simp only [p54_abs_round_pairs, p54RoundedSumCoeffs, List.foldl_map,
    List.zipWith_foldl_eq_zip_foldl]

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
  cases a with
  | nil => simp at ha
  | cons a as =>
      cases b with
      | nil => simp at hb
      | cons b bs =>
          have has : as.length = n := by simp at ha; omega
          have hbs : bs.length = n := by simp at hb; omega
          have htail : (List.zip as bs).length = n := by
            simp [List.length_zip, has, hbs]
          have hu : fp.u < 1 := by
            have hkn : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
              exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
            have hmul : fp.u ≤ ((2 * n + 1 : ℕ) : ℝ) * fp.u := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hkn) fp.u_nonneg]
            exact lt_of_le_of_lt hmul hvalid
          have hpairs := p54_pairs_bound fp x (a, b) (List.zip as bs) hu
          dsimp at hpairs
          rw [htail] at hpairs
          have hzip : (a, b) :: List.zip as bs = List.zip (a :: as) (b :: bs) := rfl
          rw [hzip, p54_exact_pairs_eq, p54_abs_pairs_eq,
            p54_round_pairs_eq, p54_abs_round_pairs_eq] at hpairs
          have hgamma := p54_pow_gamma fp.u fp.u_nonneg (2 * n + 1) hvalid
          constructor
          · exact hpairs.2.2.2.1.trans
              (mul_le_mul_of_nonneg_right hgamma hpairs.1)
          · exact hpairs.2.2.2.2.2

end VSCLReuse

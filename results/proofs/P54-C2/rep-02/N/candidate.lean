import VSCLReuse.P54.Definitions

namespace VSCLReuse

private theorem p54_poly_append (x : ℝ) (l : List ℝ) (c : ℝ) :
    p54PolyDesc x (l ++ [c]) = x * p54PolyDesc x l + c := by
  induction l with
  | nil => simp [p54PolyDesc]
  | cons a l ih =>
      simp only [List.cons_append, p54PolyDesc, List.length_append,
        List.length_singleton, pow_add, pow_one]
      rw [ih]
      ring

private theorem p54_abs_append (x : ℝ) (l : List ℝ) (c : ℝ) :
    p54AbsDesc x (l ++ [c]) = |x| * p54AbsDesc x l + |c| := by
  induction l with
  | nil => simp [p54AbsDesc]
  | cons a l ih =>
      simp only [List.cons_append, p54AbsDesc, List.length_append,
        List.length_singleton, pow_add, pow_one]
      rw [ih]
      ring

private theorem p54_poly_fold (x : ℝ) (l : List ℝ) :
    p54PolyDesc x l = l.foldl (fun v c => x * v + c) 0 := by
  induction l using List.reverseRecOn with
  | nil => simp [p54PolyDesc]
  | append_singleton l c ih =>
      rw [p54_poly_append, List.foldl_append, ← ih]
      simp

private theorem p54_abs_fold (x : ℝ) (l : List ℝ) :
    p54AbsDesc x l = l.foldl (fun v c => |x| * v + |c|) 0 := by
  induction l using List.reverseRecOn with
  | nil => simp [p54AbsDesc]
  | append_singleton l c ih =>
      rw [p54_abs_append, List.foldl_append, ← ih]
      simp

private theorem p54_horner_fold (fp : P54FPModel) (x : ℝ) (l : List ℝ) :
    p54Horner fp x l =
      l.foldl (fun v c => fp.fl_add (fp.fl_mul x v) c) 0 := by
  cases l with
  | nil => simp [p54Horner]
  | cons c cs =>
      have hm : fp.fl_mul x 0 = 0 := by
        obtain ⟨δ, _, hδ⟩ := fp.model_mul x 0
        simpa using hδ
      simp [p54Horner, hm, fp.fl_add_zero]

private theorem p54_pow_gamma (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hk : P54GammaValid u k) :
    (1 + u) ^ k - 1 ≤ p54Gamma u k := by
  have hp : ∀ m : ℕ, (1 + u) ^ m * (1 - (m : ℝ) * u) ≤ 1 := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        have hpow : 0 ≤ (1 + u) ^ m := pow_nonneg (by linarith) _
        have hstep : (1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u) ≤
            1 - (m : ℝ) * u := by
          push_cast
          nlinarith [sq_nonneg u]
        rw [pow_succ]
        calc
          (1 + u) ^ m * (1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u) =
              (1 + u) ^ m * ((1 + u) * (1 - ((m + 1 : ℕ) : ℝ) * u)) := by ring
          _ ≤ (1 + u) ^ m * (1 - (m : ℝ) * u) :=
            mul_le_mul_of_nonneg_left hstep hpow
          _ ≤ 1 := ih
  have hden : 0 < 1 - (k : ℝ) * u := by
    dsimp [P54GammaValid] at hk
    linarith
  unfold p54Gamma
  apply (le_div_iff₀ hden).2
  nlinarith [hp k]

private theorem p54_rel_error (u v w : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ w = v * (1 + δ)) :
    |v - w| ≤ u * |v| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have heq : v - v * (1 + δ) = -(v * δ) := by ring
  rw [heq, abs_neg, abs_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg v)

private theorem p54_rel_abs (u v w : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ w = v * (1 + δ)) :
    |w| ≤ (1 + u) * |v| := by
  obtain ⟨δ, hδ, rfl⟩ := h
  rw [abs_mul]
  have hfac : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  nlinarith [mul_le_mul_of_nonneg_left hfac (abs_nonneg v)]

private theorem p54_rel_nonneg (u v w : ℝ) (hu : u < 1)
    (hv : 0 ≤ v)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ w = v * (1 + δ)) :
    0 ≤ w := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have hfactor : 0 ≤ 1 + δ := by
    have := neg_abs_le δ
    linarith
  exact mul_nonneg hv hfactor

private theorem p54_add_error (fp : P54FPModel) (v w : ℝ) :
    |v + w - fp.fl_add v w| ≤ fp.u * |v + w| :=
  p54_rel_error fp.u (v + w) (fp.fl_add v w) (fp.model_add v w)

private theorem p54_mul_error (fp : P54FPModel) (v w : ℝ) :
    |v * w - fp.fl_mul v w| ≤ fp.u * |v * w| :=
  p54_rel_error fp.u (v * w) (fp.fl_mul v w) (fp.model_mul v w)

private theorem p54_add_abs (fp : P54FPModel) (v w : ℝ) :
    |fp.fl_add v w| ≤ (1 + fp.u) * |v + w| :=
  p54_rel_abs fp.u (v + w) (fp.fl_add v w) (fp.model_add v w)

private theorem p54_mul_abs (fp : P54FPModel) (v w : ℝ) :
    |fp.fl_mul v w| ≤ (1 + fp.u) * |v * w| :=
  p54_rel_abs fp.u (v * w) (fp.fl_mul v w) (fp.model_mul v w)

private theorem p54_add_nonneg (fp : P54FPModel) (hu : fp.u < 1)
    (v w : ℝ) (hv : 0 ≤ v + w) : 0 ≤ fp.fl_add v w :=
  p54_rel_nonneg fp.u (v + w) (fp.fl_add v w) hu hv (fp.model_add v w)

private theorem p54_mul_nonneg (fp : P54FPModel) (hu : fp.u < 1)
    (v w : ℝ) (hv : 0 ≤ v * w) : 0 ≤ fp.fl_mul v w :=
  p54_rel_nonneg fp.u (v * w) (fp.fl_mul v w) hu hv (fp.model_mul v w)

private theorem p54_inverse_abs (u v w : ℝ)
    (h : ∃ ε : ℝ, |ε| ≤ u ∧ v = w * (1 + ε)) :
    |v| ≤ (1 + u) * |w| :=
  p54_rel_abs u w v h

private theorem p54_add_inverse (fp : P54FPModel) (v w : ℝ) :
    |v + w| ≤ (1 + fp.u) * |fp.fl_add v w| :=
  p54_inverse_abs fp.u (v + w) (fp.fl_add v w) (fp.inverse_add v w)

private theorem p54_mul_inverse (fp : P54FPModel) (v w : ℝ) :
    |v * w| ≤ (1 + fp.u) * |fp.fl_mul v w| :=
  p54_inverse_abs fp.u (v * w) (fp.fl_mul v w) (fp.inverse_mul v w)

private theorem p54_step_error (fp : P54FPModel) (x e r c d : ℝ)
    (hd : |c - d| ≤ fp.u * |c|)
    (hdabs : |d| ≤ (1 + fp.u) * |c|) :
    |x * e + c - fp.fl_add (fp.fl_mul x r) d| ≤
      |x| * |e - r| + ((1 + fp.u) ^ 2 - 1) * (|x| * |r| + |c|) := by
  let s := fp.fl_mul x r
  let t := fp.fl_add s d
  have htri : |x * e + c - t| ≤
      |x| * |e - r| + |c - d| + |x * r - s| + |s + d - t| := by
    have heq : x * e + c - t = x * (e - r) + (c - d) + (x * r - s) +
        (s + d - t) := by ring
    rw [heq]
    calc
      |x * (e - r) + (c - d) + (x * r - s) + (s + d - t)| ≤
          |x * (e - r) + (c - d) + (x * r - s)| + |s + d - t| :=
        abs_add_le _ _
      _ ≤ (|x * (e - r) + (c - d)| + |x * r - s|) + |s + d - t| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |x| * |e - r| + |c - d| + |x * r - s| + |s + d - t| := by
        have hh := abs_add_le (x * (e - r)) (c - d)
        rw [abs_mul] at hh
        linarith
  have hm : |x * r - s| ≤ fp.u * (|x| * |r|) := by
    simpa only [s, abs_mul] using p54_mul_error fp x r
  have hs : |s| ≤ (1 + fp.u) * (|x| * |r|) := by
    simpa only [s, abs_mul] using p54_mul_abs fp x r
  have ha : |s + d - t| ≤ fp.u * (|s| + |d|) := by
    calc
      |s + d - t| ≤ fp.u * |s + d| := p54_add_error fp s d
      _ ≤ fp.u * (|s| + |d|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le s d) fp.u_nonneg
  have hsmul := mul_le_mul_of_nonneg_left hs fp.u_nonneg
  have hdmul := mul_le_mul_of_nonneg_left hdabs fp.u_nonneg
  change |x * e + c - t| ≤ _
  nlinarith [sq_nonneg fp.u]

private theorem p54_step_forward (fp : P54FPModel) (x e A r c d : ℝ)
    (k : ℕ) (hA : 0 ≤ A) (he : |e| ≤ A)
    (herr : |e - r| ≤ ((1 + fp.u) ^ k - 1) * A)
    (hd : |c - d| ≤ fp.u * |c|)
    (hdabs : |d| ≤ (1 + fp.u) * |c|) :
    0 ≤ |x| * A + |c| ∧
    |x * e + c| ≤ |x| * A + |c| ∧
    |x * e + c - fp.fl_add (fp.fl_mul x r) d| ≤
      ((1 + fp.u) ^ (k + 2) - 1) * (|x| * A + |c|) := by
  let U : ℝ := 1 + fp.u
  let T : ℝ := U ^ k
  let V : ℝ := U ^ 2
  have hU : 1 ≤ U := by dsimp [U]; linarith [fp.u_nonneg]
  have hT : 1 ≤ T := by
    dsimp [T]
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hU k
  have hV : 1 ≤ V := by dsimp [V]; nlinarith [sq_nonneg U]
  have hr : |r| ≤ T * A := by
    have htri : |r| ≤ |e| + |e - r| := by
      have hh := abs_sub_le e 0 (e - r)
      have heq : e - (e - r) = r := by ring
      simpa only [sub_zero, zero_sub, abs_neg, heq] using hh
    dsimp [T, U]
    linarith
  have hcoef : V - 1 ≤ T * V - 1 := by nlinarith
  have hlocal := p54_step_error fp x e r c d hd hdabs
  have hmulE := mul_le_mul_of_nonneg_left herr (abs_nonneg x)
  have hmulR := mul_le_mul_of_nonneg_left hr
      (mul_nonneg (by linarith : 0 ≤ V - 1) (abs_nonneg x))
  have hcoeff := mul_le_mul_of_nonneg_right hcoef (abs_nonneg c)
  have hnew :
      |x * e + c - fp.fl_add (fp.fl_mul x r) d| ≤
        (T * V - 1) * (|x| * A + |c|) := by
    change |x * e + c - fp.fl_add (fp.fl_mul x r) d| ≤
      |x| * |e - r| + (V - 1) * (|x| * |r| + |c|) at hlocal
    change |x| * |e - r| ≤ |x| * ((T - 1) * A) at hmulE
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · calc
      |x * e + c| ≤ |x * e| + |c| := abs_add_le _ _
      _ ≤ |x| * A + |c| := by
        rw [abs_mul]
        gcongr
  · convert hnew using 1
    simp [T, V, U, pow_add]

private theorem p54_step_inverse (fp : P54FPModel) (x A R c d : ℝ)
    (hu : fp.u < 1) (k : ℕ) (hR : 0 ≤ R)
    (hA : A ≤ (1 + fp.u) ^ k * R)
    (hd : |c| ≤ (1 + fp.u) * |d|) :
    0 ≤ fp.fl_add (fp.fl_mul |x| R) |d| ∧
    |x| * A + |c| ≤
      (1 + fp.u) ^ (k + 2) * fp.fl_add (fp.fl_mul |x| R) |d| := by
  let U : ℝ := 1 + fp.u
  let T : ℝ := U ^ k
  let s := fp.fl_mul |x| R
  let t := fp.fl_add s |d|
  have hU : 1 ≤ U := by dsimp [U]; linarith [fp.u_nonneg]
  have hT : 1 ≤ T := by
    dsimp [T]
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hU k
  have hs0 : 0 ≤ s :=
    p54_mul_nonneg fp hu |x| R (mul_nonneg (abs_nonneg x) hR)
  have ht0 : 0 ≤ t :=
    p54_add_nonneg fp hu s |d| (add_nonneg hs0 (abs_nonneg d))
  have hsinv : |x| * R ≤ U * s := by
    have hh := p54_mul_inverse fp |x| R
    simpa only [abs_mul, abs_abs, abs_of_nonneg hR, abs_of_nonneg hs0, U, s] using hh
  have htinv : s + |d| ≤ U * t := by
    have hh := p54_add_inverse fp s |d|
    simpa only [abs_of_nonneg (add_nonneg hs0 (abs_nonneg d)),
      abs_of_nonneg ht0, U, t] using hh
  have hmulA := mul_le_mul_of_nonneg_left hA (abs_nonneg x)
  have hmulS := mul_le_mul_of_nonneg_left hsinv (by linarith : 0 ≤ T)
  have hmulT := mul_le_mul_of_nonneg_left htinv
      (mul_nonneg (by linarith : 0 ≤ T) (by linarith : 0 ≤ U))
  have hcoeff : U * |d| ≤ T * U * |d| := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hT)
      (mul_nonneg (by linarith : 0 ≤ U) (abs_nonneg d))]
  refine ⟨ht0, ?_⟩
  change A ≤ T * R at hA
  change |c| ≤ U * |d| at hd
  change |x| * A ≤ |x| * (T * R) at hmulA
  change |x| * R ≤ U * s at hsinv
  change T * (|x| * R) ≤ T * (U * s) at hmulS
  change (T * U) * (s + |d|) ≤ (T * U) * (U * t) at hmulT
  have hpow : (1 + fp.u) ^ (k + 2) = T * U * U := by
    simp only [T, U, pow_add, pow_two]
    ring
  rw [hpow]
  nlinarith

private theorem p54_fold_bounds (fp : P54FPModel) (x : ℝ)
    (hu : fp.u < 1) (cs ds : List ℝ)
    (hrel : List.Forall₂ (fun c d : ℝ =>
      |c - d| ≤ fp.u * |c| ∧
      |d| ≤ (1 + fp.u) * |c| ∧
      |c| ≤ (1 + fp.u) * |d|) cs ds)
    (e A r R : ℝ) (k : ℕ)
    (hA : 0 ≤ A) (he : |e| ≤ A)
    (herr : |e - r| ≤ ((1 + fp.u) ^ k - 1) * A)
    (hR : 0 ≤ R) (hinv : A ≤ (1 + fp.u) ^ k * R) :
    0 ≤ cs.foldl (fun v c => |x| * v + |c|) A ∧
    |cs.foldl (fun v c => x * v + c) e| ≤
      cs.foldl (fun v c => |x| * v + |c|) A ∧
    |cs.foldl (fun v c => x * v + c) e -
      ds.foldl (fun v d => fp.fl_add (fp.fl_mul x v) d) r| ≤
      ((1 + fp.u) ^ (k + 2 * cs.length) - 1) *
        cs.foldl (fun v c => |x| * v + |c|) A ∧
    0 ≤ ds.foldl (fun v d => fp.fl_add (fp.fl_mul |x| v) |d|) R ∧
    cs.foldl (fun v c => |x| * v + |c|) A ≤
      (1 + fp.u) ^ (k + 2 * cs.length) *
        ds.foldl (fun v d => fp.fl_add (fp.fl_mul |x| v) |d|) R := by
  induction hrel generalizing e A r R k with
  | nil =>
      simpa using And.intro hA (And.intro he (And.intro herr (And.intro hR hinv)))
  | @cons c d cs ds hcd htail ih =>
      rcases hcd with ⟨hd, hdabs, hdinv⟩
      obtain ⟨hA', he', herr'⟩ :=
        p54_step_forward fp x e A r c d k hA he herr hd hdabs
      obtain ⟨hR', hinv'⟩ :=
        p54_step_inverse fp x A R c d hu k hR hinv hdinv
      have hh := ih (x * e + c) (|x| * A + |c|)
        (fp.fl_add (fp.fl_mul x r) d)
        (fp.fl_add (fp.fl_mul |x| R) |d|) (k + 2)
        hA' he' herr' hR' hinv'
      have hexp : k + 2 * (cs.length + 1) = (k + 2) + 2 * cs.length := by omega
      simpa only [List.foldl_cons, List.length_cons, Nat.succ_eq_add_one,
        hexp] using hh

private theorem p54_coeff_rel (fp : P54FPModel) (a b : List ℝ) :
    List.Forall₂ (fun c d : ℝ =>
      |c - d| ≤ fp.u * |c| ∧
      |d| ≤ (1 + fp.u) * |c| ∧
      |c| ≤ (1 + fp.u) * |d|)
      (p54SumCoeffs a b) (p54RoundedSumCoeffs fp a b) := by
  induction a generalizing b with
  | nil =>
      cases b <;> exact List.Forall₂.nil
  | cons aa as ih =>
      cases b with
      | nil => exact List.Forall₂.nil
      | cons bb bs =>
          apply List.Forall₂.cons
          · exact ⟨p54_add_error fp aa bb, p54_add_abs fp aa bb,
              p54_add_inverse fp aa bb⟩
          · exact ih bs

private theorem p54_pair_bounds (fp : P54FPModel) (x : ℝ)
    (n : ℕ) (cs ds : List ℝ)
    (hrel : List.Forall₂ (fun c d : ℝ =>
      |c - d| ≤ fp.u * |c| ∧
      |d| ≤ (1 + fp.u) * |c| ∧
      |c| ≤ (1 + fp.u) * |d|) cs ds)
    (hlen : cs.length = n + 1)
    (hvalid : P54GammaValid fp.u (2 * n + 1)) :
    |p54PolyDesc x cs - p54Horner fp x ds| ≤
      p54Gamma fp.u (2 * n + 1) * p54AbsDesc x cs ∧
    p54AbsDesc x cs ≤
      (1 + fp.u) ^ (2 * n + 1) * p54Horner fp |x| (ds.map abs) := by
  have hu : fp.u < 1 := by
    have hn : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
    have hk : fp.u ≤ ((2 * n + 1 : ℕ) : ℝ) * fp.u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
    dsimp [P54GammaValid] at hvalid
    linarith
  cases hrel with
  | nil => simp at hlen
  | @cons c d cs ds hc htail =>
      have hcs : cs.length = n := by
        simp only [List.length_cons] at hlen
        omega
      have hrun := p54_fold_bounds fp x hu cs ds htail c |c| d |d| 1
        (abs_nonneg c) le_rfl (by simpa [pow_one] using hc.1)
        (abs_nonneg d) (by simpa [pow_one] using hc.2.2)
      have hpoly : p54PolyDesc x (c :: cs) =
          cs.foldl (fun v c => x * v + c) c := by
        rw [p54_poly_fold]
        simp
      have habs : p54AbsDesc x (c :: cs) =
          cs.foldl (fun v c => |x| * v + |c|) |c| := by
        rw [p54_abs_fold]
        simp
      have hhorner : p54Horner fp x (d :: ds) =
          ds.foldl (fun v d => fp.fl_add (fp.fl_mul x v) d) d := rfl
      have hhornerAbs : p54Horner fp |x| ((d :: ds).map abs) =
          ds.foldl (fun v d => fp.fl_add (fp.fl_mul |x| v) |d|) |d| := by
        simp [p54Horner, List.foldl_map]
      have hexp : 1 + 2 * cs.length = 2 * n + 1 := by omega
      constructor
      · rw [hpoly, hhorner, habs]
        calc
          |cs.foldl (fun v c => x * v + c) c -
              ds.foldl (fun v d => fp.fl_add (fp.fl_mul x v) d) d| ≤
              ((1 + fp.u) ^ (1 + 2 * cs.length) - 1) *
                cs.foldl (fun v c => |x| * v + |c|) |c| := hrun.2.2.1
          _ ≤ p54Gamma fp.u (2 * n + 1) *
              cs.foldl (fun v c => |x| * v + |c|) |c| := by
            rw [hexp]
            exact mul_le_mul_of_nonneg_right
              (p54_pow_gamma fp.u fp.u_nonneg (2 * n + 1) hvalid) hrun.1
      · rw [habs, hhornerAbs]
        simpa only [hexp] using hrun.2.2.2.2

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
  have hlen : (p54SumCoeffs a b).length = n + 1 := by
    simp [p54SumCoeffs, List.length_zipWith, ha, hb]
  exact p54_pair_bounds fp x n (p54SumCoeffs a b)
    (p54RoundedSumCoeffs fp a b) (p54_coeff_rel fp a b) hlen hvalid

end VSCLReuse

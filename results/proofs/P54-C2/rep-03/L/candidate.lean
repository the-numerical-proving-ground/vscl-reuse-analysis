import VSCLReuse.P54.Definitions
import NumStability.Analysis.Rounding

namespace VSCLReuse

private lemma p54_poly_append (x : ℝ) (cs : List ℝ) (c : ℝ) :
    p54PolyDesc x (cs ++ [c]) = x * p54PolyDesc x cs + c := by
  induction cs with
  | nil => simp [p54PolyDesc]
  | cons a cs ih =>
      simp only [List.cons_append, p54PolyDesc, List.length_append,
        List.length_singleton, pow_succ]
      rw [ih]
      ring

private lemma p54_abs_append (x : ℝ) (cs : List ℝ) (c : ℝ) :
    p54AbsDesc x (cs ++ [c]) = |x| * p54AbsDesc x cs + |c| := by
  induction cs with
  | nil => simp [p54AbsDesc]
  | cons a cs ih =>
      simp only [List.cons_append, p54AbsDesc, List.length_append,
        List.length_singleton, pow_succ]
      rw [ih]
      ring

private lemma p54_horner_append (fp : P54FPModel) (x : ℝ)
    (cs : List ℝ) (c : ℝ) (hne : cs ≠ []) :
    p54Horner fp x (cs ++ [c]) =
      fp.fl_add (fp.fl_mul x (p54Horner fp x cs)) c := by
  cases cs with
  | nil => contradiction
  | cons a rest =>
      simp [p54Horner, List.foldl_append]

private lemma p54_abs_poly (x : ℝ) (cs : List ℝ) :
    |p54PolyDesc x cs| ≤ p54AbsDesc x cs := by
  induction cs with
  | nil => simp [p54PolyDesc, p54AbsDesc]
  | cons c cs ih =>
      simpa [p54PolyDesc, p54AbsDesc, abs_mul, abs_pow] using
        (abs_add_le (c * x ^ cs.length) (p54PolyDesc x cs)).trans
          (add_le_add le_rfl ih)

private lemma p54_abs_nonneg (x : ℝ) (cs : List ℝ) :
    0 ≤ p54AbsDesc x cs := by
  induction cs with
  | nil => simp [p54AbsDesc]
  | cons c cs ih =>
      simp only [p54AbsDesc]
      exact add_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) ih

private lemma p54_two_round (u r d e : ℝ) (hu : 0 ≤ u)
    (hd : |d| ≤ u) (he : |e| ≤ u) :
    |r * (1 + d) * (1 + e) - r| ≤ ((1 + u) ^ 2 - 1) * |r| := by
  have hde : |d * e| ≤ u * u := by
    rw [abs_mul]
    exact mul_le_mul hd he (abs_nonneg _) hu
  have hsum : |d + e + d * e| ≤ 2 * u + u * u := by
    calc
      |d + e + d * e| ≤ |d + e| + |d * e| := abs_add_le _ _
      _ ≤ |d| + |e| + |d * e| := by gcongr; exact abs_add_le _ _
      _ ≤ 2 * u + u * u := by linarith
  calc
    |r * (1 + d) * (1 + e) - r| = |r| * |d + e + d * e| := by
      have h : r * (1 + d) * (1 + e) - r = r * (d + e + d * e) := by ring
      rw [h, abs_mul]
    _ ≤ |r| * (2 * u + u * u) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = ((1 + u) ^ 2 - 1) * |r| := by ring

private lemma p54_forward_step (fp : P54FPModel) (x y z a b : ℝ) :
    let t := (1 + fp.u) ^ 2 - 1
    |fp.fl_add (fp.fl_mul x z) (fp.fl_add a b) - (x * y + (a + b))| ≤
      |x| * |z - y| + t * (|x| * |z| + |a + b|) := by
  dsimp
  obtain ⟨dm, hdm, hm⟩ := fp.model_mul x z
  obtain ⟨dc, hdc, hc⟩ := fp.model_add a b
  obtain ⟨da, hda, ha⟩ := fp.model_add (fp.fl_mul x z) (fp.fl_add a b)
  have hmul := p54_two_round fp.u (x * z) dm da fp.u_nonneg hdm hda
  have hcoef := p54_two_round fp.u (a + b) dc da fp.u_nonneg hdc hda
  have heq :
      fp.fl_add (fp.fl_mul x z) (fp.fl_add a b) - (x * y + (a + b)) =
      x * (z - y) +
        ((x * z) * (1 + dm) * (1 + da) - x * z) +
        ((a + b) * (1 + dc) * (1 + da) - (a + b)) := by
    rw [ha, hm, hc]
    ring
  rw [heq]
  calc
    _ ≤ |x * (z - y)| +
        |(x * z) * (1 + dm) * (1 + da) - x * z| +
        |(a + b) * (1 + dc) * (1 + da) - (a + b)| := by
          linarith [abs_add_le (x * (z - y))
            ((x * z) * (1 + dm) * (1 + da) - x * z),
            abs_add_le (x * (z - y) +
              ((x * z) * (1 + dm) * (1 + da) - x * z))
              ((a + b) * (1 + dc) * (1 + da) - (a + b))]
    _ ≤ |x| * |z - y| + ((1 + fp.u) ^ 2 - 1) *
          (|x| * |z| + |a + b|) := by
            rw [abs_mul] at hmul
            rw [abs_mul x (z - y)]
            convert add_le_add (add_le_add le_rfl hmul) hcoef using 1; ring

private lemma p54_add_nonneg (fp : P54FPModel) (hu : fp.u < 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ fp.fl_add a b := by
  obtain ⟨d, hd, heq⟩ := fp.model_add a b
  rw [heq]
  exact mul_nonneg (add_nonneg ha hb) (by linarith [neg_abs_le d])

private lemma p54_mul_nonneg (fp : P54FPModel) (hu : fp.u < 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ fp.fl_mul a b := by
  obtain ⟨d, hd, heq⟩ := fp.model_mul a b
  rw [heq]
  exact mul_nonneg (mul_nonneg ha hb) (by linarith [neg_abs_le d])

private lemma p54_inverse_step (fp : P54FPModel) (hu : fp.u < 1)
    {x y d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hd : 0 ≤ d) :
    x * y + d ≤ (1 + fp.u) ^ 2 * fp.fl_add (fp.fl_mul x y) d := by
  let m := fp.fl_mul x y
  let r := fp.fl_add m d
  have hm : 0 ≤ m := p54_mul_nonneg fp hu hx hy
  have hr : 0 ≤ r := p54_add_nonneg fp hu hm hd
  obtain ⟨em, hem, hmeq⟩ := fp.inverse_mul x y
  obtain ⟨ea, hea, hraeq⟩ := fp.inverse_add m d
  have hmul : x * y ≤ (1 + fp.u) * m := by
    calc
      x * y = m * (1 + em) := hmeq
      _ ≤ m * (1 + fp.u) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self em]) hm
      _ = (1 + fp.u) * m := by ring
  have hadd : m + d ≤ (1 + fp.u) * r := by
    calc
      m + d = r * (1 + ea) := hraeq
      _ ≤ r * (1 + fp.u) := mul_le_mul_of_nonneg_left (by linarith [le_abs_self ea]) hr
      _ = (1 + fp.u) * r := by ring
  have hmid : x * y + d ≤ (1 + fp.u) * (m + d) := by
    nlinarith [mul_nonneg fp.u_nonneg hd]
  have hscale := mul_le_mul_of_nonneg_left hadd (by linarith [fp.u_nonneg] : 0 ≤ 1 + fp.u)
  dsimp [m, r] at *
  nlinarith [hscale]

private lemma p54_coeff_forward (fp : P54FPModel) (a b : ℝ) :
    |fp.fl_add a b - (a + b)| ≤ fp.u * |a + b| := by
  obtain ⟨d, hd, heq⟩ := fp.model_add a b
  rw [heq]
  have h : (a + b) * (1 + d) - (a + b) = (a + b) * d := by ring
  rw [h, abs_mul]
  calc
    |a + b| * |d| ≤ |a + b| * fp.u :=
      mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = fp.u * |a + b| := by ring

private lemma p54_coeff_inverse (fp : P54FPModel) (a b : ℝ) :
    |a + b| ≤ (1 + fp.u) * |fp.fl_add a b| := by
  obtain ⟨e, he, heq⟩ := fp.inverse_add a b
  rw [heq, abs_mul]
  calc
    |fp.fl_add a b| * |1 + e| ≤ |fp.fl_add a b| * (1 + fp.u) :=
      mul_le_mul_of_nonneg_left (by
        calc |1 + e| ≤ 1 + |e| := by simpa using abs_add_le (1 : ℝ) e
             _ ≤ 1 + fp.u := by linarith) (abs_nonneg _)
    _ = (1 + fp.u) * |fp.fl_add a b| := by ring

private noncomputable def p54_exactPairs (ps : List (ℝ × ℝ)) : List ℝ :=
  ps.map (fun p => p.1 + p.2)

private noncomputable def p54_roundPairs (fp : P54FPModel)
    (ps : List (ℝ × ℝ)) : List ℝ :=
  ps.map (fun p => fp.fl_add p.1 p.2)

private lemma p54_pair_bounds (fp : P54FPModel) (hu : fp.u < 1)
    (x : ℝ) (ps : List (ℝ × ℝ)) (hne : ps ≠ []) :
    let k := 2 * ps.length - 1
    let C := (1 + fp.u) ^ k
    |p54PolyDesc x (p54_exactPairs ps) -
      p54Horner fp x (p54_roundPairs fp ps)| ≤
        (C - 1) * p54AbsDesc x (p54_exactPairs ps) ∧
    p54AbsDesc x (p54_exactPairs ps) ≤
      C * p54Horner fp |x| ((p54_roundPairs fp ps).map abs) ∧
    0 ≤ p54Horner fp |x| ((p54_roundPairs fp ps).map abs) := by
  induction ps using List.reverseRecOn with
  | nil => contradiction
  | @append_singleton ps p ih =>
      by_cases hp : ps = []
      · subst ps
        rcases p with ⟨a, b⟩
        simp [p54_exactPairs, p54_roundPairs, p54PolyDesc,
          p54AbsDesc, p54Horner]
        constructor
        · simpa [abs_sub_comm, mul_comm] using p54_coeff_forward fp a b
        · exact p54_coeff_inverse fp a b
      · obtain ⟨herr, habs, hz⟩ := ih hp
        let cs := p54_exactPairs ps
        let ds := p54_roundPairs fp ps
        let c := p.1 + p.2
        let d := fp.fl_add p.1 p.2
        let P := p54PolyDesc x cs
        let A := p54AbsDesc x cs
        let H := p54Horner fp x ds
        let Z := p54Horner fp |x| (ds.map abs)
        let k := 2 * ps.length - 1
        let C := (1 + fp.u) ^ k
        let T := (1 + fp.u) ^ 2 - 1
        have hcs : cs ≠ [] := by
          simp [cs, p54_exactPairs, hp]
        have hds : ds ≠ [] := by
          simp [ds, p54_roundPairs, hp]
        have hdsabs : ds.map abs ≠ [] := by simp [hds]
        have hk : 2 * (ps ++ [p]).length - 1 = k + 2 := by
          dsimp [k]
          simp only [List.length_append, List.length_singleton]
          have hlen : 0 < ps.length := List.length_pos_iff_ne_nil.mpr hp
          omega
        have hC : 1 ≤ C := one_le_pow₀ (by linarith [fp.u_nonneg])
        have hCbase : 1 + fp.u ≤ C :=
          le_self_pow₀ (by linarith [fp.u_nonneg]) (by
            dsimp [k]
            have hlen : 0 < ps.length := List.length_pos_iff_ne_nil.mpr hp
            omega)
        have hT : 0 ≤ T := by
          dsimp [T]
          have hsq : (1 : ℝ) ≤ (1 + fp.u) ^ 2 :=
            one_le_pow₀ (by linarith [fp.u_nonneg])
          linarith
        have hP : |P| ≤ A := p54_abs_poly x cs
        have hH : |H| ≤ C * A := by
          have ht := abs_add_le (H - P) P
          have he : |H - P| ≤ (C - 1) * A := by simpa [abs_sub_comm] using herr
          have heq : H - P + P = H := by ring
          rw [heq] at ht
          nlinarith
        have hloc := p54_forward_step fp x P H p.1 p.2
        have hcoeff := p54_coeff_inverse fp p.1 p.2
        have hinv := p54_inverse_step fp hu (abs_nonneg x) hz (abs_nonneg d)
        have hZnew : 0 ≤ fp.fl_add (fp.fl_mul |x| Z) |d| :=
          p54_add_nonneg fp hu
            (p54_mul_nonneg fp hu (abs_nonneg x) hz) (abs_nonneg d)
        have hTle : T ≤ C * (1 + T) - 1 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC) (by linarith : 0 ≤ 1 + T)]
        have hforward :
            |(x * P + c) - fp.fl_add (fp.fl_mul x H) d| ≤
              (C * (1 + fp.u) ^ 2 - 1) * (|x| * A + |c|) := by
          have h1 : |fp.fl_add (fp.fl_mul x H) d - (x * P + c)| ≤
              |x| * |H - P| + T * (|x| * |H| + |c|) := by
            simpa [d, c, T] using hloc
          have h2 : |H - P| ≤ (C - 1) * A := by simpa [abs_sub_comm] using herr
          have h3 : |x| * |H - P| + T * (|x| * |H| + |c|) ≤
              |x| * ((C - 1) * A) + T * (|x| * (C * A) + |c|) := by
            gcongr
          have h4 : |x| * ((C - 1) * A) + T * (|x| * (C * A) + |c|) ≤
              (C * (1 + fp.u) ^ 2 - 1) * (|x| * A + |c|) := by
            have hc : T * |c| ≤ (C * (1 + fp.u) ^ 2 - 1) * |c| := by
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg c)
              convert hTle using 1; ring
            nlinarith [hc]
          simpa [abs_sub_comm] using h1.trans (h3.trans h4)
        have hinverse :
            |x| * A + |c| ≤
              (C * (1 + fp.u) ^ 2) * fp.fl_add (fp.fl_mul |x| Z) |d| := by
          have h1 : |x| * A + |c| ≤
              |x| * (C * Z) + (1 + fp.u) * |d| := by
            exact add_le_add (mul_le_mul_of_nonneg_left habs (abs_nonneg x)) hcoeff
          have h2 : |x| * (C * Z) + (1 + fp.u) * |d| ≤
              C * (|x| * Z + |d|) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hCbase) (abs_nonneg d)]
          have h3 : C * (|x| * Z + |d|) ≤
              C * ((1 + fp.u) ^ 2 * fp.fl_add (fp.fl_mul |x| Z) |d|) :=
            mul_le_mul_of_nonneg_left hinv (le_trans zero_le_one hC)
          calc
            _ ≤ C * (|x| * Z + |d|) := h1.trans h2
            _ ≤ C * ((1 + fp.u) ^ 2 * fp.fl_add (fp.fl_mul |x| Z) |d|) := h3
            _ = (C * (1 + fp.u) ^ 2) * fp.fl_add (fp.fl_mul |x| Z) |d| := by ring
        have he : p54_exactPairs (ps ++ [p]) = cs ++ [c] := by
          simp [p54_exactPairs, cs, c]
        have hr : p54_roundPairs fp (ps ++ [p]) = ds ++ [d] := by
          simp [p54_roundPairs, ds, d]
        dsimp only
        rw [he, hr, hk, pow_add,
          p54_poly_append, p54_abs_append,
          p54_horner_append fp x ds d hds,
          List.map_append, List.map_singleton,
          p54_horner_append fp |x| (ds.map abs) |d| hdsabs]
        exact ⟨by simpa [P, H, A, c, d, C] using hforward,
          by simpa [A, Z, c, d, C] using hinverse,
          by simpa [Z, d] using hZnew⟩

private lemma p54_power_gamma (fp : P54FPModel) (k : ℕ) (hk : 0 < k)
    (hvalid : P54GammaValid fp.u k) :
    (1 + fp.u) ^ k - 1 ≤ p54Gamma fp.u k := by
  let gfp := NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg
  have hgvalid : NumStability.gammaValid gfp k := hvalid
  have h1valid : NumStability.gammaValid gfp 1 :=
    NumStability.gammaValid_mono gfp hk hgvalid
  have hu : fp.u ≤ NumStability.gamma gfp 1 :=
    NumStability.u_le_gamma gfp (by omega) h1valid
  have hpow := NumStability.one_add_pow_sub_one_le_gamma_mul_of_le_gamma
    gfp k 1 fp.u_nonneg hu (by simpa using hgvalid)
  simpa [gfp, NumStability.gamma, p54Gamma] using hpow

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
  let ps := List.zip a b
  have hlen : ps.length = n + 1 := by
    simp [ps, List.length_zip, ha, hb]
  have hne : ps ≠ [] := by
    intro h
    simp [h] at hlen
  have hu : fp.u < 1 := by
    have h := hvalid
    unfold P54GammaValid at h
    have hn : (1 : ℝ) ≤ (2 * n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
    have hmul : fp.u ≤ (2 * n + 1 : ℕ) * fp.u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) fp.u_nonneg]
    linarith
  have hexact : p54_exactPairs ps = p54SumCoeffs a b := by
    simp only [ps, p54_exactPairs, p54SumCoeffs, List.map_zip_eq_zipWith]
    rfl
  have hround : p54_roundPairs fp ps = p54RoundedSumCoeffs fp a b := by
    simp only [ps, p54_roundPairs, p54RoundedSumCoeffs, List.map_zip_eq_zipWith]
    rfl
  obtain ⟨herr, habs, _hz⟩ := p54_pair_bounds fp hu x ps hne
  have hk : 2 * ps.length - 1 = 2 * n + 1 := by omega
  have hpow : (1 + fp.u) ^ (2 * n + 1) - 1 ≤ p54Gamma fp.u (2 * n + 1) :=
    p54_power_gamma fp (2 * n + 1) (by omega) hvalid
  have hA : 0 ≤ p54AbsDesc x (p54SumCoeffs a b) :=
    p54_abs_nonneg x _
  constructor
  · have h1 :
        |p54PolyDesc x (p54SumCoeffs a b) -
          p54Horner fp x (p54RoundedSumCoeffs fp a b)| ≤
          ((1 + fp.u) ^ (2 * n + 1) - 1) *
            p54AbsDesc x (p54SumCoeffs a b) := by
      simpa [hexact, hround, hk] using herr
    exact h1.trans (mul_le_mul_of_nonneg_right hpow hA)
  · simpa [hexact, hround, hk] using habs

end VSCLReuse

import VSCLReuse.P54.Definitions
import NumStability.Analysis.Rounding

namespace VSCLReuse

private def p54CoeffRel (fp : P54FPModel) (c r : ℝ) : Prop :=
  |c - r| ≤ fp.u * |c| ∧
  |r| ≤ (1 + fp.u) * |c| ∧
  |c| ≤ (1 + fp.u) * |r|

private lemma p54_coeff_rel (fp : P54FPModel) (a b : ℝ) :
    p54CoeffRel fp (a + b) (fp.fl_add a b) := by
  obtain ⟨δ, hδ, hforward⟩ := fp.model_add a b
  obtain ⟨ε, hε, hinverse⟩ := fp.inverse_add a b
  have hδu : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have hεu : |1 + ε| ≤ 1 + fp.u := by
    calc
      |1 + ε| ≤ |(1 : ℝ)| + |ε| := abs_add_le 1 ε
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hε 1
  constructor
  · rw [hforward]
    have heq : a + b - (a + b) * (1 + δ) = -(a + b) * δ := by ring
    rw [heq, abs_mul, abs_neg]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg (a + b))
  constructor
  · rw [hforward, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδu (abs_nonneg (a + b))
  · rw [hinverse, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hεu (abs_nonneg (fp.fl_add a b))

private lemma p54_coeff_lists (fp : P54FPModel) :
    ∀ a b : List ℝ, a.length = b.length →
      List.Forall₂ (p54CoeffRel fp)
        (p54SumCoeffs a b) (p54RoundedSumCoeffs fp a b) := by
  intro a
  induction a with
  | nil =>
      intro b hb
      cases b with
      | nil => simp [p54SumCoeffs, p54RoundedSumCoeffs]
      | cons _ _ => simp at hb
  | cons a as ih =>
      intro b hb
      cases b with
      | nil => simp at hb
      | cons b bs =>
          have hlen : as.length = bs.length := by simp at hb; omega
          simpa [p54SumCoeffs, p54RoundedSumCoeffs] using
            List.Forall₂.cons (p54_coeff_rel fp a b) (ih bs hlen)

private lemma p54_fold_poly (x : ℝ) :
    ∀ (cs : List ℝ) (y : ℝ),
      cs.foldl (fun z c => x * z + c) y =
        y * x ^ cs.length + p54PolyDesc x cs := by
  intro cs
  induction cs with
  | nil => intro y; simp [p54PolyDesc]
  | cons c cs ih =>
      intro y
      simp [List.foldl, p54PolyDesc, ih, pow_succ]
      ring

private lemma p54_fold_abs (x : ℝ) :
    ∀ (cs : List ℝ) (y : ℝ),
      cs.foldl (fun z c => |x| * z + |c|) y =
        y * |x| ^ cs.length + p54AbsDesc x cs := by
  intro cs
  induction cs with
  | nil => intro y; simp [p54AbsDesc]
  | cons c cs ih =>
      intro y
      simp [List.foldl, p54AbsDesc, ih, pow_succ]
      ring

private lemma p54_forward_bounds (u t r : ℝ)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ r = t * (1 + δ)) :
    |t - r| ≤ u * |t| ∧ |r| ≤ (1 + u) * |t| := by
  obtain ⟨δ, hδ, hr⟩ := h
  have hfac : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + u := by simpa using add_le_add_left hδ 1
  constructor
  · rw [hr]
    have heq : t - t * (1 + δ) = -(t * δ) := by ring
    rw [heq, abs_neg, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ (abs_nonneg t)
  · rw [hr, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac (abs_nonneg t)

private lemma p54_round_nonneg (u t r : ℝ)
    (hu : u < 1) (ht : 0 ≤ t)
    (h : ∃ δ : ℝ, |δ| ≤ u ∧ r = t * (1 + δ)) : 0 ≤ r := by
  obtain ⟨δ, hδ, hr⟩ := h
  have hd : -u ≤ δ := by linarith [neg_abs_le δ]
  rw [hr]
  exact mul_nonneg ht (by linarith)

private lemma p54_inverse_bound (u t r : ℝ) (hr : 0 ≤ r)
    (h : ∃ ε : ℝ, |ε| ≤ u ∧ t = r * (1 + ε)) :
    t ≤ (1 + u) * r := by
  obtain ⟨ε, hε, ht⟩ := h
  have hfac : 1 + ε ≤ 1 + u := by linarith [le_abs_self ε]
  rw [ht]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hfac hr

private lemma p54_step_bounds (fp : P54FPModel) (hu : fp.u < 1)
    (x : ℝ) (k : ℕ) (c r y z M H : ℝ)
    (hcr : p54CoeffRel fp c r)
    (he : |y - z| ≤ ((1 + fp.u) ^ k - 1) * M)
    (hy : |y| ≤ M)
    (hM : M ≤ (1 + fp.u) ^ k * H)
    (hH : 0 ≤ H) :
    let z' := fp.fl_add (fp.fl_mul x z) r
    let H' := fp.fl_add (fp.fl_mul |x| H) |r|
    let M' := |x| * M + |c|
    |(x * y + c) - z'| ≤ ((1 + fp.u) ^ (k + 2) - 1) * M' ∧
    |x * y + c| ≤ M' ∧
    M' ≤ (1 + fp.u) ^ (k + 2) * H' ∧
    0 ≤ H' := by
  dsimp
  let C : ℝ := 1 + fp.u
  let K : ℝ := C ^ k
  let v : ℝ := fp.fl_mul x z
  let w : ℝ := fp.fl_mul |x| H
  let z' : ℝ := fp.fl_add v r
  let H' : ℝ := fp.fl_add w |r|
  have hC : 1 ≤ C := by dsimp [C]; linarith [fp.u_nonneg]
  have hK : 1 ≤ K := one_le_pow₀ hC
  have hK0 : 0 ≤ K := by linarith
  have hmul := p54_forward_bounds fp.u (x * z) v (fp.model_mul x z)
  have hadd := p54_forward_bounds fp.u (v + r) z' (fp.model_add v r)
  have hz : |z| ≤ K * M := by
    have htri : |z| ≤ |y| + |y - z| := by
      calc
        |z| = |y + -(y - z)| := by congr 1; ring
        _ ≤ |y| + |-(y - z)| := abs_add_le _ _
        _ = |y| + |y - z| := by rw [abs_neg]
    calc
      |z| ≤ |y| + |y - z| := htri
      _ ≤ M + (K - 1) * M := by
        apply add_le_add hy
        simpa [K, C] using he
      _ = K * M := by ring
  have hM0 : 0 ≤ M := le_trans (abs_nonneg y) hy
  have hmulErr : |x * z - v| ≤ fp.u * (|x| * |z|) := by
    simpa [abs_mul] using hmul.1
  have hv : |v| ≤ C * (|x| * |z|) := by
    simpa [C, abs_mul] using hmul.2
  have hvl : |v| ≤ C * (|x| * (K * M)) := by
    apply le_trans hv
    gcongr
  have haddErr : |v + r - z'| ≤ fp.u * (|v| + |r|) :=
    le_trans hadd.1 (mul_le_mul_of_nonneg_left (abs_add_le v r) fp.u_nonneg)
  have hcoeffErr := hcr.1
  have hr : |r| ≤ C * |c| := by simpa [C] using hcr.2.1
  have hsplit :
      |(x * y + c) - z'| ≤
        |x| * |y - z| + |x * z - v| + |c - r| + |v + r - z'| := by
    have heq : (x * y + c) - z' =
        x * (y - z) + (x * z - v) + (c - r) + (v + r - z') := by ring
    rw [heq]
    calc
      |_ + _ + _ + _| ≤ |x * (y - z) + (x * z - v) + (c - r)| +
          |v + r - z'| := abs_add_le _ _
      _ ≤ (|x * (y - z) + (x * z - v)| + |c - r|) +
          |v + r - z'| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|x * (y - z)| + |x * z - v|) + |c - r|) +
          |v + r - z'| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have hErr :
      |(x * y + c) - z'| ≤
        ((1 + fp.u) ^ (k + 2) - 1) * (|x| * M + |c|) := by
    have hmid :
        |(x * y + c) - z'| ≤
          |x| * ((K - 1) * M) + fp.u * (|x| * (K * M)) +
          fp.u * |c| +
          fp.u * (C * (|x| * (K * M)) + C * |c|) := by
      calc
        |(x * y + c) - z'| ≤
            |x| * |y - z| + |x * z - v| + |c - r| + |v + r - z'| := hsplit
        _ ≤ |x| * ((K - 1) * M) + fp.u * (|x| * |z|) +
              fp.u * |c| + fp.u * (|v| + |r|) := by
          gcongr
        _ ≤ _ := by
          gcongr
          all_goals exact fp.u_nonneg
    have hcomp : C ^ 2 - 1 ≤ K * C ^ 2 - 1 := by
      have hp : 0 ≤ (K - 1) * C ^ 2 := mul_nonneg (by linarith) (sq_nonneg C)
      nlinarith
    calc
      |(x * y + c) - z'| ≤
          |x| * ((K - 1) * M) + fp.u * (|x| * (K * M)) +
          fp.u * |c| +
          fp.u * (C * (|x| * (K * M)) + C * |c|) := hmid
      _ = (K * C ^ 2 - 1) * (|x| * M) + (C ^ 2 - 1) * |c| := by
        dsimp [C]; ring
      _ ≤ (K * C ^ 2 - 1) * (|x| * M + |c|) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hcomp) (abs_nonneg c)]
      _ = ((1 + fp.u) ^ (k + 2) - 1) * (|x| * M + |c|) := by
        rw [pow_add, pow_two]
  have hY : |x * y + c| ≤ |x| * M + |c| := by
    calc
      |x * y + c| ≤ |x * y| + |c| := abs_add_le _ _
      _ ≤ |x| * M + |c| := by rw [abs_mul]; gcongr
  have hw0 : 0 ≤ w :=
    p54_round_nonneg fp.u (|x| * H) w hu
      (mul_nonneg (abs_nonneg x) hH) (fp.model_mul |x| H)
  have hH'0 : 0 ≤ H' :=
    p54_round_nonneg fp.u (w + |r|) H' hu
      (add_nonneg hw0 (abs_nonneg r)) (fp.model_add w |r|)
  have hwinv : |x| * H ≤ C * w := by
    simpa [C] using
      p54_inverse_bound fp.u (|x| * H) w hw0 (fp.inverse_mul |x| H)
  have hHinv : w + |r| ≤ C * H' := by
    simpa [C] using
      p54_inverse_bound fp.u (w + |r|) H' hH'0 (fp.inverse_add w |r|)
  have hMaj : |x| * M + |c| ≤ (1 + fp.u) ^ (k + 2) * H' := by
    have hcInv : |c| ≤ C * |r| := by simpa [C] using hcr.2.2
    have hpow_nonneg : 0 ≤ C ^ (k + 1) := pow_nonneg (by linarith) _
    calc
      |x| * M + |c| ≤ |x| * (K * H) + C * |r| := by gcongr
      _ ≤ K * (C * w) + C * |r| := by
        have hh := mul_le_mul_of_nonneg_left hwinv hK0
        nlinarith [hh]
      _ ≤ (K * C) * (w + |r|) := by
        have h : C ≤ K * C := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (by linarith : 0 ≤ C)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h) (abs_nonneg r)]
      _ ≤ (K * C) * (C * H') :=
        mul_le_mul_of_nonneg_left hHinv (mul_nonneg hK0 (by linarith))
      _ = (1 + fp.u) ^ (k + 2) * H' := by
        rw [pow_add, pow_two]
        dsimp [K, C]
        ring
  exact ⟨hErr, hY, hMaj, hH'0⟩

private lemma p54_fold_bounds (fp : P54FPModel) (hu : fp.u < 1)
    (x : ℝ) (k : ℕ) (cs rs : List ℝ)
    (hrel : List.Forall₂ (p54CoeffRel fp) cs rs)
    (y z M H : ℝ)
    (he : |y - z| ≤ ((1 + fp.u) ^ k - 1) * M)
    (hy : |y| ≤ M)
    (hM : M ≤ (1 + fp.u) ^ k * H)
    (hH : 0 ≤ H) :
    let Y := cs.foldl (fun y c => x * y + c) y
    let Z := rs.foldl (fun z r => fp.fl_add (fp.fl_mul x z) r) z
    let MM := cs.foldl (fun M c => |x| * M + |c|) M
    let HH := rs.foldl (fun H r => fp.fl_add (fp.fl_mul |x| H) |r|) H
    |Y - Z| ≤ ((1 + fp.u) ^ (k + 2 * cs.length) - 1) * MM ∧
    |Y| ≤ MM ∧
    MM ≤ (1 + fp.u) ^ (k + 2 * cs.length) * HH ∧
    0 ≤ HH := by
  induction hrel generalizing k y z M H with
  | nil =>
      simpa using And.intro he (And.intro hy (And.intro hM hH))
  | @cons c r cs rs hcr hrel ih =>
      have hs := p54_step_bounds fp hu x k c r y z M H hcr he hy hM hH
      have ht := ih (k + 2) (x * y + c)
        (fp.fl_add (fp.fl_mul x z) r) (|x| * M + |c|)
        (fp.fl_add (fp.fl_mul |x| H) |r|)
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
      have hk : k + 2 * (cs.length + 1) = (k + 2) + 2 * cs.length := by omega
      simpa [List.foldl, hk] using ht

private lemma p54_pow_sub_one_le_gamma (fp : P54FPModel) (k : ℕ)
    (hk : 0 < k) (hvalid : P54GammaValid fp.u k) :
    (1 + fp.u) ^ k - 1 ≤ p54Gamma fp.u k := by
  let m : NumStability.FPModel :=
    NumStability.FPModel.exactWithUnitRoundoff fp.u fp.u_nonneg
  have hm : NumStability.gammaValid m k := by
    simpa [m, NumStability.gammaValid, P54GammaValid,
      NumStability.FPModel.exactWithUnitRoundoff] using hvalid
  have hm1 : NumStability.gammaValid m 1 :=
    NumStability.gammaValid_mono m hk hm
  have hu : fp.u ≤ NumStability.gamma m 1 := by
    simpa [m, NumStability.FPModel.exactWithUnitRoundoff] using
      NumStability.u_le_gamma m (by omega : 0 < 1) hm1
  have hpow := NumStability.one_add_pow_sub_one_le_gamma_mul_of_le_gamma
    m k 1 fp.u_nonneg hu (by simpa using hm)
  simpa [m, NumStability.FPModel.exactWithUnitRoundoff,
    NumStability.gamma, p54Gamma] using hpow

private lemma p54_fold_map_abs (fp : P54FPModel) (x : ℝ) :
    ∀ (rs : List ℝ) (H : ℝ),
      (rs.map abs).foldl (fun y b => fp.fl_add (fp.fl_mul |x| y) b) H =
        rs.foldl (fun y r => fp.fl_add (fp.fl_mul |x| y) |r|) H := by
  intro rs
  induction rs with
  | nil => intro H; rfl
  | cons r rs ih =>
      intro H
      simpa [List.foldl] using ih (fp.fl_add (fp.fl_mul |x| H) |r|)

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
  have hu : fp.u < 1 := by
    have hindex : (1 : ℝ) ≤ (2 * n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
    have hprod := mul_nonneg (sub_nonneg.mpr hindex) fp.u_nonneg
    unfold P54GammaValid at hvalid
    nlinarith
  cases a with
  | nil => simp at ha
  | cons aa as =>
      cases b with
      | nil => simp at hb
      | cons bb bs =>
          have has : as.length = n := by simp at ha; omega
          have hbs : bs.length = n := by simp at hb; omega
          have hrel := p54_coeff_lists fp as bs (by omega)
          have hcr := p54_coeff_rel fp aa bb
          have hlen : (p54SumCoeffs as bs).length = n := by
            simp [p54SumCoeffs, List.length_zipWith, has, hbs]
          have he0 : |(aa + bb) - fp.fl_add aa bb| ≤
              ((1 + fp.u) ^ 1 - 1) * |aa + bb| := by
            simpa using hcr.1
          have hM0 : |aa + bb| ≤ (1 + fp.u) ^ 1 * |fp.fl_add aa bb| := by
            simpa using hcr.2.2
          have hfold := p54_fold_bounds fp hu x 1
            (p54SumCoeffs as bs) (p54RoundedSumCoeffs fp as bs) hrel
            (aa + bb) (fp.fl_add aa bb) |aa + bb| |fp.fl_add aa bb|
            he0 le_rfl hM0 (abs_nonneg _)
          dsimp at hfold
          rw [hlen] at hfold
          have hindex : 1 + 2 * n = 2 * n + 1 := by omega
          rw [hindex] at hfold
          have hpoly :
              p54PolyDesc x (p54SumCoeffs (aa :: as) (bb :: bs)) =
                (p54SumCoeffs as bs).foldl
                  (fun y c => x * y + c) (aa + bb) := by
            simpa [p54SumCoeffs, p54PolyDesc] using
              (p54_fold_poly x (p54SumCoeffs as bs) (aa + bb)).symm
          have habs :
              p54AbsDesc x (p54SumCoeffs (aa :: as) (bb :: bs)) =
                (p54SumCoeffs as bs).foldl
                  (fun M c => |x| * M + |c|) |aa + bb| := by
            simpa [p54SumCoeffs, p54AbsDesc] using
              (p54_fold_abs x (p54SumCoeffs as bs) |aa + bb|).symm
          have hhorner :
              p54Horner fp x (p54RoundedSumCoeffs fp (aa :: as) (bb :: bs)) =
                (p54RoundedSumCoeffs fp as bs).foldl
                  (fun z r => fp.fl_add (fp.fl_mul x z) r) (fp.fl_add aa bb) := rfl
          have hhornerAbs :
              p54Horner fp |x|
                  ((p54RoundedSumCoeffs fp (aa :: as) (bb :: bs)).map abs) =
                (p54RoundedSumCoeffs fp as bs).foldl
                  (fun H r => fp.fl_add (fp.fl_mul |x| H) |r|)
                  |fp.fl_add aa bb| := by
            change ((p54RoundedSumCoeffs fp as bs).map abs).foldl
                (fun y b => fp.fl_add (fp.fl_mul |x| y) b) |fp.fl_add aa bb| = _
            exact p54_fold_map_abs fp x _ _
          have hgamma := p54_pow_sub_one_le_gamma fp (2 * n + 1)
            (by omega) hvalid
          constructor
          · rw [hpoly, hhorner, habs]
            have hnonneg : 0 ≤ (p54SumCoeffs as bs).foldl
                (fun M c => |x| * M + |c|) |aa + bb| :=
              le_trans (abs_nonneg _) hfold.2.1
            exact le_trans hfold.1
              (mul_le_mul_of_nonneg_right hgamma hnonneg)
          · rw [habs, hhornerAbs]
            exact hfold.2.2.1

end VSCLReuse

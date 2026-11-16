import VSCLReuse.P54.Definitions
import NumStability.Source.Higham.Chapter05.Section01.Horner.Basic

namespace VSCLReuse

private noncomputable def p54AsFPModel (fp : P54FPModel) : NumStability.FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fp.fl_add
  fl_sub := (· - ·)
  fl_mul := fp.fl_mul
  fl_div := (· / ·)
  fl_sqrt := Real.sqrt
  fl_add_zero := fp.fl_add_zero
  model_add := fp.model_add
  model_sub := by
    intro x y
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_mul := fp.model_mul
  model_div := by
    intro x y _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring
  model_sqrt := by
    intro x _
    refine ⟨0, ?_, ?_⟩
    · simpa using fp.u_nonneg
    · ring

private theorem p54Horner_eq (fp : P54FPModel) (x : ℝ) (cs : List ℝ) :
    p54Horner fp x cs = NumStability.fl_hornerDesc (p54AsFPModel fp) x cs := by
  cases cs with
  | nil => rfl
  | cons c cs => rfl

private theorem p54Poly_eq (x : ℝ) (cs : List ℝ) :
    p54PolyDesc x cs = NumStability.polyDesc x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [p54PolyDesc, NumStability.polyDesc, ih]

private theorem p54Abs_eq (x : ℝ) (cs : List ℝ) :
    p54AbsDesc x cs = NumStability.polyDescAbs x cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [p54AbsDesc, NumStability.polyDescAbs, ih]

private theorem p54_coeff_bounds (fp : P54FPModel) (a b : ℝ) :
    |(a + b) - fp.fl_add a b| ≤ fp.u * |a + b| ∧
    |fp.fl_add a b| ≤ (1 + fp.u) * |a + b| ∧
    |a + b| ≤ (1 + fp.u) * |fp.fl_add a b| := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  obtain ⟨ε, hε, hinv⟩ := fp.inverse_add a b
  have hδ' : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have hε' : |1 + ε| ≤ 1 + fp.u := by
    calc
      |1 + ε| ≤ |(1 : ℝ)| + |ε| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hε 1
  constructor
  · calc
      |(a + b) - fp.fl_add a b| = |(a + b) * δ| := by
        rw [hadd]
        have h : (a + b) - (a + b) * (1 + δ) = -((a + b) * δ) := by ring
        rw [h, abs_neg]
      _ = |a + b| * |δ| := abs_mul _ _
      _ ≤ fp.u * |a + b| := by nlinarith [mul_nonneg (abs_nonneg (a + b)) (sub_nonneg.mpr hδ)]
  constructor
  · rw [hadd, abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (a + b)) (sub_nonneg.mpr hδ')]
  · rw [hinv, abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (fp.fl_add a b)) (sub_nonneg.mpr hε')]

private theorem p54_list_forward_bounds (fp : P54FPModel) (x : ℝ) :
    ∀ (a b : List ℝ), a.length = b.length →
      |p54PolyDesc x (p54SumCoeffs a b) -
        p54PolyDesc x (p54RoundedSumCoeffs fp a b)| ≤
          fp.u * p54AbsDesc x (p54SumCoeffs a b) ∧
      p54AbsDesc x (p54RoundedSumCoeffs fp a b) ≤
        (1 + fp.u) * p54AbsDesc x (p54SumCoeffs a b) := by
  intro a
  induction a with
  | nil =>
      intro b hlen
      cases b with
      | nil => simp [p54SumCoeffs, p54RoundedSumCoeffs, p54PolyDesc, p54AbsDesc]
      | cons b bs => simp at hlen
  | cons a as ih =>
      intro b hlen
      cases b with
      | nil => simp at hlen
      | cons b bs =>
          have htail : as.length = bs.length := by simpa using hlen
          obtain ⟨hpoly, habs⟩ := ih bs htail
          obtain ⟨hc, hca, _⟩ := p54_coeff_bounds fp a b
          have hp : 0 ≤ |x| ^ as.length := pow_nonneg (abs_nonneg x) _
          have hpow : |x ^ as.length| = |x| ^ as.length := abs_pow x _
          have hlength : (p54SumCoeffs as bs).length = as.length := by
            simp [p54SumCoeffs, List.length_zipWith, htail]
          have hlength' : (p54RoundedSumCoeffs fp as bs).length = as.length := by
            simp [p54RoundedSumCoeffs, List.length_zipWith, htail]
          constructor
          · simp only [p54SumCoeffs, p54RoundedSumCoeffs, List.zipWith_cons_cons,
              p54PolyDesc, p54AbsDesc]
            simp only [List.length_zipWith, htail, min_self]
            rw [← htail]
            change |(a + b) * x ^ as.length + p54PolyDesc x (p54SumCoeffs as bs) -
              (fp.fl_add a b * x ^ as.length +
                p54PolyDesc x (p54RoundedSumCoeffs fp as bs))| ≤
              fp.u * (|a + b| * |x| ^ as.length +
                p54AbsDesc x (p54SumCoeffs as bs))
            have htri := abs_add_le ((a + b - fp.fl_add a b) * x ^ as.length)
              (p54PolyDesc x (p54SumCoeffs as bs) -
                p54PolyDesc x (p54RoundedSumCoeffs fp as bs))
            have hfirst : |(a + b - fp.fl_add a b) * x ^ as.length| ≤
                fp.u * |a + b| * |x| ^ as.length := by
              rw [abs_mul, hpow]
              exact mul_le_mul_of_nonneg_right hc hp
            have hrewrite :
                (a + b) * x ^ as.length + p54PolyDesc x (p54SumCoeffs as bs) -
                  (fp.fl_add a b * x ^ as.length +
                    p54PolyDesc x (p54RoundedSumCoeffs fp as bs)) =
                (a + b - fp.fl_add a b) * x ^ as.length +
                  (p54PolyDesc x (p54SumCoeffs as bs) -
                    p54PolyDesc x (p54RoundedSumCoeffs fp as bs)) := by ring
            rw [hrewrite]
            calc
              _ ≤ |(a + b - fp.fl_add a b) * x ^ as.length| +
                  |p54PolyDesc x (p54SumCoeffs as bs) -
                    p54PolyDesc x (p54RoundedSumCoeffs fp as bs)| := htri
              _ ≤ fp.u * |a + b| * |x| ^ as.length +
                  fp.u * p54AbsDesc x (p54SumCoeffs as bs) := add_le_add hfirst hpoly
              _ = fp.u * (|a + b| * |x| ^ as.length +
                    p54AbsDesc x (p54SumCoeffs as bs)) := by ring
          · simp only [p54SumCoeffs, p54RoundedSumCoeffs, List.zipWith_cons_cons,
              p54AbsDesc]
            simp only [List.length_zipWith, htail, min_self]
            rw [← htail]
            change |fp.fl_add a b| * |x| ^ as.length +
              p54AbsDesc x (p54RoundedSumCoeffs fp as bs) ≤
              (1 + fp.u) * (|a + b| * |x| ^ as.length +
                p54AbsDesc x (p54SumCoeffs as bs))
            calc
              |fp.fl_add a b| * |x| ^ as.length +
                  p54AbsDesc x (p54RoundedSumCoeffs fp as bs) ≤
                ((1 + fp.u) * |a + b|) * |x| ^ as.length +
                  (1 + fp.u) * p54AbsDesc x (p54SumCoeffs as bs) :=
                    add_le_add (mul_le_mul_of_nonneg_right hca hp) habs
              _ = (1 + fp.u) * (|a + b| * |x| ^ as.length +
                    p54AbsDesc x (p54SumCoeffs as bs)) := by ring

private theorem p54_gamma_step (u : ℝ) (hu : 0 ≤ u) (k : ℕ)
    (hvalid : P54GammaValid u (k + 1)) :
    u + p54Gamma u k * (1 + u) ≤ p54Gamma u (k + 1) := by
  let t : ℝ := (k : ℝ) * u
  have ht : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hu
  have hsum : t + u < 1 := by
    simpa [P54GammaValid, t, Nat.cast_add, add_mul] using hvalid
  have h1 : 0 < 1 - t := by linarith
  have h2 : 0 < 1 - (t + u) := by linarith
  have hid : u + t / (1 - t) * (1 + u) = (t + u) / (1 - t) := by
    field_simp
    ring
  have hle : (t + u) / (1 - t) ≤ (t + u) / (1 - (t + u)) := by
    apply (div_le_div_iff₀ h1 h2).2
    nlinarith [mul_nonneg ht hu]
  simpa [p54Gamma, t, Nat.cast_add, add_mul, hid] using hle

private theorem p54_inverse_step (fp : P54FPModel) (t y c : ℝ)
    (hu : fp.u < 1) (ht : 0 ≤ t) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    let m := fp.fl_mul t y
    let z := fp.fl_add m c
    0 ≤ m ∧ 0 ≤ z ∧
      t * y ≤ (1 + fp.u) * m ∧
      m + c ≤ (1 + fp.u) * z := by
  obtain ⟨δm, hδm, hm⟩ := fp.model_mul t y
  obtain ⟨εm, hεm, him⟩ := fp.inverse_mul t y
  have hdm : 0 ≤ 1 + δm := by
    have := (abs_le.mp hδm).1
    linarith
  have hm0 : 0 ≤ fp.fl_mul t y := by
    rw [hm]
    exact mul_nonneg (mul_nonneg ht hy) hdm
  obtain ⟨δa, hδa, ha⟩ := fp.model_add (fp.fl_mul t y) c
  obtain ⟨εa, hεa, hia⟩ := fp.inverse_add (fp.fl_mul t y) c
  have hda : 0 ≤ 1 + δa := by
    have := (abs_le.mp hδa).1
    linarith
  have hz0 : 0 ≤ fp.fl_add (fp.fl_mul t y) c := by
    rw [ha]
    exact mul_nonneg (add_nonneg hm0 hc) hda
  have hem : 1 + εm ≤ 1 + fp.u := by
    have := (abs_le.mp hεm).2
    linarith
  have hea : 1 + εa ≤ 1 + fp.u := by
    have := (abs_le.mp hεa).2
    linarith
  refine ⟨hm0, hz0, ?_, ?_⟩
  · rw [him]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hem hm0
  · rw [hia]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hea hz0

private theorem p54_inverse_coeffs (fp : P54FPModel) :
    ∀ (a b : List ℝ), a.length = b.length →
      List.Forall₂ (fun s r => |s| ≤ (1 + fp.u) * |r|)
        (p54SumCoeffs a b) (p54RoundedSumCoeffs fp a b) := by
  intro a
  induction a with
  | nil =>
      intro b h
      cases b with
      | nil => simp [p54SumCoeffs, p54RoundedSumCoeffs]
      | cons b bs => simp at h
  | cons a as ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons b bs =>
          have ht : as.length = bs.length := by simpa using h
          change List.Forall₂ (fun s r => |s| ≤ (1 + fp.u) * |r|)
            ((a + b) :: p54SumCoeffs as bs)
            ((fp.fl_add a b) :: p54RoundedSumCoeffs fp as bs)
          exact List.Forall₂.cons (p54_coeff_bounds fp a b).2.2 (ih bs ht)

private theorem p54_fold_inverse (fp : P54FPModel) (t : ℝ)
    (hu : fp.u < 1) (ht : 0 ≤ t) :
    ∀ {s r : List ℝ},
      List.Forall₂ (fun s r => |s| ≤ (1 + fp.u) * |r|) s r →
      ∀ (E R C : ℝ), 0 ≤ E → 0 ≤ R → 1 ≤ C → E ≤ C * R →
        s.foldl (fun y c => t * y + |c|) E ≤
          C * (1 + fp.u) ^ (2 * s.length) *
            r.foldl (fun y c => fp.fl_add (fp.fl_mul t y) |c|) R := by
  intro s r hrel
  induction hrel with
  | nil =>
      intro E R C _ _ _ hER
      simpa using hER
  | @cons s r ss rs hsr hrest ih =>
      intro E R C hE hR hC hER
      let m := fp.fl_mul t R
      let z := fp.fl_add m |r|
      obtain ⟨hm0, hz0, hmul, hadd⟩ :=
        p54_inverse_step fp t R |r| hu ht hR (abs_nonneg r)
      have hC0 : 0 ≤ C := by linarith
      have hf0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hEmul : t * E ≤ C * (t * R) := by
        have hh := mul_le_mul_of_nonneg_left hER ht
        nlinarith
      have hsC : |s| ≤ C * ((1 + fp.u) * |r|) := by
        calc
          |s| ≤ C * |s| := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hC) (abs_nonneg s)]
          _ ≤ C * ((1 + fp.u) * |r|) :=
            mul_le_mul_of_nonneg_left hsr hC0
      have hmid : t * R + (1 + fp.u) * |r| ≤
          (1 + fp.u) * (m + |r|) := by
        dsimp [m] at hmul ⊢
        nlinarith
      have hstep : t * E + |s| ≤ C * (1 + fp.u) ^ 2 * z := by
        calc
          t * E + |s| ≤ C * (t * R + (1 + fp.u) * |r|) := by
            nlinarith [hEmul, hsC]
          _ ≤ C * ((1 + fp.u) * (m + |r|)) :=
            mul_le_mul_of_nonneg_left hmid hC0
          _ ≤ C * ((1 + fp.u) * ((1 + fp.u) * z)) := by
            dsimp [m, z] at hadd ⊢
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hadd hf0) hC0
          _ = C * (1 + fp.u) ^ 2 * z := by ring
      have hE' : 0 ≤ t * E + |s| :=
        add_nonneg (mul_nonneg ht hE) (abs_nonneg s)
      have hfac : 1 ≤ (1 + fp.u) ^ 2 := by
        nlinarith [fp.u_nonneg, sq_nonneg fp.u]
      have hC' : 1 ≤ C * (1 + fp.u) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hfac)]
      have htail := ih (t * E + |s|) z (C * (1 + fp.u) ^ 2)
        hE' hz0 hC' hstep
      simpa only [List.foldl, List.length_cons] using
        (show ss.foldl (fun y c => t * y + |c|) (t * E + |s|) ≤
          C * (1 + fp.u) ^ (2 * (ss.length + 1)) *
            rs.foldl (fun y c => fp.fl_add (fp.fl_mul t y) |c|) z from by
              calc
                _ ≤ (C * (1 + fp.u) ^ 2) *
                    (1 + fp.u) ^ (2 * ss.length) *
                    rs.foldl (fun y c => fp.fl_add (fp.fl_mul t y) |c|) z := htail
                _ = C * (1 + fp.u) ^ (2 * (ss.length + 1)) *
                    rs.foldl (fun y c => fp.fl_add (fp.fl_mul t y) |c|) z := by
                      rw [show 2 * (ss.length + 1) = 2 + 2 * ss.length by omega, pow_add]
                      ring)

private theorem p54_abs_as_poly (x : ℝ) (cs : List ℝ) :
    p54AbsDesc x cs = p54PolyDesc |x| (cs.map abs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [p54AbsDesc, p54PolyDesc, ih]

private theorem p54_fold_map_abs (f : ℝ → ℝ → ℝ) :
    ∀ (cs : List ℝ) (y : ℝ),
      (cs.map abs).foldl f y = cs.foldl (fun z c => f z |c|) y := by
  intro cs
  induction cs with
  | nil => intro y; rfl
  | cons c cs ih =>
      intro y
      simpa [List.foldl] using ih (f y |c|)

private theorem p54_abs_fold (x c : ℝ) (cs : List ℝ) :
    p54AbsDesc x (c :: cs) =
      cs.foldl (fun y d => |x| * y + |d|) |c| := by
  calc
    p54AbsDesc x (c :: cs) =
        NumStability.polyDesc |x| ((c :: cs).map abs) := by
          rw [p54_abs_as_poly, p54Poly_eq]
    _ = NumStability.hornerDesc |x| ((c :: cs).map abs) :=
      (NumStability.hornerDesc_eq_polyDesc |x| _).symm
    _ = (cs.map abs).foldl (fun y d => |x| * y + d) |c| := by
      rfl
    _ = cs.foldl (fun y d => |x| * y + |d|) |c| :=
      p54_fold_map_abs _ cs |c|

private theorem p54_horner_abs_fold (fp : P54FPModel) (t c : ℝ)
    (cs : List ℝ) :
    p54Horner fp t ((c :: cs).map abs) =
      cs.foldl (fun y d => fp.fl_add (fp.fl_mul t y) |d|) |c| := by
  change (cs.map abs).foldl (fun y d => fp.fl_add (fp.fl_mul t y) d) |c| = _
  exact p54_fold_map_abs _ cs |c|

private theorem p54_second_bound (fp : P54FPModel) (x : ℝ)
    (n : ℕ) (a b : List ℝ)
    (ha : a.length = n + 1) (hb : b.length = n + 1)
    (hvalid : P54GammaValid fp.u (2 * n + 1)) :
    p54AbsDesc x (p54SumCoeffs a b) ≤
      (1 + fp.u) ^ (2 * n + 1) *
        p54Horner fp |x| ((p54RoundedSumCoeffs fp a b).map abs) := by
  have hu : fp.u < 1 := by
    have hn : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
    have hmul := mul_le_mul_of_nonneg_right hn fp.u_nonneg
    unfold P54GammaValid at hvalid
    nlinarith
  cases a with
  | nil => simp at ha
  | cons aa as =>
      cases b with
      | nil => simp at hb
      | cons bb bs =>
          have has : as.length = n := by simpa using ha
          have hbs : bs.length = n := by simpa using hb
          have htail : as.length = bs.length := by omega
          have hrel := p54_inverse_coeffs fp as bs htail
          have hinit := (p54_coeff_bounds fp aa bb).2.2
          have hfold := p54_fold_inverse fp |x| hu (abs_nonneg x) hrel
            |aa + bb| |fp.fl_add aa bb| (1 + fp.u)
            (abs_nonneg _) (abs_nonneg _) (by linarith [fp.u_nonneg]) hinit
          have hlen : (p54SumCoeffs as bs).length = n := by
            simp [p54SumCoeffs, List.length_zipWith, has, hbs]
          have hE : p54AbsDesc x (p54SumCoeffs (aa :: as) (bb :: bs)) =
              (p54SumCoeffs as bs).foldl
                (fun y c => |x| * y + |c|) |aa + bb| := by
            change p54AbsDesc x ((aa + bb) :: p54SumCoeffs as bs) = _
            exact p54_abs_fold x (aa + bb) _
          have hR : p54Horner fp |x|
              ((p54RoundedSumCoeffs fp (aa :: as) (bb :: bs)).map abs) =
              (p54RoundedSumCoeffs fp as bs).foldl
                (fun y c => fp.fl_add (fp.fl_mul |x| y) |c|) |fp.fl_add aa bb| := by
            change p54Horner fp |x|
              (((fp.fl_add aa bb) :: p54RoundedSumCoeffs fp as bs).map abs) = _
            exact p54_horner_abs_fold fp |x| (fp.fl_add aa bb) _
          rw [hE, hR]
          rw [hlen] at hfold
          calc
            _ ≤ (1 + fp.u) * (1 + fp.u) ^ (2 * n) *
                (p54RoundedSumCoeffs fp as bs).foldl
                  (fun y c => fp.fl_add (fp.fl_mul |x| y) |c|) |fp.fl_add aa bb| := hfold
            _ = (1 + fp.u) ^ (2 * n + 1) *
                (p54RoundedSumCoeffs fp as bs).foldl
                  (fun y c => fp.fl_add (fp.fl_mul |x| y) |c|) |fp.fl_add aa bb| := by
              rw [pow_succ]
              ring

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
  constructor
  · let s := p54SumCoeffs a b
    let r := p54RoundedSumCoeffs fp a b
    have hab : a.length = b.length := by omega
    obtain ⟨hcoeff, habs⟩ := p54_list_forward_bounds fp x a b hab
    have hrlen : r.length = n + 1 := by
      simp [r, p54RoundedSumCoeffs, List.length_zipWith, ha, hb]
    have hvalid2 : P54GammaValid fp.u (2 * n) := by
      unfold P54GammaValid at hvalid ⊢
      have hle : ((2 * n : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * n ≤ 2 * n + 1)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle fp.u_nonneg) hvalid
    have hlib : NumStability.gammaValid (p54AsFPModel fp) (2 * n) := hvalid2
    have hhorner :=
      NumStability.fl_hornerDesc_forward_error_bound
        (p54AsFPModel fp) x r (by simpa [hrlen] using hlib)
    have hh : |p54PolyDesc x r - p54Horner fp x r| ≤
        p54Gamma fp.u (2 * n) * p54AbsDesc x r := by
      simpa [p54Horner_eq, p54Poly_eq, p54Abs_eq, p54Gamma,
        NumStability.gamma, hrlen, abs_sub_comm] using hhorner
    have hgamma0 : 0 ≤ p54Gamma fp.u (2 * n) := by
      simpa [p54Gamma, NumStability.gamma] using
        (NumStability.gamma_nonneg (p54AsFPModel fp) hlib)
    have hA0 : 0 ≤ p54AbsDesc x s := by
      simpa [p54Abs_eq] using NumStability.polyDescAbs_nonneg x s
    have hgam := p54_gamma_step fp.u fp.u_nonneg (2 * n)
      (by simpa [show 2 * n + 1 = (2 * n) + 1 by omega] using hvalid)
    change |p54PolyDesc x s - p54Horner fp x r| ≤
      p54Gamma fp.u (2 * n + 1) * p54AbsDesc x s
    have hident : p54PolyDesc x s - p54Horner fp x r =
        (p54PolyDesc x s - p54PolyDesc x r) +
          (p54PolyDesc x r - p54Horner fp x r) := by ring
    rw [hident]
    calc
      |(p54PolyDesc x s - p54PolyDesc x r) +
          (p54PolyDesc x r - p54Horner fp x r)| ≤
        |p54PolyDesc x s - p54PolyDesc x r| +
          |p54PolyDesc x r - p54Horner fp x r| := abs_add_le _ _
      _ ≤ fp.u * p54AbsDesc x s +
          p54Gamma fp.u (2 * n) * p54AbsDesc x r :=
        add_le_add hcoeff hh
      _ ≤ fp.u * p54AbsDesc x s +
          p54Gamma fp.u (2 * n) * ((1 + fp.u) * p54AbsDesc x s) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left habs hgamma0)
      _ = (fp.u + p54Gamma fp.u (2 * n) * (1 + fp.u)) *
          p54AbsDesc x s := by ring
      _ ≤ p54Gamma fp.u (2 * n + 1) * p54AbsDesc x s :=
        mul_le_mul_of_nonneg_right hgam hA0
  · exact p54_second_bound fp x n a b ha hb hvalid

end VSCLReuse
